"""CLI entry point: five-phase orchestration with rich progress display
and human checkpoints.

Usage::

    python -m orchestrator.main \\
      --algorithm "SVRG" \\
      --update-rule "w_{t+1} = w_t - η·(∇f_i(w_t) - ∇f_i(w^s) + ∇f(w^s))" \\
      --proof-sketch "Variance reduction via control variate, O(1/T) rate" \\
      --archetype B

Or interactive mode::

    python -m orchestrator.main --interactive
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

from rich.console import Console
from rich.panel import Panel
from rich.progress import BarColumn, Progress, SpinnerColumn, TextColumn

from orchestrator.agents import (
    Agent,
    ToolRegistry,
    escalate,
)
from orchestrator.config import (
    DOC_ANCHORS,
    LIB_GLUE_ANCHORS,
    MAX_PHASE3_RETRIES,
    PROJECT_ROOT,
)
from orchestrator.file_io import (
    load_file,
    snapshot_file,
)
from orchestrator.tools import _path_to_lean_module
from orchestrator.metrics import (
    MetricsStore,
    capture_physical_metrics,
    count_glue_tricks_sections,
)
from orchestrator.prompts import (
    build_algorithm_card,
    load_meta_prompt_a,
    load_meta_prompt_b,
)
from orchestrator.audit_logger import AuditLogger
from orchestrator.verify import (
    check_glue_tricks_gate,
    check_leverage_gate,
    check_used_in_tags,
    lake_build,
)

console = Console()

_CATALOG_LEMMA_HEADING_RE = re.compile(r"^####\s+`([^`]+)`", re.MULTILINE)
_LIB_DECL_RE = re.compile(
    r"^(?:theorem|lemma|noncomputable\s+def|def)\s+([A-Za-z_]\w*)",
    re.MULTILINE,
)

# ---------------------------------------------------------------------------
# Error classification — Signature Hallucination vs ordinary Proof Error
# ---------------------------------------------------------------------------

_SIGNATURE_HALLUCINATION_RE = re.compile(
    r"unknown identifier|unknown constant|unknown tactic|"
    r"failed to synthesize instance|has already been declared",
    re.IGNORECASE,
)

# Lean standard error format: `SomeFile.lean:LINE:COL: error:`
_LEAN_ERROR_LINE_RE = re.compile(
    r"[\w./\\-]+\.lean:(\d+):\d+:\s*error:",
    re.IGNORECASE,
)

# Errors whose line number exceeds this threshold are considered proof-body
# problems, not signature problems — file deletion is prohibited.
_PROOF_BODY_LINE_THRESHOLD = 50

# Agent3 can receive tool results and self-fix up to this many times per attempt
# before escalating to Agent2 for new guidance.
MAX_AGENT3_FEEDBACK_TURNS = 3


def _extract_first_error_line(verify_text: str) -> int | None:
    """Return the line number of the first Lean compiler error, or None."""
    m = _LEAN_ERROR_LINE_RE.search(verify_text)
    return int(m.group(1)) if m else None


def _format_agent3_tool_feedback(
    exec_results: list,
    verify_result: dict,
    target_file: str,
    current_code: str,
) -> str:
    """Format tool execution results for Agent3 to analyze and fix."""
    exit_code = int(verify_result.get("exit_code", 1))
    sorry_count = int(verify_result.get("sorry_count", 0))
    errors = verify_result.get("errors", [])
    err_text = "\n".join(errors) if isinstance(errors, list) else str(errors)
    warnings = verify_result.get("warnings", [])
    warn_text = "\n".join(warnings) if isinstance(warnings, list) else str(warnings)
    parts = [
        "## Tool execution results",
        "",
        f"run_lean_verify({target_file}) returned:",
        f"- exit_code: {exit_code}",
        f"- sorry_count: {sorry_count}",
        "",
        "### Build errors (compiler errors with file:line:col)",
        "```",
        err_text[:6000] if err_text else "(no errors)",
        "```",
    ]
    if warn_text:
        parts.extend([
            "",
            "### Warnings (for context only — do not fix unless directly related)",
            "```",
            warn_text[:1500],
            "```",
        ])
    parts.extend([
        "",
        "Analyze the errors above. Each error line shows file:line:col and the issue "
        "(e.g. unknown identifier, wrong API, type mismatch). "
        "Fix using edit_file_patch, then call run_lean_verify. "
        "Output tool_calls with your fix.",
    ])
    failed_tools = [r for r in exec_results if r.status_code not in ("SUCCESS",)]
    if failed_tools:
        parts.extend([
            "",
            "### Other tool results",
            *[f"- {r.message}" for r in failed_tools],
        ])
    parts.extend([
        "",
        f"### Current file ({target_file})",
        "```lean",
        current_code[:10000] if current_code else "(empty)",
        "```",
    ])
    return "\n".join(parts)


def _classify_lean_error(verify_text: str) -> str:
    """Three-way classification of Lean build errors.

    SIGNATURE_HALLUCINATION  — unknown symbol detected within the first
        _PROOF_BODY_LINE_THRESHOLD lines → theorem *statement* is broken →
        full file rewrite is allowed.

    LOCAL_PROOF_ERROR  — unknown symbol detected but error line is beyond the
        threshold (deep in the proof body) → patching is the right response →
        file deletion is PROHIBITED.

    PROOF_ERROR  — all other errors (type mismatch, unsolved goals, etc.) →
        normal Surgeon-Mode patch.
    """
    has_hallucination_pattern = bool(_SIGNATURE_HALLUCINATION_RE.search(verify_text))
    if not has_hallucination_pattern:
        return "PROOF_ERROR"

    line_no = _extract_first_error_line(verify_text)
    if line_no is not None and line_no <= _PROOF_BODY_LINE_THRESHOLD:
        return "SIGNATURE_HALLUCINATION"

    # Pattern matched but error is deep in the proof body (or no line number
    # could be extracted — assume deep rather than nuke the file).
    return "LOCAL_PROOF_ERROR"


def _extract_symbol_manifest(plan: str) -> list[dict]:
    """Parse symbol_manifest from the JSON block embedded in Agent2's plan.

    Returns an empty list when the block is absent or unparseable.
    """
    match = re.search(r"```json\s*(\{.*?\})\s*```", plan, re.DOTALL)
    if not match:
        return []
    try:
        data = json.loads(match.group(1))
        return data.get("symbol_manifest", [])
    except json.JSONDecodeError:
        return []


@dataclass
class ExecutionResult:
    """Result envelope for each Agent3 tool execution."""

    status_code: str  # SUCCESS / ERROR / BLOCKED
    message: str
    attempt: int = 0


_SUBGRADIENT_CONTEXT = """

## Note: subdifferential symbols (Mathlib 4.28+)

`Mathlib.Analysis.Convex.Subdifferential` has been REMOVED in Mathlib 4.28.
Do NOT add `import Mathlib.Analysis.Convex.Subdifferential` — this module no longer exists.
Instead, define these symbols locally in your algorithm file, placed AFTER `end <SetupNamespace>`:

  def subdifferential (_ : Type*) (f : E → ℝ) (w : E) : Set E :=
    {g : E | ∀ y : E, f y ≥ f w + ⟪g, y - w⟫_ℝ}

  theorem mem_subdifferential_iff {f : E → ℝ} {w g : E} :
      g ∈ subdifferential ℝ f w ↔ ∀ y : E, f y ≥ f w + ⟪g, y - w⟫_ℝ := Iff.rfl

Mark these as LOCAL in symbol_manifest, NOT as VERIFIED from Mathlib.
"""

_SYMBOL_WHITELIST: frozenset[str] = frozenset()


class Gate4Error(RuntimeError):
    """Raised by phase4_persist when Used-in docstring tags are absent.

    Carries ``missing`` as a structured list so the catch site never needs
    to parse a string representation.
    """

    def __init__(self, missing: list[str]) -> None:
        self.missing = missing
        super().__init__(f"[Gate 4] Missing Used-in tags: {missing}")


def _collect_lib_declaration_names() -> set[str]:
    """Collect theorem/lemma/def names under Lib/ for alignment checks."""
    lib_root = PROJECT_ROOT / "Lib"
    names: set[str] = set()
    if not lib_root.exists():
        return names
    for lean_file in lib_root.rglob("*.lean"):
        try:
            content = lean_file.read_text(encoding="utf-8")
        except OSError:
            continue
        names.update(_LIB_DECL_RE.findall(content))
    return names


def _extract_catalog_lemma_names(content: str) -> list[str]:
    """Extract catalog lemma headings from a markdown patch fragment."""
    return _CATALOG_LEMMA_HEADING_RE.findall(content)


# ---------------------------------------------------------------------------
# Git baseline helpers
# ---------------------------------------------------------------------------

def _file_hash(path: str | Path) -> str | None:
    """Return MD5 hex-digest of *path*, or None if the file does not exist."""
    p = Path(path)
    if not p.is_absolute():
        p = PROJECT_ROOT / p
    return hashlib.md5(p.read_bytes()).hexdigest() if p.exists() else None


def _git_diff_files() -> set[str]:
    """Return tracked files with unstaged/staged modifications."""
    result = subprocess.run(
        ["git", "diff", "--name-only"],
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
    )
    return set(result.stdout.splitlines())


def _git_untracked_files() -> set[str]:
    """Return untracked files in the repository."""
    result = subprocess.run(
        ["git", "ls-files", "--others", "--exclude-standard"],
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
    )
    return set(result.stdout.splitlines())


def _capture_lean_baseline() -> tuple[set[str], set[str]]:
    """Capture pre-run Lean file baseline without mutating git state."""
    tracked = {f for f in _git_diff_files() if f.endswith(".lean")}
    untracked = {f for f in _git_untracked_files() if f.endswith(".lean")}
    return tracked, untracked


def _get_modified_lean_files(
    baseline_tracked: set[str],
    baseline_untracked: set[str],
) -> list[str]:
    """Return Lean files changed since run start, excluding pre-existing dirt."""
    tracked_now = {f for f in _git_diff_files() if f.endswith(".lean")}
    untracked_now = {f for f in _git_untracked_files() if f.endswith(".lean")}

    newly_tracked = tracked_now - baseline_tracked
    newly_untracked = untracked_now - baseline_untracked
    baseline_untracked_promoted = tracked_now & baseline_untracked

    return sorted(newly_tracked | newly_untracked | baseline_untracked_promoted)


def _ensure_algorithm_in_lakefile(algorithm: str) -> bool:
    """Ensure Algorithms.<algorithm> is listed in lakefile.lean's SGDAlgorithms roots.

    If the module is already present this is a no-op and returns False.  If it
    is absent it is appended to the end of the roots list so ``lake build
    SGDAlgorithms`` includes the newly-created file and returns True.
    """
    lakefile = PROJECT_ROOT / "lakefile.lean"
    if not lakefile.exists():
        console.print(f"[yellow][lakefile] lakefile.lean not found — skipping auto-update")
        return False

    module_name = f"`Algorithms.{algorithm}"
    content = lakefile.read_text(encoding="utf-8")

    if module_name in content:
        return False  # already registered — no-op

    # Find the closing bracket of the SGDAlgorithms roots list and insert before it.
    # Pattern matches the last backtick-module entry in the roots := #[...] block.
    roots_re = re.compile(
        r"(lean_lib SGDAlgorithms.*?roots\s*:=\s*#\[)(.*?)(\])",
        re.DOTALL,
    )
    m = roots_re.search(content)
    if not m:
        console.print(
            "[yellow][lakefile] Could not find SGDAlgorithms roots list — "
            "please add the module manually."
        )
        return False

    updated = content[: m.start(3)] + f", {module_name}" + content[m.start(3) :]
    lakefile.write_text(updated, encoding="utf-8")
    console.print(f"[green][lakefile] Added {module_name} to SGDAlgorithms roots.")
    return True


def _remove_algorithm_from_lakefile(algorithm: str) -> None:
    """Remove Algorithms.<algorithm> from lakefile.lean SGDAlgorithms roots (rollback).

    Called when a pipeline run fails or is interrupted to undo the temporary
    registration added at the start of Phase 3.
    """
    lakefile = PROJECT_ROOT / "lakefile.lean"
    if not lakefile.exists():
        return

    module_name = f"`Algorithms.{algorithm}"
    content = lakefile.read_text(encoding="utf-8")
    if module_name not in content:
        return

    # Try removing ", `Algorithms.X" (module was appended after existing entries).
    updated = re.sub(r",\s*" + re.escape(module_name), "", content)
    if updated == content:
        # Fallback: module appears first — remove "`Algorithms.X, " or "`Algorithms.X".
        updated = re.sub(re.escape(module_name) + r",?\s*", "", content)

    lakefile.write_text(updated, encoding="utf-8")
    console.print(f"[yellow][lakefile] Removed {module_name} from SGDAlgorithms roots (rollback).")


def _parse_persister_json(raw: str) -> list:
    """Robustly parse Agent4 JSON output. Strips markdown blocks, tolerates trailing text.
    Coerces a bare JSON object into a single-element list for forward compatibility."""
    text = raw.strip()
    # Step 1: Strip markdown code block if present.
    # Use flexible regex: \s* allows no newline between ``` and JSON; (.*?)\s* allows
    # content with or without trailing newline before closing ```.
    match = re.search(r'```(?:json)?\s*(.*?)\s*```', text, re.DOTALL)
    if match:
        text = match.group(1).strip()
    # Step 2: Parse first complete JSON value only (ignore trailing commentary)
    decoder = json.JSONDecoder()
    obj, _ = decoder.raw_decode(text)
    # Step 3: Coerce bare object to list (Agent4 sometimes returns a single op as an object)
    if isinstance(obj, dict):
        obj = [obj]
    return obj


# ---------------------------------------------------------------------------
# Agent2 guided lookup helper
# ---------------------------------------------------------------------------

def _call_agent2_with_tools(
    agent2: "Agent",
    registry: "ToolRegistry",
    user_msg: str,
    max_tool_rounds: int = 5,
) -> str:
    """Call Agent2 with optional read-only tool support.

    Agent2 may reply with a lookup request:
        {"type": "lookup", "tool_calls": [{"tool": "read_file", "arguments": {...}}, ...]}
    In that case the tools are executed against *registry* (read-only) and
    results are fed back to Agent2.  Any other reply format (plain text, or
    JSON without ``"type": "lookup"``) is returned immediately as final guidance.
    After *max_tool_rounds* the last reply is returned regardless.
    """
    reply = agent2.call(user_msg)

    for _ in range(max_tool_rounds):
        # Try to parse as JSON lookup request.
        try:
            payload = json.loads(reply)
        except (json.JSONDecodeError, ValueError):
            return reply  # plain text → final guidance

        if not isinstance(payload, dict) or payload.get("type") != "lookup":
            return reply  # non-lookup JSON → final guidance

        tool_calls = payload.get("tool_calls", [])
        if not isinstance(tool_calls, list) or not tool_calls:
            return reply

        results: list[dict] = []
        for tc in tool_calls:
            if not isinstance(tc, dict):
                continue
            tool_name = tc.get("tool", "")
            args = tc.get("arguments", {}) if isinstance(tc.get("arguments"), dict) else {}
            try:
                result = registry.call(tool_name, **args)
            except Exception as exc:  # noqa: BLE001
                result = {"error": str(exc)}
            results.append({"tool": tool_name, "arguments": args, "result": result})

        reply = agent2.call(
            "Lookup results:\n"
            + json.dumps(results, indent=2, ensure_ascii=False)
            + "\n\nContinue planning or issue more lookups if still needed."
        )

    return reply  # max rounds exhausted → return last reply as-is


# ---------------------------------------------------------------------------
# Phase implementations
# ---------------------------------------------------------------------------

def phase1_generate_prompt(
    algorithm: str,
    update_rule: str,
    proof_sketch: str,
    archetype: str,
) -> str:
    """Phase 1: Agent1 generates the Prover prompt via Meta-Prompt A."""
    console.rule("[bold cyan]Phase 1/5 — Generate Prover Prompt")

    agent1 = Agent("orchestrator")
    meta_a = load_meta_prompt_a()
    card = build_algorithm_card(algorithm, update_rule, proof_sketch, archetype)

    phase1_prompt = (
        f"Generate a complete Prover prompt by instantiating the Meta-Prompt A "
        f"template below with the algorithm card.\n\n"
        f"## Meta-Prompt A Template\n{meta_a}\n\n"
        f"## Algorithm Card\n{card}"
    )
    prompt_text = agent1.call(phase1_prompt)
    AuditLogger.get().log_phase1_detail(phase1_prompt, prompt_text)
    console.print(
        f"[green]\\[Agent1] Prover prompt generated "
        f"({len(prompt_text)} chars)."
    )
    return prompt_text


def phase2_plan_and_approve(
    prover_prompt: str,
    force_low_leverage: bool = False,
) -> tuple[str, Agent, Agent]:
    """Phase 2: Agent1 ↔ Agent2 approval loop + leverage gate.

    Returns (approved_plan, agent1, agent2) so they can be reused.
    """
    console.rule("[bold cyan]Phase 2/5 — Plan & Approve")

    agent1 = Agent("orchestrator")
    agent2 = Agent("planner")

    if "subgradient" in prover_prompt.lower() or "subdifferential" in prover_prompt.lower():
        prover_prompt = prover_prompt + _SUBGRADIENT_CONTEXT

    plan = agent2.call(prover_prompt)
    console.print(Panel(
        plan[:500] + "..." if len(plan) > 500 else plan,
        title="[cyan]Agent2 — Initial Plan",
    ))

    round_num = 0
    while True:
        # Python-level symbol_manifest gate (zero token cost).
        # Catch BLOCKED symbols before spending tokens on Agent1 review.
        # Whitelisted symbols (subdifferential, mem_subdifferential_iff) bypass the gate.
        _manifest = _extract_symbol_manifest(plan)
        _blocked = [
            e for e in _manifest
            if str(e.get("status", "")).startswith("BLOCKED")
            and e.get("symbol", "") not in _SYMBOL_WHITELIST
        ]
        if _blocked:
            _blocked_names = ", ".join(e.get("symbol", "?") for e in _blocked)
            console.print(
                f"[red][Python Gate] symbol_manifest BLOCKED: {_blocked_names}. "
                "Forcing Agent2 revision (no Agent1 token spend)."
            )
            plan = agent2.call(
                f"Your plan's symbol_manifest contains BLOCKED entries: {_blocked_names}.\n"
                "Apply Principle A (Primitive First): replace each BLOCKED symbol with "
                "a direct math primitive (inequality, ∀/∃ quantifier, inner product) "
                "before resubmitting.\n"
                "Do NOT invent a new abstract name as a replacement — use raw math."
            )
            console.print(Panel(
                plan[:500] + "..." if len(plan) > 500 else plan,
                title="[cyan]Agent2 — Revised Plan (Python Gate: BLOCKED symbols)",
            ))
            continue  # re-check symbol_manifest before Agent1 review

        round_num += 1
        review_prompt = (
            "Review the plan from Agent2. Return ONLY valid JSON:\n"
            '{"decision": "APPROVED" | "AMEND" | "REJECTED", "feedback": "..."}\n\n'
            "Decision rules:\n"
            "- AMEND: Use for fixable issues (missing docs section, Used-in tags, format). Provide specific feedback.\n"
            "- REJECTED: Use ONLY for unfixable math errors or safety violations. Do NOT use for docs/tags.\n"
            "- APPROVED: Plan meets all criteria.\n\n"
            f"Plan to review:\n{plan}"
        )
        review_raw = agent1.call(review_prompt)

        try:
            review = json.loads(review_raw)
        except json.JSONDecodeError as exc:
            raise RuntimeError(
                "[Phase 2] Reviewer returned invalid JSON. "
                f"line={exc.lineno}, col={exc.colno}, msg={exc.msg}"
            ) from exc

        if not isinstance(review, dict):
            raise RuntimeError("[Phase 2] Reviewer response must be a JSON object.")

        decision = str(review.get("decision", "")).strip().upper()
        feedback = review.get("feedback", "")
        feedback_text = feedback if isinstance(feedback, str) else str(feedback)

        AuditLogger.get().log_phase2_round(
            round_num, plan, review_prompt, review_raw, decision, feedback_text
        )

        if decision == "APPROVED":
            console.print(
                f"[green]\\[Agent1 ↔ Agent2] Plan APPROVED after {round_num} round(s)."
            )
            break

        if decision == "AMEND":
            if not isinstance(feedback, str) or not feedback.strip():
                raise RuntimeError(
                    "[Phase 2] decision=AMEND requires a non-empty feedback field."
                )
            console.print(Panel(
                feedback_text[:400] + "..." if len(feedback_text) > 400 else feedback_text,
                title=f"[yellow]Agent1 — AMEND Feedback (round {round_num})",
            ))
            # Automatic rollback to planner stage.
            plan = agent2.call(
                "Revise your plan based on reviewer feedback below.\n\n"
                f"{feedback_text}"
            )
            console.print(Panel(
                plan[:500] + "..." if len(plan) > 500 else plan,
                title=f"[cyan]Agent2 — Revised Plan (round {round_num})",
            ))
            continue

        if decision == "REJECTED":
            raise RuntimeError(
                "[Phase 2] Plan REJECTED by reviewer. "
                f"Feedback: {feedback_text or '(none)'}"
            )

        raise RuntimeError(
            "[Phase 2] Invalid decision from reviewer. "
            f"Expected APPROVED/REJECTED/AMEND, got: {decision!r}"
        )

    passed, leverage = check_leverage_gate(plan)
    console.print(
        f"[{'green' if passed else 'red'}]"
        f"\\[Gate 1] Leverage = {leverage:.1%} "
        f"({'PASS' if passed else 'BLOCKED'})"
    )
    if not passed and not force_low_leverage:
        console.print(
            "[red bold]Leverage below 50%.  Use --force-low-leverage to override."
        )
        sys.exit(1)

    return plan, agent1, agent2


def phase3_prove(
    agent2: Agent,
    target_file: str,
    plan: str,
    *,
    max_retries: int = MAX_PHASE3_RETRIES,
    archetype: str = "A",
) -> tuple[bool, int, str, dict]:
    """Phase 3: Agent2 ↔ Agent3 proving loop + Agent5 escalation.

    Returns (success, attempts, errors_or_empty, audit).
    """
    console.rule("[bold cyan]Phase 3/5 — Prove (fill sorry)")

    agent3 = Agent("sorry_closer", extra_files=[target_file])
    registry = ToolRegistry()
    registry.register_default_tools()
    # Read-only registry for Agent2 lookup rounds (no write tools exposed).
    readonly_registry = ToolRegistry()
    readonly_registry.register_readonly_tools()
    diag_log: list[str] = []

    # Pre-check: if the target file already has 0 sorry and builds clean,
    # skip the entire Agent3 loop.  This prevents destructive rewrites when
    # a previous run already completed the proof (e.g., after a Gate 4 crash).
    _tgt_precheck = Path(target_file) if Path(target_file).is_absolute() else PROJECT_ROOT / target_file
    if _tgt_precheck.exists():
        pre_result = registry.call("run_lean_verify", target_file)
        if int(pre_result.get("exit_code", 1)) == 0 and int(pre_result.get("sorry_count", 0)) == 0:
            console.print(
                "[green][Phase 3] File already complete (build=OK, sorry=0). "
                "Skipping Agent3 — proceeding directly to Phase 4."
            )
            return True, 0, "", {
                "execution_history": [],
                "attempt_failures": [],
                "estimated_token_consumption": 0,
                "retry_count": 0,
            }

    _archetype_b_warning = (
        "\n\nARCHETYPE B WARNING: This is a novel proof structure with no Layer 1 "
        "meta-theorem to delegate to. No high-level abstractions are allowed in "
        "the theorem statement without verification in Lib/. Every symbol you "
        "reference MUST be traceable to a file in the shared context. "
        "Use read_file to verify lemma names before writing anything."
        if archetype.upper() == "B" else ""
    )
    _tgt = Path(target_file) if Path(target_file).is_absolute() else PROJECT_ROOT / target_file
    initial_exists: bool = _tgt.exists()
    _file_absent_suffix = (
        "\n\nCRITICAL: The target file does NOT exist yet. Your guidance MUST instruct "
        f'Agent3 to call write_new_file(path="{target_file}", content=<full Lean scaffold>) '
        "as the FIRST tool call. Output the complete file content in a code block for "
        "Agent3 to pass to write_new_file. Do NOT suggest edit_file_patch — the file "
        "must be created first."
        if not initial_exists
        else ""
    )
    guidance = _call_agent2_with_tools(
        agent2,
        readonly_registry,
        "The verification target file is "
        + target_file
        + ". Provide initial proving guidance for Agent3.  Specify which sorry "
        "to tackle first and the recommended proof strategy (Mathlib lemma, "
        "glue pattern letter, etc.). "
        "When the plan requires both new glue AND a new algorithm file, your "
        "guidance MUST instruct Agent3 to complete BOTH in a single attempt, "
        "or verification will fail."
        + _archetype_b_warning
        + _file_absent_suffix,
    )
    console.print(Panel(
        guidance[:400] + "..." if len(guidance) > 400 else guidance,
        title="[cyan]Agent2 — Initial Guidance",
    ))

    last_errors = ""
    last_sorry_count = 0
    attempts = 0
    execution_history: list[ExecutionResult] = []
    attempt_failures: list[dict] = []
    token_char_budget = 0

    # Snapshot target-file state before any Agent3 edits.
    # initial_hash: used for Phase-3 global success gate (file must change vs start of Phase 3).
    # attempt_start_hash: snapshotted at the start of each attempt for per-attempt no-op detection.
    initial_hash: str | None = _file_hash(target_file)
    file_changed: bool = False  # updated each attempt

    for attempt in range(1, max_retries + 1):
        attempts = attempt
        attempt_start_hash: str | None = _file_hash(target_file)
        _file_absent_prefix = (
            "CRITICAL: Target file does NOT exist. You MUST call write_new_file(path="
            f'"{target_file}", content=<complete Lean code>) as your FIRST tool call. '
            "The guidance below contains the full file content — pass it to write_new_file. "
            "Only after the file exists do you call run_lean_verify.\n\n"
            if not _tgt.exists()
            else ""
        )
        prover_prompt = (
            _file_absent_prefix
            + "Use tools to close sorry placeholders.\n"
            "Return ONLY valid JSON with keys: thought, tool_calls.\n"
            "Each tool call must be an object: "
            '{"tool": "<name>", "arguments": {...}}.\n'
            "Allowed tools: read_file, search_in_file, edit_file_patch, write_new_file, run_lean_verify.\n"
            "SITUATIONAL BEHAVIOR:\n"
            "- If guidance contains PATCH blocks (<<<SEARCH>>>/<<<REPLACE>>>): "
            "execute them exactly — copy old_str and new_str verbatim.\n"
            "- If you receive build errors in a follow-up: analyze the error "
            "and line number, then fix (wrong identifier, API usage, etc.). "
            "You have autonomy to reason and repair.\n"
            "After edits call run_lean_verify. You will receive tool results "
            "and can output more tool_calls to fix any errors.\n\n"
            f"Target file: {target_file}\n"
            f"Guidance:\n{guidance}"
        )
        raw_reply = agent3.call(prover_prompt)
        token_char_budget += len(prover_prompt) + len(raw_reply)

        try:
            payload = json.loads(raw_reply)
        except json.JSONDecodeError as exc:
            err_msg = (
                "RETRY_ERROR: Invalid JSON format "
                f"(line {exc.lineno}, col {exc.colno}): {exc.msg}"
            )
            last_errors = err_msg
            diag_log.append(f"attempt={attempt} {err_msg}")
            execution_history.append(ExecutionResult(
                status_code="ERROR",
                message=err_msg,
                attempt=attempt,
            ))
            guidance = _call_agent2_with_tools(
                agent2,
                readonly_registry,
                f"Attempt {attempt} failed.\n"
                "Invalid JSON format from Agent3.\n"
                "Adjust your guidance so Agent3 returns strict JSON tool calls.",
            )
            console.print(
                f"  [Agent3] attempt {attempt}/{max_retries} — "
                f"build=FAIL, sorry=unknown"
            )
            continue

        if not isinstance(payload, dict):
            last_errors = "RETRY_ERROR: Agent3 JSON top-level must be an object."
            diag_log.append(f"attempt={attempt} {last_errors}")
            execution_history.append(ExecutionResult(
                status_code="ERROR",
                message=last_errors,
                attempt=attempt,
            ))
            guidance = _call_agent2_with_tools(
                agent2,
                readonly_registry,
                f"Attempt {attempt} failed.\n"
                "Agent3 JSON top-level was not an object.\n"
                "Adjust your guidance for strict output schema.",
            )
            console.print(
                f"  [Agent3] attempt {attempt}/{max_retries} — "
                f"build=FAIL, sorry=unknown"
            )
            continue

        tool_calls = payload.get("tool_calls", [])
        if not isinstance(tool_calls, list):
            last_errors = "RETRY_ERROR: 'tool_calls' must be a JSON list."
            diag_log.append(f"attempt={attempt} {last_errors}")
            execution_history.append(ExecutionResult(
                status_code="ERROR",
                message=last_errors,
                attempt=attempt,
            ))
            guidance = _call_agent2_with_tools(
                agent2,
                readonly_registry,
                f"Attempt {attempt} failed.\n"
                "Agent3 output schema invalid: tool_calls is not a list.\n"
                "Adjust your guidance for strict output schema.",
            )
            console.print(
                f"  [Agent3] attempt {attempt}/{max_retries} — "
                f"build=FAIL, sorry=unknown"
            )
            continue

        exec_results: list[ExecutionResult] = []
        edited_this_attempt = False
        blocked_path: str | None = None
        verify_result: dict | None = None
        patch_mismatch_detected: bool = False

        for idx, call in enumerate(tool_calls, start=1):
            if not isinstance(call, dict):
                exec_results.append(ExecutionResult(
                    status_code="ERROR",
                    message=f"tool_calls[{idx}] must be an object.",
                    attempt=attempt,
                ))
                continue

            tool_name = call.get("tool")
            arguments = call.get("arguments", {})
            if not isinstance(tool_name, str) or not isinstance(arguments, dict):
                exec_results.append(ExecutionResult(
                    status_code="ERROR",
                    message=f"tool_calls[{idx}] invalid tool/arguments.",
                    attempt=attempt,
                ))
                continue

            try:
                outcome = registry.call(tool_name, **arguments)
                exec_results.append(ExecutionResult(
                    status_code="SUCCESS",
                    message=f"{tool_name} executed.",
                    attempt=attempt,
                ))
                if tool_name in ("edit_file_patch", "write_new_file"):
                    edited_this_attempt = True
                if tool_name == "run_lean_verify":
                    verify_result = outcome
            except PermissionError as exc:
                blocked_path = str(arguments.get("path") or arguments.get("file_path") or "?")
                exec_results.append(ExecutionResult(
                    status_code="BLOCKED",
                    message=f"Security violation on path {blocked_path}: {exc}",
                    attempt=attempt,
                ))
            except ValueError as exc:
                err_str = str(exc)
                # Detect edit_file_patch SEARCH mismatch specifically so we
                # can ask Agent2 to re-generate from the raw file text.
                if tool_name == "edit_file_patch" and (
                    "not found in target file" in err_str
                    or "old_str not found" in err_str
                ):
                    patch_mismatch_detected = True
                    exec_results.append(ExecutionResult(
                        status_code="PATCH_MISMATCH",
                        message=f"edit_file_patch SEARCH not found in file: {err_str}",
                        attempt=attempt,
                    ))
                else:
                    exec_results.append(ExecutionResult(
                        status_code="ERROR",
                        message=f"{tool_name} failed: {err_str}",
                        attempt=attempt,
                    ))
            except Exception as exc:  # noqa: BLE001
                exec_results.append(ExecutionResult(
                    status_code="ERROR",
                    message=f"{tool_name} failed: {exc}",
                    attempt=attempt,
                ))

        # Strong verification loop: any edit must trigger verify.
        if edited_this_attempt and verify_result is None:
            verify_result = registry.call("run_lean_verify", target_file)
            exec_results.append(ExecutionResult(
                status_code="SUCCESS",
                message="Auto-triggered run_lean_verify after edit_file_patch.",
                attempt=attempt,
            ))

        if verify_result is None:
            verify_result = registry.call("run_lean_verify", target_file)

        exit_code = int(verify_result.get("exit_code", 1))
        last_sorry_count = int(verify_result.get("sorry_count", 0))
        verify_errors = verify_result.get("errors", [])
        verify_text = "\n".join(verify_errors) if isinstance(verify_errors, list) else str(verify_errors)
        last_errors = verify_text

        # 4-condition success gate:
        #   1. exit_code == 0   (compiler clean)
        #   2. sorry_count == 0 (no sorry placeholders)
        #   3. target file exists
        #   4. target file content changed since Phase 3 started
        current_hash = _file_hash(target_file)
        file_changed = _tgt.exists() and (not initial_exists or current_hash != initial_hash)
        # Per-attempt change detection: did Agent3 touch the file THIS attempt?
        attempt_file_changed = _tgt.exists() and (current_hash != attempt_start_hash)

        if exit_code == 0 and last_sorry_count == 0 and file_changed:
            # Full-library gate: verify no cascade breakage across SGDAlgorithms.
            full_build = lake_build(target="SGDAlgorithms")
            if full_build.returncode != 0:
                full_errors = full_build.errors or "SGDAlgorithms full build failed"
                last_errors = full_errors
                exec_results.append(ExecutionResult(
                    status_code="ERROR",
                    message=f"[Full-Build Gate] SGDAlgorithms failed:\n{full_errors[:800]}",
                    attempt=attempt,
                ))
                prove_state = "PROVE_RETRY"
            else:
                prove_state = "PROVE_SUCCESS"
        elif exit_code == 0 and last_sorry_count == 0 and not attempt_file_changed:
            # Build looks green but Agent3 never touched the file this attempt — no-op trap.
            no_change_msg = (
                "FAILURE: No changes detected in the target file. "
                "You must use 'edit_file_patch' to implement the proof "
                "before calling verification."
            )
            exec_results.append(ExecutionResult(
                status_code="ERROR",
                message=no_change_msg,
                attempt=attempt,
            ))
            last_errors = no_change_msg
            prove_state = "PROVE_RETRY"
        else:
            prove_state = "PROVE_RETRY"

        blocked_msgs = [r.message for r in exec_results if r.status_code == "BLOCKED"]
        error_msgs = [r.message for r in exec_results if r.status_code == "ERROR"]
        execution_history.extend(exec_results)

        if exit_code != 0 and verify_result is not None:
            attempt_failures.append({
                "attempt": attempt,
                "exit_code": exit_code,
                "sorry_count": last_sorry_count,
                "lean_errors": verify_text[:4000] if verify_text else "",
                "target_file_content": (
                    load_file(target_file)[:50000] if _tgt.exists() else None
                ),
            })

        build_ok = prove_state == "PROVE_SUCCESS"
        status = "OK" if build_ok else "FAIL"
        console.print(
            f"  [Agent3] attempt {attempt}/{max_retries} — "
            f"build={status}, sorry={last_sorry_count}"
        )
        if exit_code != 0 and verify_text:
            console.print(f"[dim]Lean errors:\n{verify_text[:1500]}[/dim]")

        if prove_state == "PROVE_SUCCESS":
            return True, attempts, "", {
                "execution_history": [r.__dict__ for r in execution_history],
                "attempt_failures": attempt_failures,
                "estimated_token_consumption": max(1, token_char_budget // 4),
                "retry_count": sum(
                    1
                    for r in execution_history
                    if r.status_code in {"ERROR", "BLOCKED"}
                ),
            }

        # Intelligent retry prompts.
        # Priority 1: no-op trap — Agent3 never touched the file THIS attempt.
        if prove_state == "PROVE_RETRY" and not attempt_file_changed and exit_code == 0:
            guidance = _call_agent2_with_tools(
                agent2,
                readonly_registry,
                f"Attempt {attempt} NOOP — Agent3 made no file changes.\n"
                f"Target file: {target_file}\n"
                "SURGEON MODE: Agent3 called run_lean_verify without editing the file first. "
                "Output a PATCH block (<<<SEARCH>>>/<<<REPLACE>>>) with the exact Lean code "
                "Agent3 must write, or a write_new_file instruction if the file does not exist. "
                "Be specific — no natural language advice. Agent3 will execute your patch verbatim.",
            )
            console.print(
                f"  [Agent3] attempt {attempt}/{max_retries} — "
                "build=NOOP (file unchanged)"
            )
            continue

        # Priority 2: security violation.
        if blocked_msgs:
            blocked_hint = (
                f"Security violation: You cannot edit path {blocked_path or '?'}."
                " Stay within Algorithms/ or Lib/."
            )
            diag_log.extend([f"attempt={attempt} {m}" for m in blocked_msgs])
            guidance = _call_agent2_with_tools(
                agent2,
                readonly_registry,
                f"Attempt {attempt} failed.\n"
                f"{blocked_hint}\n"
                "Adjust your guidance for safe path usage.",
            )
            continue

        if error_msgs:
            diag_log.extend([f"attempt={attempt} {m}" for m in error_msgs])

        # Priority 2.5: File still does not exist — Agent3 never called write_new_file.
        if not _tgt.exists() and "Target file does not exist" in (verify_text or ""):
            guidance = _call_agent2_with_tools(
                agent2,
                readonly_registry,
                f"Attempt {attempt} failed: Target file still does not exist.\n"
                f"Agent3 did NOT call write_new_file. You MUST output the FULL Lean file content "
                f'and explicitly instruct Agent3 to call write_new_file(path="{target_file}", '
                "content=<complete file>) as the FIRST tool call.\n"
                f"Guidance format: Provide a code block with the complete {target_file} "
                "scaffold (imports, setup, theorem stubs with sorry). Agent3 will pass it to write_new_file.",
            )
            console.print(
                f"  [Agent3] attempt {attempt}/{max_retries} — "
                "build=FAIL (file not created)"
            )
            continue

        current_code = (
            load_file(target_file)
            if _tgt.exists()
            else "(Agent3 has not created the file yet.)"
        )

        # Priority 3: Signature Hallucination — the theorem statement is broken.
        # Patching the proof body cannot fix this; the file must be rewritten.
        error_type = _classify_lean_error(verify_text)
        err_line_no = _extract_first_error_line(verify_text)
        line_no_display = str(err_line_no) if err_line_no is not None else "unknown"

        if error_type == "SIGNATURE_HALLUCINATION":
            console.print(
                f"  [Agent3] attempt {attempt}/{max_retries} — "
                "[red]SIGNATURE_HALLUCINATION detected — deleting broken file"
            )
            if _tgt.exists():
                _tgt.unlink()
            # Reset the snapshot so the next write_new_file counts as a change.
            initial_exists = False
            initial_hash = None
            file_changed = False
            guidance = _call_agent2_with_tools(
                agent2,
                readonly_registry,
                f"[STATEMENT ERROR — SIGNATURE HALLUCINATION]\n"
                f"Lean error excerpt:\n```\n{verify_text[:800]}\n```\n\n"
                f"The theorem STATEMENT itself is broken: it references a symbol "
                f"that does not exist in Lean or Lib/.\n"
                f"The old file has been DELETED. You MUST now rewrite it from scratch.\n\n"
                f"CONSTRAINT (non-negotiable — Principle A):\n"
                f"Use ONLY mathematical primitives in the new theorem signature.\n"
                f"Do NOT invent any new abstract type, set constructor, or class name —\n"
                f"including any name resembling the one that just failed.\n"
                f"Express every property as a direct inequality, ∀/∃ quantifier,\n"
                f"or inner-product expression (e.g. ∀ y, f y ≥ f x + ⟪g, y-x⟫_ℝ).\n\n"
                f"Output a complete corrected file. Agent3 will use write_new_file.",
            )
            continue

        # Priority 3b / Priority 4: Proof body error (LOCAL_PROOF_ERROR or PROOF_ERROR).
        # For both cases: give Agent3 a chance to self-fix using feedback before
        # escalating.  For LOCAL_PROOF_ERROR, fallback to sorry-degrade if
        # Agent3 cannot fix within MAX_AGENT3_FEEDBACK_TURNS.
        # File deletion is ABSOLUTELY PROHIBITED for both cases.
        if error_type == "LOCAL_PROOF_ERROR":
            console.print(
                f"  [Agent3] attempt {attempt}/{max_retries} — "
                f"[yellow]LOCAL_PROOF_ERROR at line {line_no_display} — "
                "giving Agent3 self-fix opportunity first"
            )

        feedback_turn = 0
        feedback_exec_results = exec_results
        feedback_verify_result = verify_result
        feedback_current_code = current_code
        agent3_self_fixed = False

        while feedback_turn < MAX_AGENT3_FEEDBACK_TURNS:
            feedback_msg = _format_agent3_tool_feedback(
                feedback_exec_results,
                feedback_verify_result,
                target_file,
                feedback_current_code,
            )
            raw_reply = agent3.call(feedback_msg)
            token_char_budget += len(feedback_msg) + len(raw_reply)
            console.print(
                f"  [Agent3] feedback turn {feedback_turn + 1}/{MAX_AGENT3_FEEDBACK_TURNS} — "
                "analyzing errors, attempting fix"
            )
            try:
                payload = json.loads(raw_reply)
            except json.JSONDecodeError:
                break
            if not isinstance(payload, dict):
                break
            tool_calls = payload.get("tool_calls", [])
            if not isinstance(tool_calls, list) or not tool_calls:
                break

            # Execute Agent3's fix
            feedback_exec_results = []
            for idx, call in enumerate(tool_calls, start=1):
                if not isinstance(call, dict):
                    feedback_exec_results.append(ExecutionResult(
                        status_code="ERROR",
                        message=f"tool_calls[{idx}] must be an object.",
                        attempt=attempt,
                    ))
                    continue
                tool_name = call.get("tool")
                arguments = call.get("arguments", {})
                if not isinstance(tool_name, str) or not isinstance(arguments, dict):
                    feedback_exec_results.append(ExecutionResult(
                        status_code="ERROR",
                        message=f"tool_calls[{idx}] invalid tool/arguments.",
                        attempt=attempt,
                    ))
                    continue
                try:
                    registry.call(tool_name, **arguments)
                    feedback_exec_results.append(ExecutionResult(
                        status_code="SUCCESS",
                        message=f"{tool_name} executed.",
                        attempt=attempt,
                    ))
                except (PermissionError, ValueError, Exception) as exc:
                    feedback_exec_results.append(ExecutionResult(
                        status_code="ERROR",
                        message=f"{tool_name} failed: {exc}",
                        attempt=attempt,
                    ))

            feedback_verify_result = registry.call("run_lean_verify", target_file)
            feedback_exit = int(feedback_verify_result.get("exit_code", 1))
            feedback_sorry = int(feedback_verify_result.get("sorry_count", 0))
            feedback_current_code = (
                load_file(target_file) if _tgt.exists() else ""
            )

            if feedback_exit == 0 and feedback_sorry == 0:
                f_hash = _file_hash(target_file)
                if _tgt.exists() and (not initial_exists or f_hash != initial_hash):
                    full_build = lake_build(target="SGDAlgorithms")
                    if full_build.returncode == 0:
                        agent3_self_fixed = True
                        console.print(
                            f"  [Agent3] self-fix succeeded on feedback turn "
                            f"{feedback_turn + 1}"
                        )
                        return True, attempts, "", {
                            "execution_history": [r.__dict__ for r in execution_history],
                            "attempt_failures": attempt_failures,
                            "estimated_token_consumption": max(1, token_char_budget // 4),
                            "retry_count": sum(
                                1
                                for r in execution_history
                                if r.status_code in {"ERROR", "BLOCKED"}
                            ),
                        }
            feedback_turn += 1

        # Propagate Agent3 feedback loop's final state to outer loop variables
        # so Agent2 receives the most up-to-date error info and file content.
        if feedback_turn > 0:
            exit_code = feedback_exit
            last_sorry_count = feedback_sorry
            verify_text = "\n".join(
                feedback_verify_result.get("errors", [])
                if isinstance(feedback_verify_result.get("errors"), list)
                else [str(feedback_verify_result.get("errors", ""))]
            )
            current_code = feedback_current_code

        # LOCAL_PROOF_ERROR fallback: if Agent3 could not self-fix, sorry-degrade.
        if error_type == "LOCAL_PROOF_ERROR" and not agent3_self_fixed:
            console.print(
                f"  [Agent3] attempt {attempt}/{max_retries} — "
                f"[yellow]LOCAL_PROOF_ERROR self-fix failed — falling back to sorry-degrade"
            )
            err_summary_match = re.search(
                r"error:(.+)", verify_text, re.IGNORECASE | re.DOTALL
            )
            err_summary = (
                err_summary_match.group(1).strip()[:120].replace("\n", " ")
                if err_summary_match
                else verify_text[:120].replace("\n", " ")
            )
            guidance = _call_agent2_with_tools(
                agent2,
                readonly_registry,
                f"[LOCAL PROOF ERROR — SORRY DEGRADATION REQUIRED]\n"
                f"Build exit code: {exit_code} | Sorry count: {last_sorry_count}\n"
                f"Error at line {line_no_display}:\n```\n{verify_text[:4000]}\n```\n\n"
                f"\n=== AGENT3'S CURRENT FILE ({target_file}) ===\n"
                f"```lean\n{current_code[:3000]}\n```\n\n"
                f"The error is DEEP in the proof body (line {line_no_display}). "
                f"Agent3 has already attempted self-repair but could not fix it.\n"
                f"The theorem statement and imports are correct.\n\n"
                f"STRICT RULES — violation causes automatic failure:\n"
                f"1. Do NOT use write_new_file — the file must NOT be deleted or overwritten.\n"
                f"2. Use edit_file_patch with a <<<SEARCH>>>/<<<REPLACE>>> block to replace "
                f"   the broken tactic/term at line {line_no_display} with:\n"
                f"     sorry -- LOCAL_ERROR: {err_summary}\n"
                f"   This keeps the file compilable so the next attempt can close this sorry.\n"
                f"3. SEARCH must be copied verbatim from the current file shown above.\n"
                f"4. Output ONLY the patch block — no prose explanation needed.",
            )
            continue

        # Exhausted Agent3 self-fix turns — get new guidance from Agent2.
        mismatch_prefix = ""
        if patch_mismatch_detected:
            mismatch_prefix = (
                "PATCH MISMATCH: Your previous SEARCH block did not match the file on disk.\n"
                "You MUST copy the SEARCH string VERBATIM from the raw file shown below.\n"
                "Do NOT reconstruct or reformat from memory — any whitespace difference "
                "will cause edit_file_patch to fail again.\n\n"
            )

        guidance = _call_agent2_with_tools(
            agent2,
            readonly_registry,
            mismatch_prefix
            + f"Attempt {attempt} failed.\n"
            f"Build exit code: {exit_code} | Sorry count: {last_sorry_count}\n"
            f"Error first occurs at line {line_no_display}.\n"
            f"=== FULL LEAN ERROR OUTPUT ===\n```\n{verify_text[:4000]}\n```\n"
            f"\n=== AGENT3'S CURRENT FILE ({target_file}) ===\n"
            f"```lean\n{current_code[:3000]}\n```\n\n"
            f"SURGEON MODE: Diagnose the root cause of the Lean error above. "
            f"Focus on line {line_no_display} and its surrounding context. "
            "Then output one PATCH block per error in the <<<SEARCH>>>/<<<REPLACE>>> format. "
            "SEARCH must be copied verbatim from the current file (exact whitespace/indentation). "
            "Write the exact correct Mathlib 4 code in REPLACE — no vague suggestions. "
            "If REPLACE uses a Lib/ lemma, add a comment above the patch: "
            "# Source: Lib/Glue/<File>.lean or Lib/Layer0/<File>.lean — <lemma name>. "
            "Do NOT name a lemma you have not verified in the file context provided. "
            "Agent3 will apply your patches verbatim as edit_file_patch calls.",
        )

    console.print("[red bold]Max retries exhausted — escalating to Agent5.")
    if diag_log:
        console.print(Panel(
            "\n".join(diag_log[-12:]),
            title="[yellow]Phase 3 Retry Log",
        ))
    agent5 = Agent("diagnostician", extra_files=[target_file] if _tgt.exists() else [])
    sorry_context = (
        load_file(target_file)
        if _tgt.exists()
        else f"(File '{target_file}' does not exist — Prover Agent never created it.)"
    )
    action = escalate(agent5, sorry_context, last_errors, guidance)

    if action == "abort":
        console.print("[red]Aborted by user.")
        sys.exit(1)
    elif action == "fix_assumptions":
        console.print(
            "[yellow]Human: fix assumptions in the theorem signature, then "
            "re-run the orchestrator."
        )
        sys.exit(1)
    elif action == "replan":
        console.print("[yellow]Re-planning requested — restarting Phase 2.")
        return False, attempts, last_errors, {
            "execution_history": [r.__dict__ for r in execution_history],
            "attempt_failures": attempt_failures,
            "estimated_token_consumption": max(1, token_char_budget // 4),
            "retry_count": sum(
                1
                for r in execution_history
                if r.status_code in {"ERROR", "BLOCKED"}
            ),
        }

    return False, attempts, last_errors, {
        "execution_history": [r.__dict__ for r in execution_history],
        "attempt_failures": attempt_failures,
        "estimated_token_consumption": max(1, token_char_budget // 4),
        "retry_count": sum(
            1
            for r in execution_history
            if r.status_code in {"ERROR", "BLOCKED"}
        ),
    }


def phase3b_fix_tags(
    target_file: str,
    missing: list[str],
    max_retries: int = 3,
) -> None:
    """Patch missing Used-in docstring tags without disturbing proof logic.

    Agent3 is explicitly told that the proof is already correct; it must only
    add or extend /-- ... -/ docstrings.  After each round, Gate 4 is
    re-checked; if tags are still absent the loop retries up to *max_retries*
    times before raising Gate4Error.
    """
    registry = ToolRegistry()
    registry.register_default_tools()
    agent3 = Agent("sorry_closer")

    missing_str = "\n".join(f"  - {m}" for m in missing)
    guidance = (
        "DOCSTRING-ONLY TASK — DO NOT MODIFY ANY PROOF LOGIC OR TACTIC LINES.\n"
        "Your proof already compiled (build=OK, sorry=0) and is 100% correct.\n"
        "The ONLY problem is that the following declarations are missing a "
        "'Used in:' line in their /-- ... -/ docstring:\n"
        f"{missing_str}\n\n"
        "For each declaration, use 'edit_file_patch' to find its existing "
        "docstring opening '/--' and replace it with a version that includes "
        "a line such as:\n"
        "  Used in: `<main_theorem>` (<file>, <step>)\n"
        "If the declaration has no docstring yet, add one immediately before "
        "the keyword (def/lemma/theorem).\n"
        "Do NOT touch any :=, tactic, or import lines.\n"
        "After all edits call 'run_lean_verify' once to confirm the file "
        "still compiles.\n"
        f"Target file: {target_file}"
    )

    for attempt in range(1, max_retries + 1):
        console.print(
            f"  [Gate 4b] tag-fixup attempt {attempt}/{max_retries} …"
        )
        raw_reply = agent3.call(
            "Use tools to add missing 'Used in:' docstring tags.\n"
            "Return ONLY valid JSON with keys: thought, tool_calls.\n"
            'Each tool call: {"tool": "<name>", "arguments": {...}}.\n'
            "Allowed tools: read_file, search_in_file, edit_file_patch, run_lean_verify.\n\n"
            f"Task:\n{guidance}"
        )

        try:
            payload = json.loads(raw_reply)
        except json.JSONDecodeError:
            guidance = (
                "DOCSTRING-ONLY TASK — DO NOT MODIFY PROOF LOGIC.\n"
                "Your previous reply was not valid JSON.  "
                "Return ONLY a JSON object with 'thought' and 'tool_calls'.\n"
                f"Still missing tags for:\n{missing_str}"
            )
            continue

        tool_calls = payload.get("tool_calls", []) if isinstance(payload, dict) else []
        for call in tool_calls:
            if not isinstance(call, dict):
                continue
            tool_name = call.get("tool")
            arguments = call.get("arguments", {})
            if not isinstance(tool_name, str) or not isinstance(arguments, dict):
                continue
            try:
                registry.call(tool_name, **arguments)
            except Exception as exc:  # noqa: BLE001
                console.print(f"  [Gate 4b] tool '{tool_name}' error: {exc}")

        missing_now = check_used_in_tags([target_file])
        if not missing_now:
            console.print("[green]\\[Gate 4b] All Used-in tags patched.")
            return

        missing_str = "\n".join(f"  - {m}" for m in missing_now)
        guidance = (
            "DOCSTRING-ONLY TASK — DO NOT MODIFY PROOF LOGIC.\n"
            f"Still missing 'Used in:' tags for:\n{missing_str}\n"
            "Apply edit_file_patch for the remaining declarations only.  "
            "Do NOT touch any proof logic or tactic lines."
        )

    raise Gate4Error(missing_now)


def _apply_lib_insert(file_path: str, anchor_id: str, content: str) -> str:
    """Insert content into a Lib/Glue file at the given anchor. Returns updated content."""
    if file_path not in LIB_GLUE_ANCHORS:
        raise ValueError(f"[Phase 4] Unknown Lib file for lib_write: {file_path}")
    anchors = LIB_GLUE_ANCHORS[file_path]
    if anchor_id not in anchors:
        raise ValueError(
            f"[Phase 4] Unknown anchor_id '{anchor_id}' for {file_path}. "
            f"Allowed: {list(anchors.keys())}"
        )
    cfg = anchors[anchor_id]
    regex = cfg["regex"]
    insert_mode = cfg.get("insert", "before")

    full_path = PROJECT_ROOT / file_path
    if not full_path.exists():
        raise FileNotFoundError(f"[Phase 4] Lib file does not exist: {file_path}")
    original = full_path.read_text(encoding="utf-8")

    matches = list(re.finditer(regex, original, flags=re.MULTILINE))
    if not matches:
        raise ValueError(
            f"[Phase 4] Anchor regex not found in {file_path}: {regex[:50]}..."
        )
    if len(matches) > 1:
        raise ValueError(
            f"[Phase 4] Anchor matches {len(matches)} locations in {file_path}"
        )
    m = matches[0]
    insert_body = "\n\n" + content.strip() + "\n"
    if insert_mode == "before":
        insert_at = m.start()
        updated = original[:insert_at] + insert_body + original[insert_at:]
    else:
        insert_at = m.end()
        updated = original[:insert_at] + insert_body + original[insert_at:]
    return updated


def phase4_persist(
    algorithm: str,
    target_file: str,
    plan: str,
    baseline_tracked: set[str],
    baseline_untracked: set[str],
) -> int:
    """Phase 4: Agent4 persists documentation (Glue + Layer 1).

    Returns new_tricks_added.
    """
    console.rule("[bold cyan]Phase 4/5 — Persist Documentation")
    registry = ToolRegistry()
    registry.register_default_tools()

    # Strict precondition: only persist after build is green and sorry is zero.
    verify_result = registry.call("run_lean_verify", target_file)
    if int(verify_result.get("exit_code", 1)) != 0 or int(verify_result.get("sorry_count", 1)) != 0:
        raise RuntimeError(
            "[Phase 4] BLOCKED: build must be green and sorry_count must be 0 "
            "before documentation persistence."
        )

    tricks_before = snapshot_file("docs/GLUE_TRICKS.md")
    tricks_sections_before = count_glue_tricks_sections()

    modified_lean_files = _get_modified_lean_files(
        baseline_tracked,
        baseline_untracked,
    )
    console.print(
        f"[cyan]\\[Phase 4] Modified Lean files detected: "
        f"{modified_lean_files or [target_file]}"
    )

    meta_b = load_meta_prompt_b()
    agent4 = Agent("persister", extra_files=modified_lean_files or [target_file])
    allowed_anchors = DOC_ANCHORS

    lib_anchor_info = "\n".join(
        f"- {f}: {list(a.keys())}" for f, a in LIB_GLUE_ANCHORS.items()
    )

    persistence_output = agent4.call(
        f"Persist the completed proof for algorithm '{algorithm}' using "
        f"Meta-Prompt B below.\n\n## Meta-Prompt B\n{meta_b}\n\n"
        f"## Approved proof plan (use this as [PROOF INPUT] for Meta-Prompt B)\n{plan}\n\n"
        f"## Modified Lean files\n"
        + "\n".join(f"- {f}" for f in (modified_lean_files or [target_file]))
        + "\n\n## Allowed doc anchor IDs\n"
        + "\n".join(f"- {k}" for k in sorted(allowed_anchors))
        + "\n\n## Lib/Glue anchor IDs (for lib_write ops)\n"
        + lib_anchor_info
    )
    console.print(
        f"[green]\\[Agent4] Persistence output generated "
        f"({len(persistence_output)} chars)."
    )

    try:
        patch_ops = _parse_persister_json(persistence_output)
    except json.JSONDecodeError as exc:
        raise RuntimeError(
            "[Phase 4] Persister returned invalid JSON. "
            f"line={exc.lineno}, col={exc.colno}, msg={exc.msg}"
        ) from exc

    if not isinstance(patch_ops, list):
        raise RuntimeError("[Phase 4] Persister output must be a JSON array.")

    patterns_from_output: list[str] = []
    catalog_patch_fragments: list[str] = []
    patch_ops_summary: list[dict] = []
    lib_write_ops: list[dict] = []
    algorithm_refactor_ops: list[dict] = []
    # Guard A: track anchors already patched in this run to prevent double-insert
    # when Agent4 emits two ops with the same anchor in one response.
    patched_anchors: set[str] = set()

    for idx, op in enumerate(patch_ops, start=1):
        if not isinstance(op, dict):
            raise RuntimeError(f"[Phase 4] patch_ops[{idx}] must be an object.")
        op_type = op.get("op", "doc_patch")

        if op_type == "doc_patch" or op_type is None:
            anchor_id = op.get("anchor")
            content = op.get("content")
            if not isinstance(anchor_id, str) or not isinstance(content, str):
                raise RuntimeError(
                    f"[Phase 4] patch_ops[{idx}] doc_patch requires 'anchor' and 'content'."
                )
            if anchor_id not in allowed_anchors:
                raise RuntimeError(
                    f"[Phase 4] patch_ops[{idx}] uses non-allowed anchor: {anchor_id}"
                )
            # Guard A: skip if this anchor was already patched earlier in this run.
            if anchor_id in patched_anchors:
                console.print(
                    f"[yellow]\\[Agent4] Skipping duplicate anchor {anchor_id} in same run"
                )
                continue
            # Guard B: for CATALOG_ALGO_LAYER, skip if algorithm section already exists.
            if anchor_id == "CATALOG_ALGO_LAYER":
                catalog_text = (PROJECT_ROOT / "docs/CATALOG.md").read_text(encoding="utf-8")
                algo_pat = (
                    rf"^## Algorithm Layer \(Layer 2\)\s+—\s+`Algorithms/{re.escape(algorithm)}\.lean`"
                )
                if re.search(algo_pat, catalog_text, re.MULTILINE):
                    console.print(
                        f"[cyan]\\[Agent4] Algorithm section already exists in CATALOG.md — skipping"
                    )
                    continue
            cfg = allowed_anchors[anchor_id]
            patch_result = registry.call(
                "apply_doc_patch",
                path=cfg["path"],
                anchor=cfg["regex"],
                new_content=content,
            )
            changed = bool(patch_result.get("changed", False))
            patch_ops_summary.append({
                "op": "doc_patch",
                "anchor": anchor_id,
                "path": cfg["path"],
                "changed": changed,
            })
            if changed:
                patched_anchors.add(anchor_id)
                console.print(
                    f"[green]\\[Agent4] Patched {cfg['path']} via anchor {anchor_id}"
                )
                if cfg["path"] == "docs/GLUE_TRICKS.md":
                    patterns_from_output.extend(re.findall(
                        r"^#{3,4}\s+Pattern[^\n]*",
                        content,
                        flags=re.MULTILINE,
                    ))
                if cfg["path"] == "docs/CATALOG.md":
                    catalog_patch_fragments.append(content)
            else:
                console.print(
                    f"[cyan]\\[Agent4] Skipped duplicate content for {cfg['path']} ({anchor_id})"
                )
        elif op_type == "lib_write":
            lib_write_ops.append(op)
        elif op_type == "algorithm_refactor":
            algorithm_refactor_ops.append(op)
        else:
            raise RuntimeError(
                f"[Phase 4] patch_ops[{idx}] unknown op: {op_type}. "
                "Allowed: doc_patch, lib_write, algorithm_refactor."
            )

    lib_snapshots: dict[str, str] = {}
    algo_snapshots: dict[str, str] = {}

    if lib_write_ops:
        console.print("[cyan]\\[Phase 4] Applying lib_write ops...")
        for idx, op in enumerate(lib_write_ops, start=1):
            file_path = op.get("file")
            anchor_id = op.get("anchor_id")
            content = op.get("content")
            if not all(isinstance(x, str) for x in (file_path, anchor_id, content)):
                raise RuntimeError(
                    f"[Phase 4] lib_write op {idx} requires file, anchor_id, content."
                )
            if file_path not in lib_snapshots:
                lib_snapshots[file_path] = snapshot_file(file_path)
            updated = _apply_lib_insert(file_path, anchor_id, content)
            registry.call("overwrite_file", path=file_path, content=updated)
            patch_ops_summary.append({
                "op": "lib_write",
                "path": file_path,
                "anchor_id": anchor_id,
            })
            console.print(f"[green]\\[Agent4] Inserted lemma into {file_path} via {anchor_id}")

        # Full-library build: catches cascade failures in algorithm files caused
        # by changes to Lib/Glue lemma signatures or new lemma insertions.
        build_result = lake_build(target="SGDAlgorithms")
        if build_result.returncode != 0:
            console.print("[red]\\[Phase 4] lib_write caused build failure. Rolling back...")
            for path, snap in lib_snapshots.items():
                registry.call("overwrite_file", path=path, content=snap)
            raise RuntimeError(
                "[Phase 4] Lib/refactor caused build failure. Rolled back.\n"
                + (build_result.errors or "Unknown error")
            )

    if algorithm_refactor_ops:
        console.print("[cyan]\\[Phase 4] Applying algorithm_refactor ops...")
        for idx, op in enumerate(algorithm_refactor_ops, start=1):
            file_path = op.get("file")
            patches = op.get("patches")
            if not isinstance(file_path, str) or not isinstance(patches, list):
                raise RuntimeError(
                    f"[Phase 4] algorithm_refactor op {idx} requires file and patches list."
                )
            if file_path not in algo_snapshots:
                algo_snapshots[file_path] = snapshot_file(file_path)
            for pidx, patch in enumerate(patches):
                old_str = patch.get("old_str")
                new_str = patch.get("new_str")
                if not isinstance(old_str, str) or not isinstance(new_str, str):
                    raise RuntimeError(
                        f"[Phase 4] algorithm_refactor op {idx} patch {pidx} "
                        "requires old_str and new_str."
                    )
                registry.call("edit_file_patch", path=file_path, old_str=old_str, new_str=new_str)
            patch_ops_summary.append({
                "op": "algorithm_refactor",
                "path": file_path,
                "patches_count": len(patches),
            })
            console.print(f"[green]\\[Agent4] Refactored {file_path} ({len(patches)} patch(es))")

        # Full-library build: catches cascade failures across all algorithm files,
        # not just the directly refactored ones.
        build_result = lake_build(target="SGDAlgorithms")
        if build_result.returncode != 0:
            console.print("[red]\\[Phase 4] algorithm_refactor caused build failure. Rolling back...")
            for path, snap in algo_snapshots.items():
                registry.call("overwrite_file", path=path, content=snap)
            raise RuntimeError(
                "[Phase 4] Algorithm refactor caused build failure. Rolled back.\n"
                + (build_result.errors or "Unknown error")
            )

    # Doc-code alignment: if CATALOG lemma status was touched, the lemmas must exist in Lib/.
    if catalog_patch_fragments:
        lib_names = _collect_lib_declaration_names()
        touched_lemmas: set[str] = set()
        for fragment in catalog_patch_fragments:
            touched_lemmas.update(_extract_catalog_lemma_names(fragment))
        missing = sorted(name for name in touched_lemmas if name not in lib_names)
        if missing:
            raise RuntimeError(
                "[Phase 4] CATALOG-Lib alignment failed. Missing Lib declarations: "
                + ", ".join(missing)
            )

    tricks_after = snapshot_file("docs/GLUE_TRICKS.md")
    tricks_sections_after = count_glue_tricks_sections()
    new_tricks = tricks_sections_after - tricks_sections_before

    # Gate 3: GLUE_TRICKS validation (BLOCKING)
    glue_changed = (tricks_before != tricks_after) or (new_tricks > 0)
    unique_patterns = sorted(set(patterns_from_output))
    gate3_ok, missing_patterns = check_glue_tricks_gate(
        tricks_before,
        tricks_after,
        unique_patterns,
    )
    if not gate3_ok:
        raise RuntimeError(
            "[Gate 3] Missing GLUE_TRICKS pattern entries: "
            + ", ".join(missing_patterns)
        )

    if glue_changed:
        console.print(
            f"[green]\\[Gate 3] GLUE_TRICKS.md updated — "
            f"{new_tricks} new pattern(s)."
        )
    else:
        console.print("[green]\\[Gate 3] No new patterns — GLUE_TRICKS.md unchanged.")

    # Gate 4: Used-in tag check — covers all modified Lean files, not just target
    modified = modified_lean_files or [target_file]
    missing = check_used_in_tags(modified)
    if missing:
        raise Gate4Error(missing)
    else:
        console.print("[green]\\[Gate 4] All Used-in tags present.")

    AuditLogger.get().add_phase4_data(patch_ops_summary)
    return new_tricks


def phase5_finalize(
    algorithm: str,
    new_tricks: int,
    phase3_audit: dict,
    total_attempts: int,
) -> None:
    """Phase 5: Persist physical metrics and print audit report."""
    console.rule("[bold cyan]Phase 5/5 — Finalize Metrics")

    store = MetricsStore()
    record = capture_physical_metrics(
        algorithm=algorithm,
        new_tricks_added=new_tricks,
        phase3_execution_history=phase3_audit.get("execution_history", []),
        phase3_attempts=total_attempts,
        estimated_token_consumption=int(
            phase3_audit.get("estimated_token_consumption", 0)
        ),
    )
    store.append(record)

    console.print(Panel(
        f"Algorithm:          {algorithm}\n"
        f"Build exit code:    {record.physical_exit_code}\n"
        f"Repo sorry count:   {record.total_repo_sorry_count}\n"
        f"\n"
        f"── Leverage Metrics ────────────────────────────────────\n"
        f"New Lib decls:      {record.new_lib_declarations}\n"
        f"Algo call hits:     {record.algorithm_calls_to_new_lib_declarations}\n"
        f"Physical leverage:  {record.physical_leverage_rate:.1%}  "
        f"[calls/(calls+decls)]\n"
        f"L_coverage:         {record.lib_coverage_rate:.1%}  "
        f"[used decls / total new decls]\n"
        f"L_density:          {record.lib_density_rate:.2f}  "
        f"[total calls / used decls]\n"
        f"\n"
        f"── Phase 3 Cost ────────────────────────────────────────\n"
        f"P3 retries:         {record.phase3_retry_count}\n"
        f"Sorry attempts:     {total_attempts}\n"
        f"Est. token usage:   {record.estimated_token_consumption}\n"
        f"\n"
        f"── Documentation ───────────────────────────────────────\n"
        f"Total glue lemmas:  {record.total_glue_lemmas}\n"
        f"Total L1 lemmas:    {record.total_layer1_lemmas}\n"
        f"New tricks added:   {new_tricks}\n"
        f"Final sorry count:  {record.final_sorry_count}\n"
        f"Doc-code aligned:   {'YES' if record.doc_code_alignment_ok else 'NO'}\n",
        title="[bold green]Run Complete (Physical Audit)",
    ))
    if not record.doc_code_alignment_ok:
        console.print(Panel(
            "\n".join(record.doc_code_alignment_missing or []),
            title="[red]Audit Mismatch: Doc-Code Alignment",
        ))


# ---------------------------------------------------------------------------
# Main orchestration
# ---------------------------------------------------------------------------

def run(
    algorithm: str,
    update_rule: str,
    proof_sketch: str,
    archetype: str,
    target_file: str | None = None,
    max_retries: int = MAX_PHASE3_RETRIES,
    force_low_leverage: bool = False,
) -> None:
    """Execute the full 5-phase pipeline."""

    if target_file is None:
        target_file = f"Algorithms/{algorithm}.lean"

    baseline_tracked, baseline_untracked = _capture_lean_baseline()
    audit = AuditLogger.get()
    audit.start_run(algorithm)
    success = False
    _lakefile_added_by_us = False
    files_modified: list[str] = []
    merged_phase3_audit = {
        "execution_history": [],
        "attempt_failures": [],
        "estimated_token_consumption": 0,
        "retry_count": 0,
    }

    try:
        with Progress(
            SpinnerColumn(),
            TextColumn("{task.description}"),
            BarColumn(),
            transient=True,
        ) as progress:
            task = progress.add_task("Orchestrating...", total=5)

            # Phase 1
            audit.set_phase(1)
            progress.update(task, description="Phase 1/5: Generating prover prompt...")
            prover_prompt = phase1_generate_prompt(
                algorithm, update_rule, proof_sketch, archetype
            )
            progress.advance(task)

            # Register the algorithm module in lakefile.lean before Phase 3 so
            # that `lake build Algorithms.<name>` succeeds.  Tracked so we can
            # roll back on failure.
            _lakefile_added_by_us = _ensure_algorithm_in_lakefile(
                Path(target_file).stem
            )

            # Phase 2 (may loop on re-plan)
            success = False
            total_attempts = 0
            while not success:
                audit.set_phase(2)
                progress.update(task, description="Phase 2/5: Planning & approval...")
                plan, agent1, agent2 = phase2_plan_and_approve(
                    prover_prompt, force_low_leverage
                )
                progress.advance(task)

                # Phase 3
                audit.set_phase(3)
                progress.update(task, description="Phase 3/5: Proving (fill sorry)...")
                success, attempts, _, phase3_audit = phase3_prove(
                    agent2, target_file, plan, max_retries=max_retries, archetype=archetype
                )
                total_attempts += attempts
                merged_phase3_audit["execution_history"].extend(
                    phase3_audit.get("execution_history", [])
                )
                merged_phase3_audit["attempt_failures"].extend(
                    phase3_audit.get("attempt_failures", [])
                )
                merged_phase3_audit["estimated_token_consumption"] += int(
                    phase3_audit.get("estimated_token_consumption", 0)
                )
                merged_phase3_audit["retry_count"] += int(
                    phase3_audit.get("retry_count", 0)
                )
                if not success:
                    progress.reset(task)
                    progress.advance(task)  # re-enter at phase 2

            progress.advance(task)

            # Phase 4
            audit.set_phase(4)
            progress.update(task, description="Phase 4/5: Persisting docs...")
            try:
                new_tricks = phase4_persist(
                    algorithm,
                    target_file,
                    plan,
                    baseline_tracked=baseline_tracked,
                    baseline_untracked=baseline_untracked,
                )
            except Gate4Error as exc:
                console.print(
                    f"[yellow]\\[Gate 4] Missing Used-in tags detected "
                    f"({len(exc.missing)} declaration(s)).  "
                    "Entering tag-fixup loop …"
                )
                phase3b_fix_tags(target_file, exc.missing)
                # Retry Phase 4 now that all tags are present.
                new_tricks = phase4_persist(
                    algorithm,
                    target_file,
                    plan,
                    baseline_tracked=baseline_tracked,
                    baseline_untracked=baseline_untracked,
                )
            progress.advance(task)

            # Phase 5
            audit.set_phase(5)
            progress.update(task, description="Phase 5/5: Finalizing metrics...")
            phase5_finalize(
                algorithm,
                new_tricks=new_tricks,
                phase3_audit=merged_phase3_audit,
                total_attempts=total_attempts,
            )
            progress.advance(task)

            success = True
            all_modified = _get_modified_lean_files(
                baseline_tracked,
                baseline_untracked,
            )
            docs_in_diff = {f for f in _git_diff_files() if f.startswith("docs/")}
            files_modified = sorted(set(all_modified) | docs_in_diff)
    finally:
        audit.add_phase3_data(
            merged_phase3_audit.get("execution_history", []),
            merged_phase3_audit.get("attempt_failures", []),
        )
        extra_snapshot = [target_file] if not success else []
        audit.finish_run(success, files_modified, extra_files_to_snapshot=extra_snapshot)
        if files_modified:
            console.print(
                f"[dim][Audit] Files modified: {', '.join(files_modified)}[/dim]"
            )
        if not success and _lakefile_added_by_us:
            _remove_algorithm_from_lakefile(Path(target_file).stem)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _interactive_input() -> dict[str, str]:
    """Prompt the user for algorithm card fields interactively."""
    console.print("[bold]Interactive mode — enter algorithm details.\n")
    return {
        "algorithm": console.input("[bold]Algorithm name:[/bold] ").strip(),
        "update_rule": console.input("[bold]Update rule:[/bold] ").strip(),
        "proof_sketch": console.input("[bold]Proof sketch:[/bold] ").strip(),
        "archetype": console.input("[bold]Archetype (A/B):[/bold] ").strip().upper(),
    }


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Multi-agent orchestrator for StochOptLib proof automation."
    )
    parser.add_argument("--algorithm", type=str, help="Algorithm name")
    parser.add_argument("--update-rule", type=str, help="Mathematical update formula")
    parser.add_argument("--proof-sketch", type=str, help="Natural-language proof sketch")
    parser.add_argument("--archetype", type=str, choices=["A", "B"], help="A or B")
    parser.add_argument("--target-file", type=str, default=None,
                        help="Target .lean file (default: Algorithms/<algorithm>.lean)")
    parser.add_argument("--max-retries", type=int, default=MAX_PHASE3_RETRIES,
                        help="Max sorry-closing retries (default: 5)")
    parser.add_argument("--force-low-leverage", action="store_true",
                        help="Override the ≥50%% leverage gate")
    parser.add_argument("--interactive", action="store_true",
                        help="Prompt for algorithm card interactively")

    args = parser.parse_args()

    if args.interactive:
        fields = _interactive_input()
    else:
        if not all([args.algorithm, args.update_rule, args.proof_sketch, args.archetype]):
            parser.error(
                "Provide --algorithm, --update-rule, --proof-sketch, and "
                "--archetype, or use --interactive."
            )
        fields = {
            "algorithm": args.algorithm,
            "update_rule": args.update_rule,
            "proof_sketch": args.proof_sketch,
            "archetype": args.archetype,
        }

    run(
        algorithm=fields["algorithm"],
        update_rule=fields["update_rule"],
        proof_sketch=fields["proof_sketch"],
        archetype=fields["archetype"],
        target_file=args.target_file,
        max_retries=args.max_retries,
        force_low_leverage=args.force_low_leverage,
    )


if __name__ == "__main__":
    main()
