"""Phase 1 and Phase 2 orchestration steps."""
from __future__ import annotations

import json
import sys

from rich.console import Console
from rich.panel import Panel

from orchestrator.agents import Agent
from orchestrator.audit_logger import AuditLogger
from orchestrator.context_builders import _extract_symbol_manifest
from orchestrator.error_classifier import _json_candidates
from orchestrator.prompts import build_algorithm_card, load_meta_prompt_a
from orchestrator.verify import check_leverage_gate

console = Console()

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
        review: dict = {}
        for _retry in range(3):
            review_raw = agent1.call(review_prompt)
            if not review_raw.strip():
                console.print(
                    f"[yellow][Phase 2] Reviewer returned empty response "
                    f"(attempt {_retry + 1}/3)"
                )
                continue
            # Extract the JSON object even if the LLM prepended prose text.
            # Try three strategies in order:
            #   1. Direct parse (LLM followed instructions exactly)
            #   2. Find first '{' and parse from there
            #   3. Extract a ```json ... ``` fenced block
            _parsed: dict | None = None
            _parse_err: json.JSONDecodeError | None = None
            for _candidate in _json_candidates(review_raw):
                try:
                    _obj = json.loads(_candidate)
                    if isinstance(_obj, dict):
                        _parsed = _obj
                        break
                except json.JSONDecodeError as _exc:
                    _parse_err = _exc
            if _parsed is not None:
                review = _parsed
                break
            exc = _parse_err or json.JSONDecodeError("no JSON found", review_raw, 0)
            if _retry < 2:
                console.print(
                    f"[yellow][Phase 2] Reviewer returned invalid JSON "
                    f"(attempt {_retry + 1}/3): {exc.msg}"
                )
                review_prompt = (
                    "Your previous response could not be parsed as JSON. "
                    "Return ONLY a single JSON object with NO surrounding text:\n"
                    '{"decision": "APPROVED" | "AMEND" | "REJECTED", "feedback": "..."}\n\n'
                    "Do NOT include any explanation, markdown, or code fences.\n\n"
                    f"Plan to review:\n{plan}"
                )
                continue
            raise RuntimeError(
                "[Phase 2] Reviewer returned invalid JSON after 3 attempts. "
                f"line={exc.lineno}, col={exc.colno}, msg={exc.msg}"
            ) from exc
        else:
            raise RuntimeError("[Phase 2] Reviewer returned empty response after 3 attempts.")

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


# ---------------------------------------------------------------------------
# Escalation context helpers (Change 4 / 6b)
# ---------------------------------------------------------------------------

_ESCALATION_CHAR_LIMIT = 20_000


def _extract_declaration_skeleton(lines: list[str]) -> str:
    """Return a skeleton of *lines*: keep declaration headers, strip proof bodies.

    A 'proof body' is everything between a line that ends with ':= by' (or
    starts a ``:=`` assignment) and the next line at column 0 that starts a new
    top-level declaration (``def``, ``theorem``, ``lemma``, ``noncomputable``,
    ``structure``, ``namespace``, ``end``, ``--``, ``#``, blank).
    """
    DECL_KW = re.compile(r"^\s*(def |theorem |lemma |noncomputable |structure |namespace |end |@\[|--|\s*#)")
    in_body = False
    result: list[str] = []
    for line in lines:
        stripped = line.rstrip()
        if DECL_KW.match(line):
            in_body = False
        if in_body:
            continue
        result.append(stripped)
        if re.search(r":=\s*by\s*$", stripped) or re.search(r":=\s*$", stripped):
            result.append("  sorry  -- (proof body omitted in skeleton)")
            in_body = True
    return "\n".join(result)


def _build_escalation_file_context(target_file: str, stuck_line: int | None = None) -> str:
    """Return file content for Agent2 escalation with a soft 20k-char cap.

    If the file fits within *_ESCALATION_CHAR_LIMIT* characters it is returned
    verbatim.  Otherwise a declaration skeleton plus a ±200-line window around
    *stuck_line* (when provided) is returned instead.
    """
    try:
        content = load_file(target_file)
    except Exception:  # noqa: BLE001
        return "(file missing or unreadable)"

    if len(content) <= _ESCALATION_CHAR_LIMIT:
        return content

    lines = content.splitlines()
    skeleton = _extract_declaration_skeleton(lines)

    if stuck_line is not None:
        window_start = max(0, stuck_line - 200)
        window_end = min(len(lines), stuck_line + 200)
        window = "\n".join(lines[window_start:window_end])
        return (
            f"-- SKELETON (proof bodies omitted for brevity)\n{skeleton}\n\n"
            f"-- FULL CONTEXT around line {stuck_line} (±200 lines)\n{window}"
        )
    return f"-- SKELETON (proof bodies omitted; file exceeds {_ESCALATION_CHAR_LIMIT} chars)\n{skeleton}"


def _audit_staging_usage(
    target_file: str,
    staging_path: "Path",
    console_print: "Any",
) -> dict[str, bool]:
    """Return ``{lemma_name: used}`` for all declarations in the staging file.

    Scans the final algorithm file for each declaration name found in the
    staging file and reports whether it is referenced at least once.
    """
    staging_content = ""
    if staging_path.exists():
        staging_content = staging_path.read_text(encoding="utf-8")
    else:
        try:
            _rel = str(staging_path.relative_to(PROJECT_ROOT))
            staging_content = snapshot_file(_rel)
        except Exception:  # noqa: BLE001
            staging_content = ""
    if not staging_content:
        return {}
    try:
        target_content = load_file(target_file)
    except Exception:  # noqa: BLE001
        target_content = ""

    decl_names = re.findall(r"(?:theorem|lemma|def)\s+(\w+)", staging_content)

    usage: dict[str, bool] = {}
    for name in decl_names:
        used = bool(re.search(rf"\b{re.escape(name)}\b", target_content))
        usage[name] = used
        status = "USED" if used else "UNUSED (candidate for cleanup)"
        console_print(f"  [Staging] {name} — {status}")

    return usage


