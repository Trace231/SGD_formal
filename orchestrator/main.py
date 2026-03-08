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
import json
import re
import subprocess
import sys
from dataclasses import dataclass

from rich.console import Console
from rich.panel import Panel
from rich.progress import BarColumn, Progress, SpinnerColumn, TextColumn

from orchestrator.agents import (
    Agent,
    ToolRegistry,
    escalate,
)
from orchestrator.config import DOC_ANCHORS, MAX_PHASE3_RETRIES, PROJECT_ROOT
from orchestrator.file_io import (
    load_file,
    snapshot_file,
)
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
from orchestrator.verify import (
    check_glue_tricks_gate,
    check_leverage_gate,
    check_used_in_tags,
)

console = Console()

_CATALOG_LEMMA_HEADING_RE = re.compile(r"^####\s+`([^`]+)`", re.MULTILINE)
_LIB_DECL_RE = re.compile(
    r"^(?:theorem|lemma|noncomputable\s+def|def)\s+([A-Za-z_]\w*)",
    re.MULTILINE,
)


@dataclass
class ExecutionResult:
    """Result envelope for each Agent3 tool execution."""

    status_code: str  # SUCCESS / ERROR / BLOCKED
    message: str
    attempt: int = 0


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

    prompt_text = agent1.call(
        f"Generate a complete Prover prompt by instantiating the Meta-Prompt A "
        f"template below with the algorithm card.\n\n"
        f"## Meta-Prompt A Template\n{meta_a}\n\n"
        f"## Algorithm Card\n{card}"
    )
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

    plan = agent2.call(prover_prompt)
    console.print(Panel(
        plan[:500] + "..." if len(plan) > 500 else plan,
        title="[cyan]Agent2 — Initial Plan",
    ))

    round_num = 0
    while True:
        round_num += 1
        review_raw = agent1.call(
            "Review the plan from Agent2 and return ONLY valid JSON with this schema:\n"
            "{\n"
            '  "decision": "APPROVED" | "REJECTED" | "AMEND",\n'
            '  "feedback": "<required when decision is AMEND; optional otherwise>"\n'
            "}\n\n"
            f"Plan to review:\n{plan}"
        )

        try:
            review = json.loads(review_raw)
        except json.JSONDecodeError as exc:
            raise RuntimeError(
                "[Phase 2] Reviewer returned invalid JSON. "
                f"line={exc.lineno}, col={exc.colno}, msg={exc.msg}"
            ) from exc

        if not isinstance(review, dict):
            raise RuntimeError("[Phase 2] Reviewer response must be a JSON object.")

        decision = review.get("decision")
        feedback = review.get("feedback", "")
        feedback_text = feedback if isinstance(feedback, str) else str(feedback)

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
) -> tuple[bool, int, str, dict]:
    """Phase 3: Agent2 ↔ Agent3 proving loop + Agent5 escalation.

    Returns (success, attempts, errors_or_empty, audit).
    """
    console.rule("[bold cyan]Phase 3/5 — Prove (fill sorry)")

    agent3 = Agent("sorry_closer", extra_files=[target_file])
    registry = ToolRegistry()
    registry.register_default_tools()
    diag_log: list[str] = []

    guidance = agent2.call(
        "Provide initial proving guidance for Agent3.  Specify which sorry "
        "to tackle first and the recommended proof strategy (Mathlib lemma, "
        "glue pattern letter, etc.)."
    )
    console.print(Panel(
        guidance[:400] + "..." if len(guidance) > 400 else guidance,
        title="[cyan]Agent2 — Initial Guidance",
    ))

    last_errors = ""
    last_sorry_count = 0
    attempts = 0
    execution_history: list[ExecutionResult] = []
    token_char_budget = 0

    for attempt in range(1, max_retries + 1):
        attempts = attempt
        prover_prompt = (
            "Use tools to close sorry placeholders.\n"
            "Return ONLY valid JSON with keys: thought, tool_calls.\n"
            "Each tool call must be an object: "
            '{"tool": "<name>", "arguments": {...}}.\n'
            "Allowed tools: read_file, edit_file_patch, run_lean_verify.\n"
            "Do not claim completion in text; verification decides completion.\n\n"
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
            guidance = agent2.call(
                f"Attempt {attempt} failed.\n"
                "Invalid JSON format from Agent3.\n"
                "Adjust your guidance so Agent3 returns strict JSON tool calls."
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
            guidance = agent2.call(
                f"Attempt {attempt} failed.\n"
                "Agent3 JSON top-level was not an object.\n"
                "Adjust your guidance for strict output schema."
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
            guidance = agent2.call(
                f"Attempt {attempt} failed.\n"
                "Agent3 output schema invalid: tool_calls is not a list.\n"
                "Adjust your guidance for strict output schema."
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
                if tool_name == "edit_file_patch":
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

        # Strict success criterion: verify result only.
        if exit_code == 0 and last_sorry_count == 0:
            prove_state = "PROVE_SUCCESS"
        else:
            prove_state = "PROVE_RETRY"

        blocked_msgs = [r.message for r in exec_results if r.status_code == "BLOCKED"]
        error_msgs = [r.message for r in exec_results if r.status_code == "ERROR"]
        execution_history.extend(exec_results)

        build_ok = prove_state == "PROVE_SUCCESS"
        status = "OK" if build_ok else "FAIL"
        console.print(
            f"  [Agent3] attempt {attempt}/{max_retries} — "
            f"build={status}, sorry={last_sorry_count}"
        )

        if prove_state == "PROVE_SUCCESS":
            return True, attempts, "", {
                "execution_history": [r.__dict__ for r in execution_history],
                "estimated_token_consumption": max(1, token_char_budget // 4),
                "retry_count": sum(
                    1
                    for r in execution_history
                    if r.status_code in {"ERROR", "BLOCKED"}
                ),
            }

        # Intelligent retry prompts.
        if blocked_msgs:
            blocked_hint = (
                f"Security violation: You cannot edit path {blocked_path or '?'}."
                " Stay within Algorithms/ or Lib/."
            )
            diag_log.extend([f"attempt={attempt} {m}" for m in blocked_msgs])
            guidance = agent2.call(
                f"Attempt {attempt} failed.\n"
                f"{blocked_hint}\n"
                "Adjust your guidance for safe path usage."
            )
            continue

        line_match = re.search(r":(\d+):\d+|line\s+(\d+)", verify_text, flags=re.IGNORECASE)
        line_no = line_match.group(1) or line_match.group(2) if line_match else "unknown"
        retry_hint = (
            f"Your previous edit caused a Lean error at line {line_no}. Fix it."
        )
        if error_msgs:
            diag_log.extend([f"attempt={attempt} {m}" for m in error_msgs])
        guidance = agent2.call(
            f"Attempt {attempt} failed.\n"
            f"{retry_hint}\n"
            f"Build exit code: {exit_code}\n"
            f"Sorry count: {last_sorry_count}\n"
            f"Errors:\n```\n{verify_text[:2000]}\n```\n"
            "Adjust your guidance for Agent3."
        )

    console.print("[red bold]Max retries exhausted — escalating to Agent5.")
    if diag_log:
        console.print(Panel(
            "\n".join(diag_log[-12:]),
            title="[yellow]Phase 3 Retry Log",
        ))
    agent5 = Agent("diagnostician", extra_files=[target_file])
    sorry_context = load_file(target_file)
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
            "estimated_token_consumption": max(1, token_char_budget // 4),
            "retry_count": sum(
                1
                for r in execution_history
                if r.status_code in {"ERROR", "BLOCKED"}
            ),
        }

    return False, attempts, last_errors, {
        "execution_history": [r.__dict__ for r in execution_history],
        "estimated_token_consumption": max(1, token_char_budget // 4),
        "retry_count": sum(
            1
            for r in execution_history
            if r.status_code in {"ERROR", "BLOCKED"}
        ),
    }


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

    persistence_output = agent4.call(
        f"Persist the completed proof for algorithm '{algorithm}' using "
        f"Meta-Prompt B below.\n\n## Meta-Prompt B\n{meta_b}\n\n"
        f"## Approved proof plan (use this as [PROOF INPUT] for Meta-Prompt B)\n{plan}\n\n"
        f"## Modified Lean files\n"
        + "\n".join(f"- {f}" for f in (modified_lean_files or [target_file]))
        + "\n\n## Allowed anchor IDs\n"
        + "\n".join(f"- {k}" for k in sorted(allowed_anchors))
    )
    console.print(
        f"[green]\\[Agent4] Persistence output generated "
        f"({len(persistence_output)} chars)."
    )

    try:
        patch_ops = json.loads(persistence_output)
    except json.JSONDecodeError as exc:
        raise RuntimeError(
            "[Phase 4] Persister returned invalid JSON. "
            f"line={exc.lineno}, col={exc.colno}, msg={exc.msg}"
        ) from exc

    if not isinstance(patch_ops, list):
        raise RuntimeError("[Phase 4] Persister output must be a JSON array.")

    patterns_from_output: list[str] = []
    catalog_patch_fragments: list[str] = []
    for idx, op in enumerate(patch_ops, start=1):
        if not isinstance(op, dict):
            raise RuntimeError(f"[Phase 4] patch_ops[{idx}] must be an object.")
        anchor_id = op.get("anchor")
        content = op.get("content")
        if not isinstance(anchor_id, str) or not isinstance(content, str):
            raise RuntimeError(
                f"[Phase 4] patch_ops[{idx}] requires string fields 'anchor' and 'content'."
            )
        if anchor_id not in allowed_anchors:
            raise RuntimeError(
                f"[Phase 4] patch_ops[{idx}] uses non-allowed anchor: {anchor_id}"
            )

        cfg = allowed_anchors[anchor_id]
        patch_result = registry.call(
            "apply_doc_patch",
            path=cfg["path"],
            anchor=cfg["regex"],
            new_content=content,
        )
        changed = bool(patch_result.get("changed", False))
        if changed:
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
        raise RuntimeError(f"[Gate 4] Missing Used-in tags: {missing}")
    else:
        console.print("[green]\\[Gate 4] All Used-in tags present.")

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
        f"Physical leverage:  {record.physical_leverage_rate:.1%}\n"
        f"Build exit code:    {record.physical_exit_code}\n"
        f"Repo sorry count:   {record.total_repo_sorry_count}\n"
        f"New Lib decls:      {record.new_lib_declarations}\n"
        f"Algo call hits:     {record.algorithm_calls_to_new_lib_declarations}\n"
        f"P3 retries:         {record.phase3_retry_count}\n"
        f"Est. token usage:   {record.estimated_token_consumption}\n"
        f"Doc-code aligned:   {'YES' if record.doc_code_alignment_ok else 'NO'}\n"
        f"Total glue lemmas:  {record.total_glue_lemmas}\n"
        f"Total L1 lemmas:    {record.total_layer1_lemmas}\n"
        f"New tricks added:   {new_tricks}\n"
        f"Sorry attempts:     {total_attempts}\n"
        f"Final sorry count:  {record.final_sorry_count}\n",
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

    with Progress(
        SpinnerColumn(),
        TextColumn("{task.description}"),
        BarColumn(),
        transient=True,
    ) as progress:
        task = progress.add_task("Orchestrating...", total=5)

        # Phase 1
        progress.update(task, description="Phase 1/5: Generating prover prompt...")
        prover_prompt = phase1_generate_prompt(
            algorithm, update_rule, proof_sketch, archetype
        )
        progress.advance(task)

        # Phase 2 (may loop on re-plan)
        success = False
        total_attempts = 0
        merged_phase3_audit: dict = {
            "execution_history": [],
            "estimated_token_consumption": 0,
            "retry_count": 0,
        }
        while not success:
            progress.update(task, description="Phase 2/5: Planning & approval...")
            plan, agent1, agent2 = phase2_plan_and_approve(
                prover_prompt, force_low_leverage
            )
            progress.advance(task)

            # Phase 3
            progress.update(task, description="Phase 3/5: Proving (fill sorry)...")
            success, attempts, _, phase3_audit = phase3_prove(
                agent2, target_file, plan, max_retries=max_retries
            )
            total_attempts += attempts
            merged_phase3_audit["execution_history"].extend(
                phase3_audit.get("execution_history", [])
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
        progress.update(task, description="Phase 4/5: Persisting docs...")
        new_tricks = phase4_persist(
            algorithm,
            target_file,
            plan,
            baseline_tracked=baseline_tracked,
            baseline_untracked=baseline_untracked,
        )
        progress.advance(task)

        # Phase 5
        progress.update(task, description="Phase 5/5: Finalizing metrics...")
        phase5_finalize(
            algorithm,
            new_tricks=new_tricks,
            phase3_audit=merged_phase3_audit,
            total_attempts=total_attempts,
        )
        progress.advance(task)


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
