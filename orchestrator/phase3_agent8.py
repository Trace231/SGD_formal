"""Agent8 Decision Hub — Phase 3 error-recovery state machine.

After all normal Agent3 retry attempts are exhausted, this module runs a
tick-based decision loop.  Each tick:
  1. Clears Agent8's context (anti-pollution).
  2. Builds a minimal diagnostic context (truncated file, errors, decision history).
  3. Calls Agent8 to produce a single JSON decision.
  4. Dispatches the chosen action (Agent3 tactical, Agent7 signature, Agent7→Agent6
     bridge lemma, Agent2 replan, or human gate).
  5. Verifies the result; appends to decision_history.
  6. Exits early on success (exit=0, sorry=0) or human gate.
"""
from __future__ import annotations

import functools
import json
import re
import tempfile
import time
from pathlib import Path
from typing import Any

from rich.console import Console
from rich.panel import Panel

from orchestrator.agents import Agent, ToolRegistry
from orchestrator.agent_callers import (
    _call_agent2_with_tools,
    _call_agent7_with_tools,
    _run_agent6_glue_loop,
)
from orchestrator.config import (
    AGENT8_DEBUG,
    AGENT8_FILE_WINDOW_RADIUS,
    AGENT8_HUMAN_GATE_CONSECUTIVE_THRESHOLD,
    AUDIT_DIR,
    PROJECT_ROOT,
    REFERENCE_FILES_WITH_DESCRIPTIONS,
    RETRY_LIMITS,
)
from orchestrator.context_builders import (
    _build_escalation_file_context,
    _extract_imported_algo_sigs,
    _prequery_dependency_signatures,
)
from orchestrator.error_classifier import _extract_first_error_line, _json_candidates
from orchestrator.file_io import load_file, snapshot_file

console = Console()

# ---------------------------------------------------------------------------
# Lib file descriptions — compact summary for Agent8 context
# ---------------------------------------------------------------------------

# Alias to the config-driven list — avoids hardcoding file descriptions here.
LIB_FILE_DESCRIPTIONS = REFERENCE_FILES_WITH_DESCRIPTIONS


def _extract_error_signature(errors_text: str) -> str:
    """Extract a short key phrase from the first build error (max 60 chars)."""
    if not errors_text:
        return ""
    for line in errors_text.splitlines():
        line = line.strip()
        if not line or line.startswith("--"):
            continue
        # Strip Lean file path prefix (e.g. "Algorithms/Foo.lean:42:3: error: ...")
        m = re.match(r".*?:\d+:\d+:\s*(?:error:\s*)?(.*)", line)
        if m:
            return m.group(1).strip()[:60]
        if len(line) > 10:
            return line[:60]
    return errors_text.strip()[:60]


# ---------------------------------------------------------------------------
# Context builder for each Agent8 tick
# ---------------------------------------------------------------------------

def _build_agent8_tick_context(
    target_file: str,
    errors_text: str,
    agent2_plan: str,
    decision_history: list[dict],
    staging_rel: str,
    agent9_plan: dict | None = None,
    plan_updated_tick: int = 0,
    midcheck_mode: bool = False,
    midcheck_turns_elapsed: int = 0,
) -> str:
    """Build a minimal, non-truncated diagnostic prompt for Agent8.

    Uses smart file truncation: only error-line ± AGENT8_FILE_WINDOW_RADIUS lines
    are included for the algorithm file.  Agent8 can request more context via
    read-only tools if needed.
    """
    # --- Algorithm file: smart truncation around error lines ---
    try:
        full_content = load_file(target_file)
        file_lines = full_content.splitlines()
    except FileNotFoundError:
        file_lines = []
        full_content = "(file does not exist)"

    error_line_nums: list[int] = []
    for line in errors_text.splitlines():
        m = re.search(r":(\d+):\d+:", line)
        if m:
            error_line_nums.append(int(m.group(1)))

    if error_line_nums and len(file_lines) > AGENT8_FILE_WINDOW_RADIUS * 3:
        # Build windows around each error line
        included: set[int] = set()
        for ln in error_line_nums:
            start = max(0, ln - 1 - AGENT8_FILE_WINDOW_RADIUS)
            end = min(len(file_lines), ln - 1 + AGENT8_FILE_WINDOW_RADIUS + 1)
            included.update(range(start, end))
        # Always include first 10 lines (imports) and last 5 lines
        included.update(range(min(10, len(file_lines))))
        included.update(range(max(0, len(file_lines) - 5), len(file_lines)))

        sorted_lines = sorted(included)
        truncated_parts: list[str] = []
        prev = -2
        for idx in sorted_lines:
            if idx != prev + 1:
                truncated_parts.append(f"  ... (lines {prev + 2}–{idx} omitted) ...")
            truncated_parts.append(f"{idx + 1:>5}| {file_lines[idx]}")
            prev = idx
        algo_display = "\n".join(truncated_parts)
    else:
        algo_display = "\n".join(
            f"{i + 1:>5}| {line}" for i, line in enumerate(file_lines)
        )

    # --- Staging file ---
    try:
        staging_content = load_file(staging_rel)
    except FileNotFoundError:
        staging_content = "(no staging file)"

    # --- Lib descriptions ---
    lib_desc = "\n".join(f"  - {path}: {desc}" for path, desc in LIB_FILE_DESCRIPTIONS)

    # --- Decision history ---
    _hist_window = RETRY_LIMITS.get("AGENT8_HISTORY_WINDOW", 8)
    if decision_history:
        history_lines = []
        _last_success_tick: int | None = None
        for entry in decision_history:
            if entry.get("outcome") == "success":
                _last_success_tick = entry["tick"]
        for entry in decision_history[-_hist_window:]:
            _eb = entry.get("errors_before", "")
            _ea = entry.get("errors_after", "")
            _delta = entry.get("sorry_delta", None)
            _sc = entry.get("sorry_count", "?")
            _sc_before = (int(_sc) - int(_delta)) if (_delta is not None and _sc != "?") else "?"
            _outcome = entry.get("outcome", "?")
            # Outcome tag
            if _outcome == "success":
                _outcome_tag = "[SUCCESS]"
            elif _outcome == "replan_done":
                _outcome_tag = "[REPLAN]"
            elif _eb and _ea and _eb[:120] == _ea[:120] and _delta == 0:
                _outcome_tag = "[NO-CHANGE]"
            elif _delta is not None and _delta < 0:
                _outcome_tag = "[PROGRESS]"
            else:
                _outcome_tag = "[FAIL]"
            history_lines.append(
                f"  tick {entry['tick']} {_outcome_tag}: action={entry['action']}, "
                f"target={entry.get('target_theorem', '?')}, "
                f"sorry={_sc_before}→{_sc} (delta {_delta if _delta is not None else '?'})"
            )
            if _eb:
                history_lines.append(f"    before: \"{_eb[:120]}\"")
            if _ea and _ea != _eb:
                history_lines.append(f"    after : \"{_ea[:120]}\"")
        if _last_success_tick is not None:
            history_lines.insert(
                0,
                f"  NOTE: Last [SUCCESS] was at tick {_last_success_tick} — "
                "do NOT undo work that built on it."
            )
        history_block = "\n".join(history_lines)
    else:
        history_block = "  (no previous decisions)"

    # Dynamically extract signatures of identifiers mentioned in the errors,
    # searching across project Lean files — works for any algorithm.
    dep_sigs = _prequery_dependency_signatures(errors_text, target_file, max_symbols=5)

    # Extract signatures of declarations imported by the target algorithm file.
    algo_sigs = _extract_imported_algo_sigs(target_file)

    _err_chars = RETRY_LIMITS.get("AGENT8_ERROR_CHARS", 3000)
    _staging_chars = RETRY_LIMITS.get("AGENT8_STAGING_CHARS", 2000)
    _plan_chars = RETRY_LIMITS.get("AGENT8_PLAN_CHARS", 3000)
    _a9_chars = RETRY_LIMITS.get("AGENT9_PLAN_CHARS", 3000)

    # Banner shown for one tick immediately after Agent9 re-planning.
    _new_plan_banner = ""
    if plan_updated_tick > 0:
        _new_plan_banner = (
            f"## [NEW PLAN FROM AGENT9 — updated at tick {plan_updated_tick}]\n"
            "The proof strategy was just revised by Agent9. "
            "Re-evaluate ALL open sorrys against the new plan before choosing an action. "
            "Do NOT repeat the action that triggered the replan.\n\n"
        )

    # Mid-check mode banner: reminds Agent8 it is a soft-gate check.
    _midcheck_banner = ""
    if midcheck_mode:
        _midcheck_banner = (
            f"## [MID-CHECK MODE — soft gate at Agent3 turn {midcheck_turns_elapsed}]\n"
            "You are performing a **periodic mid-proof check** inside the Agent3 per-sorry loop.\n"
            "Agent3 has been running for the last few turns.  Your job is to decide:\n"
            "  • If the errors are **tactical** (missing tactic, wrong lemma name, "
            "rewrite direction), return action=agent3_tactical so Agent3 continues with "
            "its remaining budget unchanged.\n"
            "  • If the errors indicate a **structural** problem (unknown identifier / "
            "interface mismatch / missing glue lemma / wrong strategy), escalate to the "
            "appropriate agent (agent7_signature, agent7_then_agent6, or agent2_replan).\n"
            "Avoid agent2_replan unless truly necessary — prefer agent7 or agent3_tactical.\n\n"
        )

    # Agent9 structured plan block (omitted when no plan is available).
    _a9_block = ""
    if agent9_plan:
        import json as _json
        try:
            _a9_text = _json.dumps(agent9_plan, indent=2, ensure_ascii=False)
        except Exception:
            _a9_text = str(agent9_plan)
        _a9_block = (
            f"## Agent9 Structured Plan\n"
            f"```json\n{_a9_text[:_a9_chars]}\n```\n\n"
        )

    return (
        f"{_midcheck_banner}"
        f"{_new_plan_banner}"
        "## Current Algorithm File (smart-truncated around error lines)\n"
        f"File: {target_file}\n"
        f"```lean\n{algo_display}\n```\n\n"
        f"## Build Errors\n```\n{errors_text[:_err_chars]}\n```\n\n"
        f"## Staging File ({staging_rel})\n```lean\n{staging_content[:_staging_chars]}\n```\n\n"
        f"## Proof Plan (current)\n{agent2_plan[:_plan_chars]}\n\n"
        f"## Library Files Available\n{lib_desc}\n\n"
        f"{_a9_block}"
        f"## Decision History (recent)\n{history_block}\n\n"
        f"{dep_sigs}"
        f"{algo_sigs}\n\n"
        "Analyze the errors and produce a single JSON decision following the "
        "priority rules in your system prompt."
    )


# ---------------------------------------------------------------------------
# JSON decision parser with retry logic
# ---------------------------------------------------------------------------

_VALID_ACTIONS = {
    "agent3_tactical",
    "agent7_signature",
    "agent7_then_agent6",
    "agent2_replan",
    "human_missing_assumption",
}


def _parse_agent8_decision(raw_reply: str) -> dict | None:
    """Parse Agent8's JSON decision.  Returns the dict or None on failure."""
    for candidate in _json_candidates(raw_reply.strip()):
        try:
            obj = json.loads(candidate)
        except json.JSONDecodeError:
            continue
        if isinstance(obj, dict) and obj.get("action") in _VALID_ACTIONS:
            return obj
    # Fallback: try the whole reply as JSON
    try:
        obj = json.loads(raw_reply.strip())
        if isinstance(obj, dict) and obj.get("action") in _VALID_ACTIONS:
            return obj
    except json.JSONDecodeError:
        pass
    return None


# ---------------------------------------------------------------------------
# Agent9 theorem-strategy context builder
# ---------------------------------------------------------------------------

def _build_agent9_theorem_context(
    agent9_plan: dict | None,
    target_theorem: str,
) -> str:
    """Return a formatted strategy block for *target_theorem* from the Agent9 plan.

    Used to enrich Agent3's dispatch prompt so it has theorem-specific guidance
    (proof strategy, key lemmas, dependencies) from Agent9's structured plan.
    Returns empty string when the plan is absent or the theorem is not found.
    """
    if not agent9_plan or not target_theorem:
        return ""
    for thm in agent9_plan.get("theorems", []):
        if thm.get("name") == target_theorem:
            lines = [
                f"\n\n## Agent9 Strategy for `{target_theorem}`",
                f"- proof_strategy: {thm.get('proof_strategy', 'N/A')}",
                f"- proof_technique: {thm.get('proof_technique', 'unknown')}",
                f"- key_lib_lemmas: {thm.get('key_lib_lemmas', [])}",
                f"- missing_glue_lemmas: {thm.get('missing_glue_lemmas', [])}",
                f"- dependency_map: {thm.get('dependency_map', {})}",
                f"- depends_on: {thm.get('dependencies', thm.get('depends_on', []))}",
                f"- difficulty: {thm.get('estimated_difficulty', thm.get('difficulty', 'unknown'))}",
            ]
            return "\n".join(lines) + "\n"
    return ""


# ---------------------------------------------------------------------------
# Dispatch: Agent3 tactical fix
# ---------------------------------------------------------------------------

def _agent8_run_agent3(
    target_file: str,
    staging_rel: str,
    agent2_plan: str,
    targeted_prompt: str,
    allowed_edit_lines: str | None,
    *,
    max_turns: int | None = None,
) -> dict:
    """Run a fresh Agent3 with a targeted prompt and simplified tool loop.

    Returns {"exit_code": int, "sorry_count": int, "errors": str}.
    """
    max_turns = max_turns or RETRY_LIMITS.get("AGENT8_AGENT3_MAX_TURNS", 15)

    agent3 = Agent("sorry_closer", extra_files=[target_file])
    registry = ToolRegistry()
    registry.register_default_tools()
    algo_name = Path(target_file).stem
    from orchestrator.tools import write_staging_lemma
    registry.register(
        "write_staging_lemma",
        functools.partial(write_staging_lemma, target_algo=algo_name),
    )

    # Write full Agent2 plan to a temp file so Agent3 can read it without truncation
    plan_file = Path(tempfile.gettempdir()) / f"agent8_plan_{algo_name}.md"
    plan_file.write_text(agent2_plan, encoding="utf-8")

    scope_instruction = ""
    if allowed_edit_lines:
        scope_instruction = (
            f"\n\nSCOPE CONSTRAINT: You may ONLY edit lines {allowed_edit_lines} "
            "of the target file. Do not modify code outside this range."
        )

    try:
        _staging_snippet = load_file(staging_rel)[
            : RETRY_LIMITS.get("AGENT8_STAGING_CHARS", 2000)
        ]
    except FileNotFoundError:
        _staging_snippet = "(no staging file)"

    initial_msg = (
        f"[AGENT8 DISPATCH — Tactical Fix]\n\n"
        f"{targeted_prompt}\n\n"
        f"The full proof plan is available at: {plan_file}\n"
        f"(Read it with read_file if you need the complete mathematical strategy.)\n"
        f"Target file: {target_file}\n"
        f"Staging file: {staging_rel}\n\n"
        f"## Current Staging File\n```lean\n{_staging_snippet}\n```\n"
        f"{scope_instruction}\n\n"
        "Fix the specified error. When done, signal tool=done. "
        "Output ONE JSON action per response: {{thought, tool, arguments}}."
    )

    raw_reply = agent3.call(initial_msg)

    for turn in range(max_turns):
        try:
            payload = json.loads(raw_reply)
        except json.JSONDecodeError:
            raw_reply = agent3.call(
                "Invalid JSON. Return valid JSON: {thought, tool, arguments}."
            )
            continue
        if not isinstance(payload, dict):
            raw_reply = agent3.call("JSON must be an object. Retry.")
            continue

        tool_name = str(payload.get("tool", ""))
        arguments = payload.get("arguments", {}) or {}

        if tool_name == "done":
            verify = registry.call("run_lean_verify", target_file)
            exit_code = int(verify.get("exit_code", 1))
            sorry_count = int(verify.get("sorry_count", -1))
            if exit_code == 0 and sorry_count == 0:
                return {
                    "exit_code": exit_code,
                    "sorry_count": sorry_count,
                    "errors": "",
                }
            # Reject done if not clean
            raw_reply = agent3.call(
                f"## done rejected — build not clean\n"
                f"exit={exit_code}, sorry={sorry_count}\n"
                f"```\n{verify.get('errors', [])}\n```\n"
                "Fix the remaining errors, then signal done again."
            )
            continue

        # Block routing tools — Agent8 owns routing
        if tool_name in (
            "request_agent2_help", "request_agent6_glue",
            "request_agent7_interface_audit",
        ):
            raw_reply = agent3.call(
                f"Tool `{tool_name}` is not available in Agent8 dispatch mode. "
                "Agent8 handles routing. Focus on the tactical fix described in "
                "your instructions."
            )
            continue

        # Execute tool
        args = dict(arguments)
        # Normalize path/file_path
        if "path" in args and "file_path" not in args:
            for k in ("get_lean_goal", "check_lean_have", "run_lean_verify"):
                if tool_name == k:
                    args["file_path"] = args.pop("path")
                    break

        try:
            result = registry.call(tool_name, **args)
        except KeyError:
            raw_reply = agent3.call(
                f"Unknown tool `{tool_name}`. Available: "
                "read_file, search_codebase, search_in_file, edit_file_patch, "
                "write_new_file, run_lean_verify, get_lean_goal, check_lean_have."
            )
            continue
        except Exception as exc:
            raw_reply = agent3.call(f"Tool error: {exc}")
            continue

        if isinstance(result, dict):
            result_text = json.dumps(result, indent=2, ensure_ascii=False)
        else:
            result_text = str(result)
        raw_reply = agent3.call(f"## {tool_name} result\n```\n{result_text}\n```\n")

    # Turns exhausted — verify final state
    final = registry.call("run_lean_verify", target_file)
    return {
        "exit_code": int(final.get("exit_code", 1)),
        "sorry_count": int(final.get("sorry_count", -1)),
        "errors": str(final.get("errors", "")),
    }


# ---------------------------------------------------------------------------
# Dispatch: Agent7 signature check/fix
# ---------------------------------------------------------------------------

def _agent8_run_agent7(
    target_file: str,
    errors_text: str,
    agent7_targeted_prompt: str,
) -> tuple[dict | None, str]:
    """Run a fresh Agent7 for signature diagnosis.

    Returns (agent7_plan_or_None, raw_reply).
    """
    agent7 = Agent("interface_auditor", extra_files=[target_file])
    agent7_registry = ToolRegistry()
    agent7_registry.register_readonly_tools()

    error_line = _extract_first_error_line(errors_text)
    snippet = _build_escalation_file_context(target_file, error_line)
    dep_sigs = _prequery_dependency_signatures(errors_text, target_file)

    prompt = (
        "Produce a strict interface-audit protocol JSON for Agent3.\n"
        f"Target file: {target_file}\n"
        "[Agent8 Decision Hub dispatch — signature diagnosis]\n\n"
        f"Agent8 diagnosis:\n{agent7_targeted_prompt[:RETRY_LIMITS.get('AGENT8_A7_PROMPT_CHARS', 1500)]}\n\n"
        f"Latest build errors:\n```\n{errors_text[:2000]}\n```\n\n"
        f"Current file snippet:\n```lean\n{snippet[:8000]}\n```\n\n"
        f"Dependency signatures:\n```lean\n{dep_sigs[:4000]}\n```\n\n"
        "Return strict JSON only as specified in your system prompt."
    )

    plan, raw = _call_agent7_with_tools(agent7, agent7_registry, prompt)
    return plan, raw


# ---------------------------------------------------------------------------
# Dispatch: Agent7 → Agent6 (signature check then bridge lemma)
# ---------------------------------------------------------------------------

def _agent8_run_agent7_then_agent6(
    target_file: str,
    staging_rel: str,
    errors_text: str,
    agent7_targeted_prompt: str,
    agent6_targeted_prompt: str,
) -> dict:
    """Run Agent7 for signature check, then Agent6 to prove the bridge lemma.

    Returns {"exit_code": int, "sorry_count": int, "errors": str}.
    """
    # Phase 1: Agent7 signature audit
    a7_plan, _a7_raw = _agent8_run_agent7(
        target_file, errors_text, agent7_targeted_prompt
    )

    if a7_plan:
        console.print(
            f"  [Agent8→Agent7] Root cause: {a7_plan.get('root_cause', '?')}"
        )
        # Execute direct_apply steps from Agent7 protocol
        exec_registry = ToolRegistry()
        exec_registry.register_default_tools()
        for step in a7_plan.get("ordered_steps", []):
            if step.get("direct_apply") and step.get("tool") == "edit_file_patch":
                req_args = step.get("required_args", {})
                if req_args.get("old_str") and req_args.get("new_str"):
                    try:
                        exec_registry.call(
                            "edit_file_patch",
                            path=req_args.get("path", target_file),
                            old_str=req_args["old_str"],
                            new_str=req_args["new_str"],
                        )
                    except Exception:
                        pass

    # Phase 2: Agent6 glue lemma proof
    staging_path = PROJECT_ROOT / staging_rel
    algo_name = Path(target_file).stem
    agent6 = Agent("glue_filler", extra_files=[target_file])
    agent6_registry = ToolRegistry()
    agent6_registry.register_staging_tools(target_algo=algo_name)
    from orchestrator.tools import check_lean_have, get_lean_goal
    agent6_registry.register("get_lean_goal", get_lean_goal)
    agent6_registry.register("check_lean_have", check_lean_have)

    success, msg = _run_agent6_glue_loop(
        agent6,
        agent6_registry,
        target_file,
        staging_path,
        staging_rel,
        goal=agent6_targeted_prompt,
        error_message=errors_text[:500],
        diagnosis=agent6_targeted_prompt,
        target_algo=algo_name,
    )

    # Verify final state
    from orchestrator.tools import run_lean_verify
    final = run_lean_verify(target_file)
    return {
        "exit_code": int(final.get("exit_code", 1)),
        "sorry_count": int(final.get("sorry_count", -1)),
        "errors": str(final.get("errors", "")),
    }


# ---------------------------------------------------------------------------
# Dispatch: Agent2 replan
# ---------------------------------------------------------------------------

def _agent8_run_agent2_replan(
    agent2: Agent,
    target_file: str,
    errors_text: str,
    current_plan: str,
) -> str:
    """Clear Agent2 context and request a revised proof strategy.

    Returns the new plan text.
    """
    agent2.messages.clear()

    try:
        current_file = load_file(target_file)
    except FileNotFoundError:
        current_file = "(file does not exist)"

    replan_prompt = (
        "[AGENT8 — STRATEGY REVISION REQUEST]\n\n"
        "The current proof strategy has failed after all retry attempts. "
        "Please revise the proof plan based on the errors below.\n\n"
        f"## Current Plan\n{current_plan[:RETRY_LIMITS.get('AGENT8_A2_PLAN_CHARS', 4000)]}\n\n"
        f"## Current Errors\n```\n{errors_text[:RETRY_LIMITS.get('AGENT8_A2_ERROR_CHARS', 2000)]}\n```\n\n"
        f"## Current File Content\n```lean\n{current_file[:RETRY_LIMITS.get('AGENT8_A2_FILE_CHARS', 6000)]}\n```\n\n"
        "Revise the proof strategy. You may:\n"
        "- Decompose sub-goals differently\n"
        "- Add new intermediate lemmas\n"
        "- Change the proof approach (different Mathlib lemmas, different tactic family)\n"
        "- Adjust the proof order\n\n"
        "CONSTRAINT: Do NOT modify parts of the proof that are already correct "
        "(lines that compile without errors). Focus on the failing sections.\n\n"
        "Provide revised guidance with PATCH blocks as usual."
    )

    staging_registry = ToolRegistry()
    staging_registry.register_staging_tools(target_algo=Path(target_file).stem)
    new_plan, _ = _call_agent2_with_tools(agent2, staging_registry, replan_prompt)
    return new_plan


# ---------------------------------------------------------------------------
# Debug logger
# ---------------------------------------------------------------------------

def _debug_log(
    algo_name: str, tick: int, decision: dict, outcome: dict, **extra: Any
) -> None:
    """Write per-tick debug info to the audit directory."""
    if not AGENT8_DEBUG:
        return
    debug_dir = AUDIT_DIR / "agent8_debug"
    debug_dir.mkdir(parents=True, exist_ok=True)
    log_path = debug_dir / f"{algo_name}_ticks.jsonl"
    entry = {
        "tick": tick,
        "timestamp": time.time(),
        "decision": decision,
        "outcome": outcome,
        **extra,
    }
    with open(log_path, "a", encoding="utf-8") as f:
        f.write(json.dumps(entry, ensure_ascii=False) + "\n")


# ---------------------------------------------------------------------------
# Behavior-driven anti-loop check
# ---------------------------------------------------------------------------

def _check_anti_loop(
    decision: dict,
    decision_history: list[dict],
) -> tuple[str, str]:
    """Decide whether the proposed action should be overridden to break a loop.

    Returns ``(action, override_reason)``.  When no override is needed,
    ``override_reason`` is empty and ``action`` equals ``decision["action"]``.

    Logic (evaluated in priority order):
    1. **Zero-progress repeat** — the same action was used in the last N
       history entries, all of which had ``sorry_delta == 0`` AND
       ``errors_after[:120] == errors_before[:120]``.  Escalate to
       ``agent2_replan`` (or ``human_missing_assumption`` if the proposed
       action is already ``agent2_replan``).
    2. **Error frozen across all recent actions** — the last 3 history entries
       (regardless of action) all share the same ``errors_after[:120]``.
       Escalate to ``human_missing_assumption``.
    3. **Classic heuristic fallback** — ``(action, error_sig[:LEN])`` pair
       repeated too many times (uses ``AGENT8_ERROR_SIG_FULL_LEN`` instead of
       the old 40-char truncation).
    """
    _no_progress_n = RETRY_LIMITS.get("AGENT8_NO_PROGRESS_ESCALATE_AFTER", 2)
    _sig_len = RETRY_LIMITS.get("AGENT8_ERROR_SIG_FULL_LEN", 120)
    proposed_action = decision.get("action", "agent3_tactical")
    error_sig = decision.get("error_signature", "")
    _escapable = proposed_action not in ("agent2_replan", "human_missing_assumption")

    if not decision_history:
        return proposed_action, ""

    # --- Condition 1: zero-progress repeat for the same action ---
    _same_action_entries = [
        e for e in decision_history if e.get("action") == proposed_action
    ]
    if len(_same_action_entries) >= _no_progress_n:
        _last_n = _same_action_entries[-_no_progress_n:]
        _all_no_progress = all(
            e.get("sorry_delta", None) == 0
            and e.get("errors_before", "")[:120] == e.get("errors_after", "")[:120]
            for e in _last_n
        )
        if _all_no_progress:
            _reason = (
                f"action '{proposed_action}' made zero progress in last "
                f"{_no_progress_n} attempts (errors unchanged, sorry_delta=0)"
            )
            if proposed_action == "agent2_replan":
                return "human_missing_assumption", _reason
            return "agent2_replan", _reason

    # --- Condition 2: error frozen across all recent actions ---
    if len(decision_history) >= 3:
        _last3 = decision_history[-3:]
        _ea_signatures = [e.get("errors_after", "")[:120] for e in _last3]
        # Also require sorry_delta == 0 for all entries: when exit_code==0 but sorrys
        # remain, errors is an empty list ("[]"), making all ea_signatures identical
        # even while progress is made (sorrys decreasing). Without this guard we'd
        # fire human_missing_assumption on a normally-progressing sequence.
        _all_sorry_frozen = all(e.get("sorry_delta", None) == 0 for e in _last3)
        if _ea_signatures[0] and len(set(_ea_signatures)) == 1 and _all_sorry_frozen:
            _reason = (
                f"errors and sorry both unchanged across last 3 ticks: "
                f"\"{_ea_signatures[0][:60]}\""
            )
            return "human_missing_assumption", _reason

    # --- Condition 3: classic (action, error_sig) pair heuristic (extended sig) ---
    if _escapable and decision_history:
        _sig_key = error_sig[:_sig_len]
        _pair_repeats = sum(
            1
            for e in decision_history
            if e.get("action") == proposed_action
            and e.get("error_signature", "")[:_sig_len] == _sig_key
        )
        if _pair_repeats >= 2:
            _reason = (
                f"(action='{proposed_action}', error_sig='{_sig_key[:60]}') "
                f"repeated {_pair_repeats + 1}× in history"
            )
            return "agent2_replan", _reason

    return proposed_action, ""


# ---------------------------------------------------------------------------
# Main state-machine loop
# ---------------------------------------------------------------------------

def run_agent8_loop(
    agent2: Agent,
    target_file: str,
    staging_rel: str,
    agent2_plan: str,
    last_errors: str,
    *,
    best_checkpoint: dict | None = None,
    agent9_plan: dict | None = None,
) -> tuple[bool, str, str]:
    """Run the Agent8 decision hub loop.

    Returns (success, updated_plan, last_errors).
    - success=True if the file compiles with exit=0 and sorry=0.
    - success=False if Agent8 exhausts its steps or hits human gate.
    """
    algo_name = Path(target_file).stem
    max_steps = RETRY_LIMITS.get("AGENT8_MAX_STEPS", 8)
    decision_history: list[dict] = []
    current_plan = agent2_plan
    current_errors = last_errors
    _consecutive_parse_failures = 0
    _consecutive_same_error: int = 0
    _last_error_sig: str = ""

    # Running sorry count — updated after every dispatch so we can compute
    # per-tick deltas and record them in decision_history.
    # Seed from best_checkpoint if available (most recent known sorry count before
    # Agent8 started), so the first-tick delta is meaningful rather than -(999 - N).
    _current_sorry_count: int = (
        int(best_checkpoint.get("sorry_count", 999))
        if best_checkpoint
        else 999
    )

    console.rule("[bold magenta]Agent8 Decision Hub — Error Recovery")
    console.print(
        f"  Target: {target_file} | Max steps: {max_steps} | "
        f"Debug: {AGENT8_DEBUG}"
    )

    # (legacy per-tick counters kept for the _consecutive_same_error hard-trigger below)

    # Tracks the tick at which the Agent9 plan was most recently updated, so
    # _build_agent8_tick_context can prepend a "NEW PLAN" banner on the following tick.
    _plan_updated_tick: int = 0

    for tick in range(1, max_steps + 1):
        console.print(f"\n[magenta]--- Agent8 Tick {tick}/{max_steps} ---")

        # 0. Fresh verify — always rebuild errors from the current file state
        # so that smart-truncation line numbers match the actual file content.
        from orchestrator.tools import run_lean_verify as _tick_verify
        _fresh = _tick_verify(target_file)
        _fresh_errors = str(_fresh.get("errors", ""))
        _fresh_sorry = int(_fresh.get("sorry_count", _current_sorry_count))
        # Override stale errors only when the fresh build produced hard errors,
        # or when current_errors is empty (nothing meaningful to preserve).
        if _fresh_errors.strip() or not current_errors.strip():
            current_errors = _fresh_errors
        _current_sorry_count = _fresh_sorry
        console.print(
            f"  [Agent8] Fresh verify: exit={_fresh.get('exit_code', '?')}, "
            f"sorry={_fresh_sorry}"
        )

        # 1. Build context
        ctx = _build_agent8_tick_context(
            target_file, current_errors, current_plan, decision_history, staging_rel,
            agent9_plan=agent9_plan,
            plan_updated_tick=_plan_updated_tick,
        )

        # 2. Call Agent8 with optional investigation rounds
        agent8 = Agent("decision_hub")
        _inv_registry = ToolRegistry()
        _inv_registry.register_investigation_tools()
        _max_inv = RETRY_LIMITS.get("AGENT8_INVESTIGATION_TURNS", 3)
        _investigation_rounds_this_tick = 0
        raw_reply = agent8.call(ctx)

        for _inv_round in range(_max_inv):
            try:
                _inv_payload = json.loads(raw_reply)
            except (json.JSONDecodeError, ValueError):
                break
            if not (
                isinstance(_inv_payload, dict)
                and _inv_payload.get("type") == "lookup"
                and isinstance(_inv_payload.get("tool_calls"), list)
                and len(_inv_payload["tool_calls"]) > 0
            ):
                break
            _inv_results: list[dict] = []
            for _tc in _inv_payload["tool_calls"]:
                _tn = _tc.get("tool", "")
                _ta = _tc.get("arguments", {}) or {}
                try:
                    _tr = _inv_registry.call(_tn, **_ta)
                except Exception as _exc:
                    _tr = {"error": str(_exc)}
                _inv_results.append({"tool": _tn, "result": _tr})
            _investigation_rounds_this_tick += 1
            raw_reply = agent8.call(
                "Investigation results:\n"
                + json.dumps(_inv_results, indent=2, ensure_ascii=False)
                + "\n\nNow output your final JSON decision."
            )

        # 3. Parse decision (with retry)
        decision = _parse_agent8_decision(raw_reply)
        if decision is None:
            _consecutive_parse_failures += 1
            console.print(
                f"  [Agent8] JSON parse failed ({_consecutive_parse_failures}/3). "
                "Retrying..."
            )
            if _consecutive_parse_failures >= 3:
                console.print(
                    "[yellow][Agent8] 3 consecutive parse failures — "
                    "defaulting to agent2_replan"
                )
                decision = {
                    "action": "agent2_replan",
                    "priority_level": "P2",
                    "reason": "Agent8 JSON parse failures — falling back to replan",
                    "targeted_prompt": "Revise the proof strategy.",
                    "error_signature": _extract_error_signature(current_errors),
                }
            else:
                # Retry with explicit instruction
                raw_reply = agent8.call(
                    "Your response was not valid JSON. Return ONLY a single JSON "
                    "object with the required fields: action, priority_level, reason, "
                    "targeted_prompt, error_signature. No markdown fences."
                )
                decision = _parse_agent8_decision(raw_reply)
                if decision is None:
                    continue
        _consecutive_parse_failures = 0

        action = decision.get("action", "agent3_tactical")
        error_sig = decision.get(
            "error_signature", _extract_error_signature(current_errors)
        )
        targeted_prompt = decision.get("targeted_prompt", "")

        console.print(
            f"  [Agent8] Decision: {action} "
            f"(P={decision.get('priority_level', '?')}) "
            f"| error_sig=\"{error_sig[:60]}\""
        )
        console.print(f"  [Agent8] Reason: {decision.get('reason', '?')}")

        # 4. Anti-loop check (behavior-driven, replaces old heuristic pair counters).
        action, _antiloop_reason = _check_anti_loop(decision, decision_history)
        if _antiloop_reason:
            console.print(f"  [AntiLoop] {action} ← {_antiloop_reason}")
            decision["action"] = action
            targeted_prompt = (
                f"[FORCED by anti-loop: {_antiloop_reason}] " + targeted_prompt
            )

        # Hard trigger: same error_signature too many consecutive ticks → human gate.
        # Kept as a final safety net on top of _check_anti_loop.
        if error_sig and error_sig == _last_error_sig:
            _consecutive_same_error += 1
        else:
            _consecutive_same_error = 1
            _last_error_sig = error_sig

        if _consecutive_same_error >= AGENT8_HUMAN_GATE_CONSECUTIVE_THRESHOLD:
            if action != "human_missing_assumption":
                console.print(
                    f"  [Agent8] HARD TRIGGER: same error {_consecutive_same_error}× "
                    "→ forcing human_missing_assumption"
                )
                action = "human_missing_assumption"
                decision["action"] = action

        # 5. Dispatch — capture state BEFORE action for delta computation.
        _errors_before: str = current_errors[:300]
        _sorry_before: int = _current_sorry_count
        outcome: dict = {"outcome": "unknown"}

        try:
            if action == "agent3_tactical":
                console.print("  [Agent8→Agent3] Dispatching tactical fix...")
                _a9_thm_ctx = _build_agent9_theorem_context(
                    agent9_plan, decision.get("target_theorem", "")
                )
                result = _agent8_run_agent3(
                    target_file,
                    staging_rel,
                    current_plan,
                    targeted_prompt + _a9_thm_ctx,
                    decision.get("allowed_edit_lines"),
                )
                outcome = {
                    "outcome": "success" if result["exit_code"] == 0 and result["sorry_count"] == 0 else "failed",
                    "exit_code": result["exit_code"],
                    "sorry_count": result["sorry_count"],
                }
                current_errors = result.get("errors", current_errors)

            elif action == "agent7_signature":
                console.print("  [Agent8→Agent7] Dispatching signature audit...")
                a7_prompt = decision.get("agent7_targeted_prompt", targeted_prompt)
                a7_plan, _a7_raw = _agent8_run_agent7(
                    target_file, current_errors, a7_prompt
                )
                # Execute direct_apply steps
                if a7_plan:
                    exec_registry = ToolRegistry()
                    exec_registry.register_default_tools()
                    for step in a7_plan.get("ordered_steps", []):
                        if step.get("direct_apply") and step.get("tool") == "edit_file_patch":
                            req = step.get("required_args", {})
                            if req.get("old_str") and req.get("new_str"):
                                try:
                                    exec_registry.call(
                                        "edit_file_patch",
                                        path=req.get("path", target_file),
                                        old_str=req["old_str"],
                                        new_str=req["new_str"],
                                    )
                                except Exception:
                                    pass

                from orchestrator.tools import run_lean_verify
                verify = run_lean_verify(target_file)
                outcome = {
                    "outcome": "success" if int(verify.get("exit_code", 1)) == 0 and int(verify.get("sorry_count", -1)) == 0 else "failed",
                    "exit_code": int(verify.get("exit_code", 1)),
                    "sorry_count": int(verify.get("sorry_count", -1)),
                }
                current_errors = str(verify.get("errors", current_errors))

            elif action == "agent7_then_agent6":
                console.print("  [Agent8→Agent7→Agent6] Dispatching signature + glue...")
                a7_prompt = decision.get("agent7_targeted_prompt", targeted_prompt)
                a6_prompt = decision.get("agent6_targeted_prompt", targeted_prompt)
                result = _agent8_run_agent7_then_agent6(
                    target_file, staging_rel, current_errors, a7_prompt, a6_prompt
                )
                outcome = {
                    "outcome": "success" if result["exit_code"] == 0 and result["sorry_count"] == 0 else "failed",
                    "exit_code": result["exit_code"],
                    "sorry_count": result["sorry_count"],
                }
                current_errors = result.get("errors", current_errors)

            elif action == "agent2_replan":
                console.print("  [Agent8→Agent9] Dispatching strategy re-planning via Agent9...")
                from orchestrator.phase3a_agent9 import run_agent9_replan as _run_a9_replan
                _new_plan = _run_a9_replan(
                    target_file,
                    current_errors,
                    agent9_plan or {},
                    algo_name,
                    current_plan,
                )
                if _new_plan:
                    agent9_plan = _new_plan
                    current_plan = json.dumps(_new_plan, indent=2, ensure_ascii=False)
                    _plan_updated_tick = tick
                    console.print(
                        "  [Agent8→Agent9] Re-plan succeeded. "
                        "Agent8 retains control for next tick."
                    )
                else:
                    console.print(
                        "  [Agent8→Agent9] Re-plan failed — falling back to Agent2."
                    )
                    current_plan = _agent8_run_agent2_replan(
                        agent2, target_file, current_errors, current_plan
                    )
                # Run a fresh verify to capture current state.
                # No Agent3 dispatch — Agent8 decides the next action on the next tick.
                from orchestrator.tools import run_lean_verify as _rlv
                _replan_verify = _rlv(target_file)
                outcome = {
                    "outcome": "replan_done",
                    "exit_code": int(_replan_verify.get("exit_code", 1)),
                    "sorry_count": int(
                        _replan_verify.get("sorry_count", _current_sorry_count)
                    ),
                }
                current_errors = str(_replan_verify.get("errors", current_errors))

            elif action == "human_missing_assumption":
                console.print(
                    Panel(
                        f"Agent8 requests human intervention.\n\n"
                        f"Diagnosis:\n{targeted_prompt}\n\n"
                        f"Error signature: {error_sig}\n"
                        f"Decision history: {len(decision_history)} ticks",
                        title="[red bold]Agent8 — Human Gate",
                    )
                )
                outcome = {"outcome": "human_gate"}
                decision_history.append({
                    "tick": tick,
                    "action": action,
                    "target_theorem": decision.get("target_theorem"),
                    "error_signature": error_sig,
                    "errors_before": _errors_before,
                    "errors_after": _errors_before,  # no dispatch happened
                    "sorry_delta": 0,
                    **outcome,
                })
                _debug_log(
                    algo_name, tick, decision, outcome,
                    ctx_char_len=len(ctx),
                    first_error_line=_extract_first_error_line(current_errors),
                    error_sig=error_sig,
                    investigation_rounds=_investigation_rounds_this_tick,
                    dispatch_prompt_len=len(targeted_prompt),
                )
                return False, current_plan, current_errors

        except Exception as exc:
            console.print(f"  [Agent8] Dispatch error: {exc}")
            outcome = {"outcome": "dispatch_error", "error": str(exc)}

        # Update running sorry count from outcome (keep previous on dispatch_error).
        _current_sorry_count = int(outcome.get("sorry_count", _current_sorry_count))
        _errors_after: str = current_errors[:300]
        _sorry_delta: int = _current_sorry_count - _sorry_before

        # 6. Record decision
        decision_history.append({
            "tick": tick,
            "action": action,
            "target_theorem": decision.get("target_theorem"),
            "error_signature": error_sig,
            "errors_before": _errors_before,
            "errors_after": _errors_after,
            "sorry_delta": _sorry_delta,
            **outcome,
        })
        _debug_log(
            algo_name, tick, decision, outcome,
            ctx_char_len=len(ctx),
            first_error_line=_extract_first_error_line(current_errors),
            error_sig=error_sig,
            investigation_rounds=_investigation_rounds_this_tick,
            dispatch_prompt_len=len(targeted_prompt),
        )

        # 7. Check success
        if outcome.get("outcome") == "success":
            # Double-check with run_lean_verify
            from orchestrator.tools import run_lean_verify, run_repo_verify
            verify = run_lean_verify(target_file)
            exit_code = int(verify.get("exit_code", 1))
            sorry_count = int(verify.get("sorry_count", -1))
            if exit_code == 0 and sorry_count == 0:
                console.print(
                    f"[green bold][Agent8] Success at tick {tick}! "
                    "Build clean, 0 sorry."
                )
                return True, current_plan, ""
            # Not actually clean — update errors and continue
            current_errors = str(verify.get("errors", current_errors))
            console.print(
                f"  [Agent8] Reported success but verify shows "
                f"exit={exit_code}, sorry={sorry_count}. Continuing..."
            )

        console.print(
            f"  [Agent8] Tick {tick} result: {outcome.get('outcome', '?')} "
            f"(exit={outcome.get('exit_code', '?')}, "
            f"sorry={outcome.get('sorry_count', '?')})"
        )

    console.print(
        f"[yellow][Agent8] Exhausted {max_steps} steps without success."
    )
    return False, current_plan, current_errors


# ---------------------------------------------------------------------------
# Mid-check entry point (soft gate)
# ---------------------------------------------------------------------------

def run_agent8_midcheck(
    target_file: str,
    staging_rel: str,
    current_plan: str,
    current_errors: str,
    *,
    agent2: "Agent | None" = None,
    agent9_plan: dict | None = None,
    decision_history: list[dict] | None = None,
    turns_elapsed: int = 0,
) -> dict:
    """Make a single Agent8 routing decision during the Agent3 per-sorry loop.

    This is the "soft gate" mid-check: it does NOT dispatch any agents itself.
    It returns a decision dict so the caller (main.py) can choose whether to
    let Agent3 continue or hand off to the appropriate specialized agent.

    Returns a dict with at least:
        {
            "action":          str,   # agent3_tactical | agent7_signature |
                                      # agent7_then_agent6 | agent2_replan |
                                      # human_missing_assumption
            "reason":          str,
            "targeted_prompt": str,
            "error_signature": str,
            "priority_level":  str,
        }
    On any failure (parse errors, exceptions) falls back to action=agent3_tactical
    so the caller can safely continue.
    """
    algo_name = Path(target_file).stem
    _decision_history: list[dict] = decision_history or []

    console.print(
        f"\n[bold magenta][Agent8 MidCheck] Soft-gate at turn {turns_elapsed} "
        f"for {algo_name}"
    )

    # Build context — reuse existing helper, no plan-update banner needed here.
    ctx = _build_agent8_tick_context(
        target_file,
        current_errors,
        current_plan,
        _decision_history,
        staging_rel,
        agent9_plan=agent9_plan,
        plan_updated_tick=0,
        midcheck_mode=True,
        midcheck_turns_elapsed=turns_elapsed,
    )

    # Call Agent8 (single round, reduced investigation budget for speed).
    agent8 = Agent("decision_hub")
    _inv_registry = ToolRegistry()
    _inv_registry.register_investigation_tools()
    _max_inv = min(RETRY_LIMITS.get("AGENT8_INVESTIGATION_TURNS", 3), 2)
    raw_reply = agent8.call(ctx)

    for _inv_round in range(_max_inv):
        try:
            _inv_payload = json.loads(raw_reply)
        except (json.JSONDecodeError, ValueError):
            break
        if not (
            isinstance(_inv_payload, dict)
            and _inv_payload.get("type") == "lookup"
            and isinstance(_inv_payload.get("tool_calls"), list)
            and len(_inv_payload["tool_calls"]) > 0
        ):
            break
        _inv_results: list[dict] = []
        for _tc in _inv_payload["tool_calls"]:
            _tn = _tc.get("tool", "")
            _ta = _tc.get("arguments", {}) or {}
            try:
                _tr = _inv_registry.call(_tn, **_ta)
            except Exception as _exc:
                _tr = {"error": str(_exc)}
            _inv_results.append({"tool": _tn, "result": _tr})
        raw_reply = agent8.call(
            "Investigation results:\n"
            + json.dumps(_inv_results, indent=2, ensure_ascii=False)
            + "\n\nNow output your final JSON decision."
        )

    # Parse with one retry attempt before falling back.
    decision = _parse_agent8_decision(raw_reply)
    if decision is None:
        # One explicit retry.
        raw_reply = agent8.call(
            "Your response was not valid JSON. Return ONLY a single JSON "
            "object with the required fields: action, priority_level, reason, "
            "targeted_prompt, error_signature. No markdown fences."
        )
        decision = _parse_agent8_decision(raw_reply)

    if decision is None:
        console.print(
            "[yellow][Agent8 MidCheck] Parse failed — defaulting to agent3_tactical"
        )
        return {
            "action": "agent3_tactical",
            "reason": "Mid-check parse failure — letting Agent3 continue",
            "targeted_prompt": "",
            "error_signature": _extract_error_signature(current_errors),
            "priority_level": "P3",
        }

    # Anti-loop check using the shared history.
    action, _antiloop_reason = _check_anti_loop(decision, _decision_history)
    if _antiloop_reason:
        console.print(f"  [AntiLoop/MidCheck] {action} ← {_antiloop_reason}")
        decision["action"] = action

    console.print(
        f"  [Agent8 MidCheck] Decision: {decision.get('action')} "
        f"(P={decision.get('priority_level', '?')}) "
        f"| reason=\"{decision.get('reason', '')[:80]}\""
    )

    return decision
