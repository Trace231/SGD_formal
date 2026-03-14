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
    RETRY_LIMITS,
)
from orchestrator.context_builders import (
    _build_escalation_file_context,
    _prequery_dependency_signatures,
)
from orchestrator.error_classifier import _extract_first_error_line, _json_candidates
from orchestrator.file_io import load_file, snapshot_file

console = Console()

# ---------------------------------------------------------------------------
# Lib file descriptions — compact summary for Agent8 context
# ---------------------------------------------------------------------------

LIB_FILE_DESCRIPTIONS: list[tuple[str, str]] = [
    ("Lib/Glue/Probability.lean",
     "Probability/integral tools: probReal_univ, integral_const, IsProbabilityMeasure, HasBoundedVariance"),
    ("Lib/Glue/Algebra.lean",
     "Norm-squared expansion, gradient step inner-product algebra"),
    ("Lib/Glue/Measurable.lean",
     "Measurability and integrable composite helpers"),
    ("Lib/Glue/Calculus.lean",
     "Hilbert space FTC, segment integration"),
    ("Lib/Layer0/ConvexFOC.lean",
     "Convex/strongly-convex first-order conditions"),
    ("Lib/Layer0/GradientFTC.lean",
     "L-smooth gradient quadratic bound"),
    ("Lib/Layer0/IndepExpect.lean",
     "Expectation/independence: expectation_inner_gradL_eq, expectation_norm_sq_gradL_bound"),
    ("Lib/Layer1/StochasticDescent.lean",
     "StochasticDescentHyps structure and convergence theorems"),
]


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
    if decision_history:
        history_lines = []
        for entry in decision_history[-8:]:
            history_lines.append(
                f"  tick {entry['tick']}: action={entry['action']}, "
                f"target={entry.get('target_theorem', '?')}, "
                f"error_sig=\"{entry.get('error_signature', '?')}\", "
                f"result={entry.get('outcome', '?')}, "
                f"exit={entry.get('exit_code', '?')}, sorry={entry.get('sorry_count', '?')}"
            )
        history_block = "\n".join(history_lines)
    else:
        history_block = "  (no previous decisions)"

    # Dynamically extract signatures of identifiers mentioned in the errors,
    # searching across project Lean files — works for any algorithm.
    dep_sigs = _prequery_dependency_signatures(errors_text, target_file, max_symbols=5)

    return (
        "## Current Algorithm File (smart-truncated around error lines)\n"
        f"File: {target_file}\n"
        f"```lean\n{algo_display}\n```\n\n"
        f"## Build Errors\n```\n{errors_text[:3000]}\n```\n\n"
        f"## Staging File ({staging_rel})\n```lean\n{staging_content[:2000]}\n```\n\n"
        f"## Agent2 Proof Plan (current)\n{agent2_plan[:3000]}\n\n"
        f"## Library Files Available\n{lib_desc}\n\n"
        f"## Decision History (recent)\n{history_block}\n\n"
        f"{dep_sigs}"
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

    initial_msg = (
        f"[AGENT8 DISPATCH — Tactical Fix]\n\n"
        f"{targeted_prompt}\n\n"
        f"The full proof plan is available at: {plan_file}\n"
        f"(Read it with read_file if you need the complete mathematical strategy.)\n"
        f"Target file: {target_file}\n"
        f"Staging file: {staging_rel}"
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
        f"Agent8 diagnosis:\n{agent7_targeted_prompt[:1500]}\n\n"
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
        f"## Current Plan\n{current_plan[:4000]}\n\n"
        f"## Current Errors\n```\n{errors_text[:2000]}\n```\n\n"
        f"## Current File Content\n```lean\n{current_file[:6000]}\n```\n\n"
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

def _debug_log(algo_name: str, tick: int, decision: dict, outcome: dict) -> None:
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
    }
    with open(log_path, "a", encoding="utf-8") as f:
        f.write(json.dumps(entry, ensure_ascii=False) + "\n")


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

    console.rule("[bold magenta]Agent8 Decision Hub — Error Recovery")
    console.print(
        f"  Target: {target_file} | Max steps: {max_steps} | "
        f"Debug: {AGENT8_DEBUG}"
    )

    # Anti-loop: track consecutive (action, error_sig) pair failures
    _last_action_error_pair: tuple[str, str] = ("", "")
    _consecutive_same_action_error: int = 0

    for tick in range(1, max_steps + 1):
        console.print(f"\n[magenta]--- Agent8 Tick {tick}/{max_steps} ---")

        # 1. Build context
        ctx = _build_agent8_tick_context(
            target_file, current_errors, current_plan, decision_history, staging_rel
        )

        # 2. Call Agent8 (fresh context every tick)
        agent8 = Agent("decision_hub")
        raw_reply = agent8.call(ctx)

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
            f"| error_sig=\"{error_sig[:40]}\""
        )
        console.print(f"  [Agent8] Reason: {decision.get('reason', '?')}")

        # 4a. Anti-loop: same (action, error_sig) pair repeated ≥ 2 times → force agent2_replan
        _escapable = action not in ("agent2_replan", "human_missing_assumption")
        _current_pair = (action, error_sig[:40])
        if _current_pair == _last_action_error_pair and _escapable:
            _consecutive_same_action_error += 1
        else:
            _consecutive_same_action_error = 1
            _last_action_error_pair = _current_pair

        if _consecutive_same_action_error >= 2 and _escapable:
            console.print(
                f"  [Agent8] ANTI-LOOP: same action+error pair repeated "
                f"{_consecutive_same_action_error}× → forcing agent2_replan"
            )
            action = "agent2_replan"
            decision["action"] = action
            targeted_prompt = (
                f"[FORCED by anti-loop: '{_current_pair[0]}' failed "
                f"{_consecutive_same_action_error}× for error '{error_sig[:60]}'] "
                + targeted_prompt
            )
            _consecutive_same_action_error = 0  # reset after forcing
            _last_action_error_pair = ("", "")

        # 4b. Hard trigger: same error_signature too many consecutive times → human gate
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

        # 5. Dispatch
        outcome: dict = {"outcome": "unknown"}

        try:
            if action == "agent3_tactical":
                console.print("  [Agent8→Agent3] Dispatching tactical fix...")
                result = _agent8_run_agent3(
                    target_file,
                    staging_rel,
                    current_plan,
                    targeted_prompt,
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
                console.print("  [Agent8→Agent2] Dispatching strategy revision...")
                current_plan = _agent8_run_agent2_replan(
                    agent2, target_file, current_errors, current_plan
                )
                # After replan, run Agent3 to apply the new strategy
                result = _agent8_run_agent3(
                    target_file, staging_rel, current_plan,
                    "Apply the revised proof strategy from Agent2. "
                    "Focus on the errors identified in the replan.",
                    None,
                )
                outcome = {
                    "outcome": "success" if result["exit_code"] == 0 and result["sorry_count"] == 0 else "failed",
                    "exit_code": result["exit_code"],
                    "sorry_count": result["sorry_count"],
                }
                current_errors = result.get("errors", current_errors)

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
                    **outcome,
                })
                _debug_log(algo_name, tick, decision, outcome)
                return False, current_plan, current_errors

        except Exception as exc:
            console.print(f"  [Agent8] Dispatch error: {exc}")
            outcome = {"outcome": "dispatch_error", "error": str(exc)}

        # 6. Record decision
        decision_history.append({
            "tick": tick,
            "action": action,
            "target_theorem": decision.get("target_theorem"),
            "error_signature": error_sig,
            **outcome,
        })
        _debug_log(algo_name, tick, decision, outcome)

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
