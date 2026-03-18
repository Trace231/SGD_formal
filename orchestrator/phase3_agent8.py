"""Agent8 Decision Hub — deterministic routing and lightweight dispatch.

This rewrite intentionally removes Agent8 self-LLM routing. Agent8 now:

1. Verifies the current file state.
2. Classifies the dominant error subtype deterministically.
3. Chooses a route from recent progress history.
4. Dispatches Agent3 / Agent7 / Agent9 directly.

The public entry points remain stable:

- ``run_agent8_loop(...) -> tuple[bool, str, str]``
- ``run_agent8_midcheck(...) -> dict``

Lower-level dispatch helpers are preserved for compatibility with
``phase3_agent3``.
"""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

from rich.console import Console

from orchestrator.agents import ToolRegistry
from orchestrator.config import RETRY_LIMITS
from orchestrator.error_classifier import _extract_first_error_line, _parse_lean_errors
from orchestrator.phase3_agent8_v1 import (
    _agent8_run_agent3_single as _legacy_agent3_single,
    _agent8_run_agent7 as _legacy_agent7,
    _agent8_run_agent7_then_agent6 as _legacy_agent7_then_agent6,
)
from orchestrator.phase3a_agent9 import run_agent9_replan

console = Console()

_SUBTYPE_DECLARATION_SYNTAX_FAILURE = "declaration_syntax_failure"
_SUBTYPE_DECLARATION_API_MISMATCH = "declaration_api_mismatch"
_SUBTYPE_PROOF_API_MISMATCH = "proof_api_mismatch"
_SUBTYPE_PROOF_TACTIC_FAILURE = "proof_tactic_failure"
_SUBTYPE_STRATEGY_MISMATCH = "strategy_mismatch"

_REPAIR_UNIT_LOCAL_PATCH = "local_patch"
_REPAIR_UNIT_BLOCK_RESTRUCTURE = "block_restructure"
_REPAIR_UNIT_STATEMENT_GAP = "statement_gap"

_BLOCKER_CERTIFIED_STRUCTURAL_BLOCK = "certified_structural_block"
_BLOCKER_CERTIFIED_STATEMENT_GAP = "certified_statement_gap"

_DECLARATION_SYNTAX_MARKERS = (
    "unexpected token",
    "invalid syntax",
    "expected token",
    "parser error",
)
_DECLARATION_ZONE_MARKERS = (
    "unknown identifier",
    "unknown constant",
    "invalid field",
    "failed to synthesize instance",
    "function expected",
)
_PROOF_ZONE_MARKERS = (
    "tactic",
    ":= by",
    "unsolved goals",
    "goal",
    "have ",
    "show ",
    "exact ",
    "apply ",
    "rw ",
)
_PROOF_STRUCTURAL_MARKERS = (
    "unsolved goals",
    "tactic",
    "rewrite failed",
    "apply failed",
    "exact failed",
    "no goals solved",
)
_PROOF_API_SHAPE_MARKERS = (
    "application type mismatch",
    "type mismatch",
    "too many arguments",
    "wrong number of arguments",
    "argument has wrong type",
    "function expected",
)


def _extract_error_signature(errors_text: str) -> str:
    """Extract a short key phrase from the first build error."""
    if not errors_text:
        return ""
    for line in errors_text.splitlines():
        line = line.strip()
        if not line:
            continue
        m = re.match(r".*?([^/:\s]+\.lean):(\d+):\d+:\s*error:\s*(.*)", line)
        if m:
            return f"{m.group(1)}:{m.group(2)}:{m.group(3).strip()[:120]}"
    return errors_text.splitlines()[0].strip()[:160]


def _canonical_error_signature(errors_text: str) -> str:
    """Stable error signature using file, line and normalized message head."""
    if not errors_text:
        return ""
    for line in errors_text.splitlines():
        line = line.strip()
        if not line:
            continue
        m = re.match(r".*?([^/:\s]+\.lean):(\d+):\d+:\s*error:\s*(.*)", line)
        if m:
            msg = re.sub(r"\s+", " ", m.group(3).strip().lower())
            return f"{m.group(1)}:{m.group(2)}:{msg[:80]}"
    return re.sub(r"\s+", " ", errors_text.strip().lower())[:120]


def _is_structural_error(error_signature: str, errors_text: str) -> bool:
    """Return True for declaration-zone / structure errors."""
    hay = f"{error_signature}\n{errors_text}".lower()
    if "declaration zone" in hay:
        return True
    if any(marker in hay for marker in _DECLARATION_SYNTAX_MARKERS):
        return True
    if any(marker in hay for marker in _DECLARATION_ZONE_MARKERS):
        if any(marker in hay for marker in ("have ", "show ", "exact ", "tactic")):
            return False
        return True
    return False


def _classify_error_subtype(
    errors_text: str,
    target_file: str = "",
    *,
    decision_history: list[dict] | None = None,
) -> str:
    """Classify the dominant routing subtype using deterministic heuristics."""
    _ = target_file
    if not errors_text:
        return _SUBTYPE_PROOF_TACTIC_FAILURE

    hay = errors_text.lower()

    if any(m in hay for m in _DECLARATION_SYNTAX_MARKERS):
        return _SUBTYPE_DECLARATION_SYNTAX_FAILURE

    if any(m in hay for m in _DECLARATION_ZONE_MARKERS):
        has_proof_zone_context = any(m in hay for m in _PROOF_ZONE_MARKERS)
        if not has_proof_zone_context:
            return _SUBTYPE_DECLARATION_API_MISMATCH
        return _SUBTYPE_DECLARATION_API_MISMATCH

    has_proof_zone_context = any(m in hay for m in _PROOF_ZONE_MARKERS)
    has_structural_proof_marker = any(m in hay for m in _PROOF_STRUCTURAL_MARKERS)
    has_api_shape_marker = any(m in hay for m in _PROOF_API_SHAPE_MARKERS)
    strong_api_signal = any(
        m in hay
        for m in (
            "too many arguments",
            "wrong number of arguments",
            "argument has wrong type",
            "applied to",
            "expects",
        )
    )

    if decision_history and len(decision_history) >= 3:
        recent = decision_history[-3:]
        all_zero_progress = all(
            int(entry.get("sorry_after", entry.get("sorry_before", 0)))
            >= int(entry.get("sorry_before", 0))
            and str(entry.get("canonical_error_signature", ""))
            == str(recent[-1].get("canonical_error_signature", ""))
            for entry in recent
        )
        if all_zero_progress:
            return _SUBTYPE_STRATEGY_MISMATCH

    if has_proof_zone_context and has_structural_proof_marker and not strong_api_signal:
        return _SUBTYPE_PROOF_TACTIC_FAILURE

    if has_api_shape_marker:
        return _SUBTYPE_PROOF_API_MISMATCH

    return _SUBTYPE_PROOF_TACTIC_FAILURE


def _target_region_from_errors(
    errors_text: str,
    *,
    fallback_span: str | None = None,
    radius: int = 3,
) -> str:
    """Build a stable coarse target-region label from current errors."""
    if fallback_span:
        return str(fallback_span)
    line = _extract_first_error_line(errors_text)
    if line is None:
        return "unknown"
    start = max(1, int(line) - max(0, int(radius)))
    stop = max(start, int(line) + max(0, int(radius)))
    return f"{start}-{stop}"


def _coerce_errors_text(errors: Any) -> str:
    if isinstance(errors, list):
        return "\n".join(str(x) for x in errors if str(x).strip())
    if errors is None:
        return ""
    return str(errors)


def _error_count_from_verify(verify_result: dict[str, Any], errors_text: str) -> int:
    if "error_count" in verify_result:
        try:
            return int(verify_result["error_count"])
        except Exception:
            pass
    errors = verify_result.get("errors", [])
    if isinstance(errors, list):
        return len([e for e in errors if str(e).strip()])
    structured = _parse_lean_errors(errors_text)
    if structured:
        return len(structured)
    return len([ln for ln in errors_text.splitlines() if ln.strip()])


def _agent8_result_score(result: dict[str, Any]) -> tuple[int, int, int]:
    """Smaller score is better."""
    return (
        int(result.get("exit_code", 1)),
        int(result.get("sorry_count", 999)),
        len(str(result.get("errors", ""))),
    )


def _extract_decl_signatures(text: str) -> list[str]:
    """Extract theorem/lemma declaration header lines for signature comparisons."""
    out: list[str] = []
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.startswith(("theorem ", "lemma ", "def ", "example ")):
            out.append(stripped)
    return out


def _estimate_patch_line_span(old_str: str, new_str: str) -> int:
    """Estimate the line span touched by a patch."""
    return max(
        len(old_str.splitlines()) if old_str else 0,
        len(new_str.splitlines()) if new_str else 0,
    )


def _patch_touches_decl_signature(old_str: str, new_str: str) -> bool:
    """Return True when a patch changes theorem/lemma declaration headers."""
    return _extract_decl_signatures(old_str) != _extract_decl_signatures(new_str)


def _build_agent9_theorem_context(agent9_plan: dict | None, target_theorem: str) -> str:
    """Return a compact theorem-specific block from the Agent9 plan."""
    if not agent9_plan or not target_theorem:
        return ""
    for thm in agent9_plan.get("theorems", []):
        if thm.get("name") != target_theorem:
            continue
        line_no = thm.get("lean_statement_line", thm.get("line_number", "?"))
        deps = thm.get("dependencies", thm.get("depends_on", []))
        difficulty = thm.get("estimated_difficulty", thm.get("difficulty", "unknown"))
        strategy = thm.get("proof_strategy", "")
        lemmas = thm.get("key_lib_lemmas", [])
        missing_glue = thm.get("missing_glue_lemmas", [])
        return (
            "\n\n[Agent9 theorem context]\n"
            f"name: {thm.get('name', '')}\n"
            f"lean_statement_line: {line_no}\n"
            f"estimated_difficulty: {difficulty}\n"
            f"depends_on: {deps}\n"
            f"proof_strategy: {strategy}\n"
            f"key_lib_lemmas: {lemmas}\n"
            f"missing_glue_lemmas: {missing_glue}\n"
        )
    return ""


def _no_progress_streak(
    history: list[dict],
    canonical_sig: str,
    *,
    window: int = 3,
) -> int:
    """Return consecutive no-progress streak length for the current canonical error."""
    streak = 0
    for entry in reversed(history):
        if str(entry.get("canonical_error_signature", "")) != canonical_sig:
            break
        sorry_before = int(entry.get("sorry_before", 0))
        sorry_after = int(entry.get("sorry_after", sorry_before))
        changed = bool(entry.get("main_error_signature_changed", False))
        if sorry_after < sorry_before or changed:
            break
        streak += 1
        if streak >= window:
            return streak
    return streak


def _prefer_agent3_search_owner(
    error_subtype: str,
    *,
    no_progress_streak: int = 0,
) -> tuple[str, str]:
    """Choose local_patch vs block_restructure for Agent3-owned proof repair."""
    if error_subtype in {_SUBTYPE_PROOF_TACTIC_FAILURE, _SUBTYPE_PROOF_API_MISMATCH}:
        if no_progress_streak >= 2:
            return _REPAIR_UNIT_BLOCK_RESTRUCTURE, "stalled local patch promoted to sampled search"
        return _REPAIR_UNIT_LOCAL_PATCH, "proof-body repair stays with Agent3"
    return _REPAIR_UNIT_LOCAL_PATCH, "default local patch"


def _route_for_subtype(
    subtype: str,
    history: list[dict],
    canonical_sig: str,
) -> tuple[str, str, str]:
    """Pure deterministic routing based on subtype and recent progress."""
    streak = _no_progress_streak(history, canonical_sig, window=6)
    last_action = str(history[-1].get("action", "")) if history else ""

    if subtype == _SUBTYPE_STRATEGY_MISMATCH:
        if last_action == "agent9_replan":
            return "human_missing_assumption", _REPAIR_UNIT_STATEMENT_GAP, "strategy mismatch persisted after replan"
        return "agent9_replan", _REPAIR_UNIT_STATEMENT_GAP, "repeated zero-progress suggests strategy mismatch"

    if subtype in {
        _SUBTYPE_DECLARATION_SYNTAX_FAILURE,
        _SUBTYPE_DECLARATION_API_MISMATCH,
    }:
        if streak >= 4 and last_action == "agent9_replan":
            return "human_missing_assumption", _REPAIR_UNIT_STATEMENT_GAP, "declaration error persisted after agent7 and replan"
        if streak >= 2 and last_action == "agent7_signature":
            return "agent9_replan", _REPAIR_UNIT_STATEMENT_GAP, "agent7 signature fix stalled on same declaration error"
        return "agent7_signature", _REPAIR_UNIT_LOCAL_PATCH, "declaration-zone issues belong to Agent7"

    if streak >= 5 and last_action == "agent9_replan":
        return "human_missing_assumption", _REPAIR_UNIT_STATEMENT_GAP, "proof-body search still stalled after replan"
    if streak >= 4:
        return "agent9_replan", _REPAIR_UNIT_STATEMENT_GAP, "proof-body search stalled across multiple ticks"
    if streak >= 2:
        return "agent3_tactical", _REPAIR_UNIT_BLOCK_RESTRUCTURE, "same proof region stalled; widen Agent3 search"
    return "agent3_tactical", _REPAIR_UNIT_LOCAL_PATCH, "proof-body fix remains with Agent3"


def _coerce_prompt_text(value: Any, fallback: str) -> str:
    text = str(value or "").strip()
    return text if text else fallback


def _resolve_decision_prompt(decision: Any, key: str, fallback: str) -> str:
    if isinstance(decision, dict):
        return _coerce_prompt_text(decision.get(key, ""), fallback)
    return fallback


def _format_replanned_guidance(current_plan_text: str, new_plan: dict[str, Any]) -> str:
    if not new_plan:
        return current_plan_text
    return (
        current_plan_text.rstrip()
        + "\n\n## Agent9 Replan\n"
        + json.dumps(new_plan, indent=2, ensure_ascii=False)
        + "\n"
    )


_agent8_run_agent3_single = _legacy_agent3_single
_agent8_run_agent7 = _legacy_agent7
_agent8_run_agent7_then_agent6 = _legacy_agent7_then_agent6


def _agent8_run_agent3(
    target_file: str,
    agent2_plan: str,
    targeted_prompt: str,
    allowed_edit_lines: str | None,
    *,
    max_turns: int | None = None,
    compile_first_mode: bool = False,
    patch_guard_mode: bool = False,
    search_allowed: bool | None = None,
    transactional_mode: bool = False,
    error_subtype: str = "",
    repair_unit: str = _REPAIR_UNIT_LOCAL_PATCH,
    target_region: str = "",
) -> dict[str, Any]:
    """Dispatch Agent3 through the Agent3 search kernel.

    The new Agent8 ignores ``allowed_edit_lines`` and lets Agent3 own search scope.
    """
    from orchestrator.phase3_agent3 import run_agent3_search_kernel

    _ = allowed_edit_lines
    max_turns = max_turns or int(RETRY_LIMITS.get("AGENT8_AGENT3_MAX_TURNS", 15))
    if repair_unit == _REPAIR_UNIT_BLOCK_RESTRUCTURE and not transactional_mode:
        max_turns = min(
            max_turns,
            int(RETRY_LIMITS.get("AGENT8_AGENT3_SAMPLE_MAX_TURNS_PER_CANDIDATE", 8)),
        )
    return run_agent3_search_kernel(
        target_file,
        agent2_plan,
        targeted_prompt,
        None,
        max_turns=max_turns,
        compile_first_mode=compile_first_mode,
        patch_guard_mode=patch_guard_mode,
        search_allowed=search_allowed,
        transactional_mode=transactional_mode,
        error_subtype=error_subtype,
        repair_unit=repair_unit,
        target_region=target_region,
        run_single_candidate=_agent8_run_agent3_single,
    )


def _execute_agent7_direct_apply(target_file: str, agent7_plan: dict[str, Any] | None) -> None:
    if not isinstance(agent7_plan, dict):
        return
    ordered_steps = agent7_plan.get("ordered_steps", [])
    if not isinstance(ordered_steps, list):
        return
    exec_registry = ToolRegistry()
    exec_registry.register_default_tools()
    for step in ordered_steps:
        if not isinstance(step, dict) or not step.get("direct_apply"):
            continue
        if step.get("tool") != "edit_file_patch":
            continue
        req = step.get("required_args", {}) or {}
        old_str = req.get("old_str")
        new_str = req.get("new_str")
        if not old_str or new_str is None:
            continue
        try:
            exec_registry.call(
                "edit_file_patch",
                path=req.get("path", target_file),
                old_str=old_str,
                new_str=new_str,
            )
        except Exception as exc:
            console.print(f"[yellow][Agent8] Agent7 direct_apply failed: {exc}")


def _dispatch_agent9(
    target_file: str,
    current_errors: str,
    current_plan_dict: dict[str, Any],
    algo_name: str,
    current_plan_text: str,
) -> dict[str, Any]:
    return run_agent9_replan(
        target_file,
        current_errors,
        current_plan_dict,
        algo_name,
        current_plan_text,
    )


def _make_history_entry(
    *,
    tick: int,
    action: str,
    subtype: str,
    repair_unit: str,
    target_region: str,
    before: dict[str, Any],
    after: dict[str, Any],
    reason: str,
) -> dict[str, Any]:
    before_errors = _coerce_errors_text(before.get("errors", ""))
    after_errors = _coerce_errors_text(after.get("errors", ""))
    before_sig = _canonical_error_signature(before_errors)
    after_sig = _canonical_error_signature(after_errors)
    before_sorry = int(before.get("sorry_count", 999))
    after_sorry = int(after.get("sorry_count", before_sorry))
    before_count = _error_count_from_verify(before, before_errors)
    after_count = _error_count_from_verify(after, after_errors)
    blocker_status = (
        _BLOCKER_CERTIFIED_STATEMENT_GAP
        if repair_unit == _REPAIR_UNIT_STATEMENT_GAP
        else ""
    )
    return {
        "tick": tick,
        "action": action,
        "repair_unit": repair_unit,
        "target_region": target_region,
        "reason": reason,
        "error_subtype": subtype,
        "error_signature": before_sig,
        "canonical_error_signature": after_sig or before_sig,
        "errors_before": before_errors,
        "errors_after": after_errors,
        "top_error_count_before": before_count,
        "top_error_count_after": after_count,
        "error_count_delta": after_count - before_count,
        "main_error_signature_changed": after_sig != before_sig,
        "route_effective": after_sorry < before_sorry or after_sig != before_sig or after_count < before_count,
        "sorry_before": before_sorry,
        "sorry_after": after_sorry,
        "sorry_delta": after_sorry - before_sorry,
        "outcome": "success"
        if int(after.get("exit_code", 1)) == 0 and after_sorry == 0
        else "failed",
        "blocker_status": blocker_status,
        "blocker_report": (
            {
                "repair_unit": repair_unit,
                "blocker_status": blocker_status,
                "target_region": target_region,
                "reason": reason,
            }
            if blocker_status
            else {}
        ),
    }


def _current_plan_dict_from_text(plan_text: str) -> dict[str, Any]:
    try:
        obj = json.loads(plan_text)
    except Exception:
        return {}
    return obj if isinstance(obj, dict) else {}


def run_agent8_loop(
    agent2: Any,
    target_file: str,
    agent2_plan: str,
    last_errors: str,
    *,
    best_checkpoint: dict | None = None,
    agent9_plan: dict | None = None,
) -> tuple[bool, str, str]:
    """Run deterministic Agent8 routing until success or exhaustion."""
    from orchestrator.tools import run_lean_verify

    _ = agent2
    algo_name = Path(target_file).stem
    max_steps = int(RETRY_LIMITS.get("AGENT8_MAX_STEPS", 8))
    decision_history: list[dict[str, Any]] = []
    current_plan_text = agent2_plan
    current_plan_dict = agent9_plan or _current_plan_dict_from_text(agent2_plan)
    current_errors = last_errors

    if best_checkpoint and isinstance(best_checkpoint, dict):
        current_errors = _coerce_errors_text(best_checkpoint.get("errors", current_errors))

    console.rule("[bold magenta]Agent8 Decision Hub — Deterministic Router")
    console.print(f"  Target: {target_file} | Max steps: {max_steps}")

    for tick in range(1, max_steps + 1):
        fresh = dict(run_lean_verify(target_file))
        fresh_errors = _coerce_errors_text(fresh.get("errors", current_errors))
        fresh["errors"] = fresh_errors
        current_errors = fresh_errors

        if int(fresh.get("exit_code", 1)) == 0 and int(fresh.get("sorry_count", -1)) == 0:
            return True, current_plan_text, ""

        subtype = _classify_error_subtype(
            current_errors,
            target_file,
            decision_history=decision_history,
        )
        canonical_sig = _canonical_error_signature(current_errors)
        action, repair_unit, reason = _route_for_subtype(subtype, decision_history, canonical_sig)
        target_region = _target_region_from_errors(current_errors)

        console.print(
            f"  [Agent8] tick={tick} action={action} subtype={subtype} "
            f"repair_unit={repair_unit} sig={canonical_sig[:80]}"
        )
        console.print(f"  [Agent8] reason: {reason}")

        if action == "human_missing_assumption":
            decision_history.append(
                _make_history_entry(
                    tick=tick,
                    action=action,
                    subtype=subtype,
                    repair_unit=repair_unit,
                    target_region=target_region,
                    before=fresh,
                    after=fresh,
                    reason=reason,
                )
            )
            return False, current_plan_text, current_errors

        if action == "agent7_signature":
            a7_prompt = (
                f"[deterministic route] {reason}\n"
                f"Current errors:\n{current_errors[:2000]}"
            )
            a7_plan, _raw = _agent8_run_agent7(target_file, current_errors, a7_prompt)
            _execute_agent7_direct_apply(target_file, a7_plan)
            result = dict(run_lean_verify(target_file))
        elif action == "agent9_replan":
            new_plan = _dispatch_agent9(
                target_file,
                current_errors,
                current_plan_dict,
                algo_name,
                current_plan_text,
            )
            if isinstance(new_plan, dict) and new_plan:
                current_plan_dict = new_plan
                current_plan_text = _format_replanned_guidance(current_plan_text, new_plan)
            result = dict(run_lean_verify(target_file))
        else:
            theorem_hint = ""
            if isinstance(current_plan_dict, dict):
                theorem_hint = _build_agent9_theorem_context(current_plan_dict, algo_name)
            prompt = (
                f"[deterministic route] {reason}\n"
                f"Error subtype: {subtype}\n"
                f"Target region: {target_region}\n"
                + theorem_hint
            )
            result = _agent8_run_agent3(
                target_file,
                current_plan_text,
                prompt,
                None,
                compile_first_mode=False,
                transactional_mode=False,
                patch_guard_mode=False,
                search_allowed=(repair_unit == _REPAIR_UNIT_BLOCK_RESTRUCTURE),
                error_subtype=subtype,
                repair_unit=repair_unit,
                target_region=target_region,
            )

        result = dict(result)
        result["errors"] = _coerce_errors_text(result.get("errors", current_errors))
        current_errors = result["errors"]
        decision_history.append(
            _make_history_entry(
                tick=tick,
                action=action,
                subtype=subtype,
                repair_unit=repair_unit,
                target_region=target_region,
                before=fresh,
                after=result,
                reason=reason,
            )
        )

        if int(result.get("exit_code", 1)) == 0 and int(result.get("sorry_count", -1)) == 0:
            return True, current_plan_text, ""

    return False, current_plan_text, current_errors


def run_agent8_midcheck(
    target_file: str,
    current_plan: str,
    current_errors: str,
    *,
    agent2: Any | None = None,
    agent9_plan: dict | None = None,
    decision_history: list[dict] | None = None,
    turns_elapsed: int = 0,
    baseline_errors: str = "",
) -> dict[str, Any]:
    """Return a deterministic soft-gate decision for the Agent3 inner loop."""
    from orchestrator.tools import run_lean_verify

    _ = (agent2, agent9_plan, baseline_errors)
    history = decision_history or []
    fresh = dict(run_lean_verify(target_file))
    fresh_errors = _coerce_errors_text(fresh.get("errors", current_errors))
    subtype = _classify_error_subtype(fresh_errors, target_file, decision_history=history)
    canonical_sig = _canonical_error_signature(fresh_errors)
    action, repair_unit, reason = _route_for_subtype(subtype, history, canonical_sig)
    target_region = _target_region_from_errors(fresh_errors)
    _, search_reason = _prefer_agent3_search_owner(
        subtype,
        no_progress_streak=_no_progress_streak(history, canonical_sig, window=6),
    )

    agent3_execution_mode = (
        "search"
        if action == "agent3_tactical" and repair_unit == _REPAIR_UNIT_BLOCK_RESTRUCTURE
        else "local_patch"
    )

    return {
        "action": action,
        "priority_level": "P1" if action != "agent3_tactical" else "P4",
        "reason": reason,
        "targeted_prompt": (
            f"[midcheck turn {turns_elapsed}] {reason}\n"
            f"Current errors:\n{fresh_errors[:2000]}\n"
        ),
        "error_signature": _extract_error_signature(fresh_errors),
        "canonical_error_signature": canonical_sig,
        "hypothesis": reason,
        "confidence": 1.0,
        "counterfactual": "deterministic router replaces Agent8 self-LLM arbitration",
        "error_subtype": subtype,
        "repair_unit": repair_unit,
        "target_region": target_region,
        "agent3_execution_mode": agent3_execution_mode,
        "agent7_targeted_prompt": f"[midcheck] {reason}",
        "agent6_targeted_prompt": f"[midcheck] {reason}",
        "blocker_status": (
            _BLOCKER_CERTIFIED_STATEMENT_GAP
            if repair_unit == _REPAIR_UNIT_STATEMENT_GAP
            else ""
        ),
        "blocker_report": (
            {
                "repair_unit": repair_unit,
                "blocker_status": _BLOCKER_CERTIFIED_STATEMENT_GAP,
                "target_region": target_region,
                "reason": reason,
            }
            if repair_unit == _REPAIR_UNIT_STATEMENT_GAP
            else {}
        ),
        "investigation_success": False,
        "investigation_failures": [],
        "search_reason": search_reason,
        "current_plan_preview": current_plan[:200] if current_plan else "",
    }


__all__ = [
    "_BLOCKER_CERTIFIED_STATEMENT_GAP",
    "_BLOCKER_CERTIFIED_STRUCTURAL_BLOCK",
    "_REPAIR_UNIT_BLOCK_RESTRUCTURE",
    "_REPAIR_UNIT_LOCAL_PATCH",
    "_REPAIR_UNIT_STATEMENT_GAP",
    "_SUBTYPE_DECLARATION_API_MISMATCH",
    "_SUBTYPE_DECLARATION_SYNTAX_FAILURE",
    "_SUBTYPE_PROOF_API_MISMATCH",
    "_SUBTYPE_PROOF_TACTIC_FAILURE",
    "_SUBTYPE_STRATEGY_MISMATCH",
    "_agent8_result_score",
    "_agent8_run_agent3",
    "_agent8_run_agent3_single",
    "_agent8_run_agent7",
    "_agent8_run_agent7_then_agent6",
    "_build_agent9_theorem_context",
    "_canonical_error_signature",
    "_classify_error_subtype",
    "_coerce_errors_text",
    "_coerce_prompt_text",
    "_estimate_patch_line_span",
    "_error_count_from_verify",
    "_extract_decl_signatures",
    "_extract_error_signature",
    "_is_structural_error",
    "_patch_touches_decl_signature",
    "_prefer_agent3_search_owner",
    "_resolve_decision_prompt",
    "_route_for_subtype",
    "run_agent8_loop",
    "run_agent8_midcheck",
]
