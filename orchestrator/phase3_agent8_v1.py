"""Agent8 Decision Hub — Phase 3 error-recovery state machine.

After all normal Agent3 retry attempts are exhausted, this module runs a
tick-based decision loop.  Each tick:
  1. Clears Agent8's context (anti-pollution).
  2. Builds a minimal diagnostic context (truncated file, errors, decision history).
  3. Calls Agent8 to produce a single JSON decision.
  4. Dispatches the chosen action (Agent3 tactical, Agent7 signature, Agent7→Agent6
     bridge lemma, Agent9 replan, or human gate).
  5. Verifies the result; appends to decision_history.
  6. Exits early on success (exit=0, sorry=0) or human gate.
"""
from __future__ import annotations

import hashlib
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
    _call_agent7_with_tools,
    _run_agent6_glue_loop,
)
from orchestrator.contracts import (
    AGENT8_REQUIRED_DECISION_FIELDS,
    AGENT8_VALID_ACTIONS,
    AGENT8_VALID_BLOCKER_STATUSES,
    AGENT8_VALID_ERROR_SUBTYPES,
    AGENT8_VALID_REPAIR_UNITS,
)
from orchestrator.config import (
    AGENT8_APOLLO_DECOMPOSE_ENABLED,
    AGENT8_DEBUG,
    AGENT8_FILE_WINDOW_RADIUS,
    AGENT8_HUMAN_GATE_CONSECUTIVE_THRESHOLD,
    AUDIT_DIR,
    PROJECT_ROOT,
    REFERENCE_FILES_WITH_DESCRIPTIONS,
    RETRY_LIMITS,
)
from orchestrator.context_builders import (
    _build_stale_error_hint,
    _build_escalation_file_context,
    _extract_imported_algo_sigs,
    _prioritize_error_text,
    _prequery_dependency_signatures,
)
from orchestrator.error_classifier import (
    _extract_first_error_line,
    _json_candidates,
    _parse_lean_errors,
)
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


def _canonical_error_signature(errors_text: str) -> str:
    """Stable verifier-derived primary error signature."""
    if not errors_text:
        return ""
    for line in errors_text.splitlines():
        line = line.strip()
        if not line or line.startswith("--"):
            continue
        m = re.match(r"(.*?):(\d+):(\d+):\s*(?:error:\s*)?(.*)", line)
        if m:
            file_part = Path(m.group(1)).name
            msg = re.sub(r"\s+", " ", m.group(4).strip()).lower()
            return f"{file_part}:{m.group(2)}:{msg[:160]}"
        return re.sub(r"\s+", " ", line).lower()[:160]
    return re.sub(r"\s+", " ", errors_text.strip()).lower()[:160]


def _is_structural_error(error_signature: str, errors_text: str) -> bool:
    """Heuristic: structural errors require at least one investigation lookup."""
    hay = f"{error_signature}\n{errors_text}".lower()
    has_proof_zone = any(m in hay for m in _PROOF_ZONE_MARKERS)
    has_decl_zone = any(m in hay for m in _DECLARATION_ZONE_MARKERS)
    if has_proof_zone and not has_decl_zone and any(
        marker in hay for marker in ("application type mismatch", "failed to synthesize")
    ):
        return False
    structural_markers = (
        "unknown identifier",
        "unknown constant",
        "failed to synthesize",
        "typeclass",
        "application type mismatch",
        "declaration zone",
        "invalid field",
    )
    return any(m in hay for m in structural_markers)


# ---------------------------------------------------------------------------
# Error Subtype Classifier
# ---------------------------------------------------------------------------

# Stable string constant for the canonical subtypes.
_SUBTYPE_DECLARATION_SYNTAX_FAILURE = "declaration_syntax_failure"
_SUBTYPE_DECLARATION_API_MISMATCH = "declaration_api_mismatch"
_SUBTYPE_PROOF_API_MISMATCH       = "proof_api_mismatch"
_SUBTYPE_PROOF_TACTIC_FAILURE     = "proof_tactic_failure"
_SUBTYPE_STRATEGY_MISMATCH        = "strategy_mismatch"

_REPAIR_UNIT_LOCAL_PATCH = "local_patch"
_REPAIR_UNIT_BLOCK_RESTRUCTURE = "block_restructure"
_REPAIR_UNIT_GLUE = "glue"
_REPAIR_UNIT_GLOBAL_REPLAN = "global_replan"
_REPAIR_UNIT_STATEMENT_GAP = "statement_gap"

_BLOCKER_RESOLVED = "resolved"
_BLOCKER_ESCALATED_SUBPROBLEM = "escalated_subproblem"
_BLOCKER_CERTIFIED_STATEMENT_GAP = "certified_statement_gap"
_BLOCKER_CERTIFIED_STRUCTURAL_BLOCK = "certified_structural_block"
_BLOCKER_INFRA_FAILURE = "infra_failure"

# Markers that strongly suggest the error is inside a proof body (:= by ...)
_PROOF_ZONE_MARKERS = (
    "tactic",
    "rewrite",
    "linarith",
    "simp",
    "ring",
    "have ",
    "calc ",
    "exact ",
    "apply ",
    "unsolved goals",
    "motive is not type correct",
    "function expected",
)

# Markers that strongly suggest API shape mismatch inside a proof body
_PROOF_API_SHAPE_MARKERS = (
    "integral_",
    "sum_range",
    "finset.sum",
    "integral_add",
    "integral_sub",
    "integral_const_mul",
    "integral_const",
    "integral_nonneg",
    "integral_mono",
    "measure_theory",
    "too many arguments",
    "wrong number of arguments",
    "argument has wrong type",
    "applied to",
    "explicit argument",
    "implicit argument",
    "expects",
)

_PROOF_STRUCTURAL_MARKERS = (
    "rewrite failed",
    "did not simplify",
    "did not find an occurrence",
    "no goals to be solved",
    "unsolved goals",
    "could not unify",
    "calc ",
    "have ",
    "sum_add_distrib",
    "sum_mul",
    "sum_range_succ",
    "linarith",
    "ring",
    "field_simp",
    "gcongr",
    "type mismatch",
    "application type mismatch",
)

# Markers that point to the declaration zone (before := by)
_DECLARATION_ZONE_MARKERS = (
    "unknown identifier",
    "unknown constant",
    "invalid field",
    "declaration zone",
    "cannot find",
    "failed to synthesize",
    "typeclass",
)
_DECLARATION_SYNTAX_MARKERS = (
    "unexpected token",
    "invalid syntax",
    "unexpected end of input",
    "expected '}'",
    "expected ']'",
    "expected ')'",
    "parser",
)


def _classify_error_subtype(
    errors_text: str,
    target_file: str = "",
    *,
    decision_history: "list[dict] | None" = None,
) -> str:
    """Classify the dominant error category for routing decisions.

    Returns one of canonical subtype strings:
    - ``declaration_syntax_failure`` — parser/syntax error before semantic checks
    - ``declaration_api_mismatch``  — error before ``:= by`` (declaration zone)
    - ``proof_api_mismatch``        — API shape/arg error inside proof body
    - ``proof_tactic_failure``      — pure tactic logic failure inside proof body
    - ``strategy_mismatch``         — repeated failures suggest wrong math approach

    The classifier is purely text-heuristic; it never calls LLM or tools.
    It uses a three-stage waterfall:
      1. Zone feature  — detect declaration-zone keywords
      2. Semantic feature — detect proof-zone API shape markers
      3. History feature — repeated zero-progress signals strategy mismatch
    """
    if not errors_text:
        return _SUBTYPE_PROOF_TACTIC_FAILURE  # default

    hay = errors_text.lower()
    error_sig = _extract_error_signature(errors_text).lower()

    # Stage 0 — Declaration syntax/parser failure (highest priority)
    if any(m in hay for m in _DECLARATION_SYNTAX_MARKERS):
        return _SUBTYPE_DECLARATION_SYNTAX_FAILURE

    # Stage 1 — Declaration zone: strong structural markers
    if any(m in hay for m in _DECLARATION_ZONE_MARKERS):
        # Narrow to declaration zone if there is NO proof-zone context in the
        # same error block (some errors appear at both locations).
        has_proof_zone_context = any(m in hay for m in _PROOF_ZONE_MARKERS)
        # declaration zone markers without conflicting proof zone → P0-class
        if not has_proof_zone_context:
            return _SUBTYPE_DECLARATION_API_MISMATCH
        # Both markers → prefer declaration since structural takes priority.
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

    # Stage 2 — repeated zero-progress across recent ticks upgrades to strategy
    # mismatch even when the visible surface error is still a tactic failure.
    if decision_history and len(decision_history) >= 3:
        _recent = decision_history[-3:]
        _all_zero_progress = all(
            e.get("top_error_count_after", 0) >= e.get("top_error_count_before", 0)
            and e.get("outcome") in ("failed", "dispatch_error")
            for e in _recent
        )
        if _all_zero_progress:
            return _SUBTYPE_STRATEGY_MISMATCH

    # Stage 3 — proof-body structural/tactic failures should dominate generic
    # type-mismatch wording unless there is strong call-shape evidence.
    if has_proof_zone_context and has_structural_proof_marker and not strong_api_signal:
        return _SUBTYPE_PROOF_TACTIC_FAILURE

    # Stage 4 — Proof API shape mismatch inside proof body
    if has_api_shape_marker:
        if has_proof_zone_context:
            return _SUBTYPE_PROOF_API_MISMATCH
        return _SUBTYPE_PROOF_API_MISMATCH

    # Default: proof tactic failure
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


def _region_no_progress_streak(
    decision_history: list[dict],
    *,
    target_region: str,
    repair_unit: str,
) -> int:
    """Count trailing no-progress entries for the same region/repair family."""
    if not target_region or target_region == "unknown":
        return 0
    streak = 0
    for entry in reversed(decision_history):
        if str(entry.get("target_region", "")) != target_region:
            break
        if str(entry.get("repair_unit", "")) != repair_unit:
            break
        if not _is_no_progress_entry(entry):
            break
        streak += 1
    return streak


def _build_block_restructure_contract(
    *,
    target_region: str,
    subproblem_kind: str = "",
) -> str:
    """Operational contract for block-level proof rewrites."""
    kind_hint = f" Active APOLLO node kind: `{subproblem_kind}`." if subproblem_kind else ""
    return (
        "\n\n[BLOCK RESTRUCTURE CONTRACT]\n"
        f"Target region: {target_region or 'unknown'}.{kind_hint}\n"
        "This is NOT a pure API-signature patch round.\n"
        "Work on one proof block only and keep surrounding declarations stable.\n"
        "Protocol:\n"
        "  1. Re-read the target block and identify the exact goal-shape mismatch.\n"
        "  2. Prefer splitting long `calc` / `have` chains into explicit intermediate steps.\n"
        "  3. Rewrite one local block at a time; do not broad-rewrite the file.\n"
        "  4. Use get_lean_goal/check_lean_have when the blocker is a nested subgoal.\n"
        "  5. Verify immediately after each block rewrite and checkpoint progress.\n"
        "  6. Preserve theorem/lemma headers; refactor proof bodies only.\n"
    )


def _build_blocker_report(
    *,
    blocker_status: str,
    repair_unit: str,
    target_region: str,
    error_subtype: str,
    error_signature: str,
    decision_history: list[dict],
    attempted_actions: list[str] | None = None,
    apollo_attempted: bool = False,
    current_errors: str = "",
) -> dict[str, Any]:
    """Create a structured blocker report for stable termination/audit."""
    attempted = attempted_actions or []
    if not attempted:
        attempted = [
            str(entry.get("action", ""))
            for entry in decision_history
            if str(entry.get("target_region", "")) == target_region
        ]
    attempted = [a for a in attempted if a]
    return {
        "blocker_status": blocker_status,
        "repair_unit": repair_unit,
        "target_region": target_region,
        "error_subtype": error_subtype,
        "error_signature": error_signature[:180],
        "attempted_actions": attempted[-6:],
        "same_region_attempts": sum(
            1 for entry in decision_history
            if str(entry.get("target_region", "")) == target_region
        ),
        "apollo_attempted": bool(apollo_attempted),
        "latest_error_excerpt": str(current_errors or "").splitlines()[:3],
    }


_PROOF_API_STRUCTURAL_MARKERS = (
    "rewrite failed",
    "did not simplify",
    "did not find an occurrence",
    "no goals to be solved",
    "could not unify",
    "pattern",
    "calc ",
    "have ",
    "field_simp",
    "gcongr",
    "sum_le_sum",
    "sum_add_distrib",
    "sum_mul",
)


def _proof_api_local_patch_attempts(
    decision_history: list[dict],
    *,
    target_region: str,
) -> int:
    """Count prior local-patch proof-api attempts for one target region."""
    if not target_region or target_region == "unknown":
        return 0
    return sum(
        1
        for entry in decision_history
        if str(entry.get("target_region", "")) == target_region
        and str(entry.get("repair_unit", "")) == _REPAIR_UNIT_LOCAL_PATCH
        and str(entry.get("action", "")) == "agent3_tactical"
        and str(entry.get("error_subtype", "")) == _SUBTYPE_PROOF_API_MISMATCH
        and str(entry.get("outcome", "")) != "network_failure"
    )


def _proof_api_prefers_search_restructure(
    *,
    error_subtype: str,
    current_errors: str,
    decision_history: list[dict],
    target_region: str,
    allowed_edit_lines: str | None = None,
) -> bool:
    """Whether proof-body API mismatch should leave strict transactional patching."""
    if error_subtype != _SUBTYPE_PROOF_API_MISMATCH:
        return False

    hay = str(current_errors or "").lower()
    if not any(marker in hay for marker in _PROOF_API_STRUCTURAL_MARKERS):
        return False

    local_patch_ticks = _proof_api_local_patch_attempts(
        decision_history,
        target_region=target_region,
    )
    region_attempts = sum(
        1 for entry in decision_history
        if str(entry.get("target_region", "")) == target_region
    )
    no_progress_streak = _region_no_progress_streak(
        decision_history,
        target_region=target_region,
        repair_unit=_REPAIR_UNIT_LOCAL_PATCH,
    )
    local_patch_cap = max(
        1,
        int(RETRY_LIMITS.get("AGENT8_PROOF_API_LOCAL_PATCH_MAX_TICKS", 1)),
    )
    sampling_trigger = max(
        1,
        int(RETRY_LIMITS.get("AGENT8_PROOF_API_SAMPLING_TRIGGER", 2)),
    )
    region_streak_trigger = max(
        1,
        int(RETRY_LIMITS.get("AGENT8_PROOF_API_REGION_STREAK_TRIGGER", 2)),
    )
    return (
        local_patch_ticks >= local_patch_cap
        or region_attempts >= sampling_trigger
        or no_progress_streak >= max(1, region_streak_trigger - 1)
        or (bool(allowed_edit_lines) and no_progress_streak >= 1)
    )


def _agent3_execution_mode_for_repair(
    *,
    error_subtype: str,
    repair_unit: str,
    current_errors: str,
    decision_history: list[dict],
    target_region: str,
    allowed_edit_lines: str | None = None,
) -> str:
    """Return the preferred Agent3 execution mode for this repair."""
    if repair_unit == _REPAIR_UNIT_BLOCK_RESTRUCTURE:
        return "sampled_search"
    if _proof_api_prefers_search_restructure(
        error_subtype=error_subtype,
        current_errors=current_errors,
        decision_history=decision_history,
        target_region=target_region,
        allowed_edit_lines=allowed_edit_lines,
    ):
        return "sampled_search"
    if error_subtype == _SUBTYPE_PROOF_API_MISMATCH:
        return "transactional_local_patch"
    return "local_patch"


def _prefer_agent3_search_owner(
    *,
    action: str,
    error_subtype: str,
    current_errors: str,
    decision_history: list[dict],
    target_region: str,
    allowed_edit_lines: str | None = None,
) -> tuple[str, str]:
    """Keep proof-body search/decomposition centered in Agent3 when possible."""
    structural_proof_body = (
        error_subtype == _SUBTYPE_PROOF_TACTIC_FAILURE
        or _proof_api_prefers_search_restructure(
            error_subtype=error_subtype,
            current_errors=current_errors,
            decision_history=decision_history,
            target_region=target_region,
            allowed_edit_lines=allowed_edit_lines,
        )
    )
    if not structural_proof_body:
        return action, ""

    if action in {"apollo_decompose_repair", "agent9_replan"}:
        return (
            "agent3_tactical",
            "Agent8 lightweight router keeps structural proof-body search/decomposition inside Agent3.",
        )
    if action == "agent7_signature" and not any(
        marker in str(current_errors or "").lower()
        for marker in _DECLARATION_ZONE_MARKERS
    ):
        return (
            "agent3_tactical",
            "Agent8 lightweight router avoids escalating structural proof-body failures to Agent7.",
        )
    return action, ""


def _classify_repair_unit(
    *,
    action: str,
    error_subtype: str,
    current_errors: str,
    decision_history: list[dict],
    target_region: str,
    allowed_edit_lines: str | None = None,
    subproblem_kind: str = "",
) -> str:
    """Map current evidence to the minimum repair unit, independent of action."""
    if action == "agent7_then_agent6" or subproblem_kind == "missing_glue":
        return _REPAIR_UNIT_GLUE
    if action == "agent9_replan" or subproblem_kind == "global_strategy":
        return _REPAIR_UNIT_GLOBAL_REPLAN
    if action == "human_missing_assumption" or subproblem_kind == "assumption_gap":
        return _REPAIR_UNIT_STATEMENT_GAP
    if subproblem_kind == "proof_state_sublemma":
        return _REPAIR_UNIT_BLOCK_RESTRUCTURE

    hay = str(current_errors or "").lower()
    restructure_markers = _PROOF_API_STRUCTURAL_MARKERS
    if any(marker in hay for marker in restructure_markers):
        _streak = _region_no_progress_streak(
            decision_history,
            target_region=target_region,
            repair_unit=_REPAIR_UNIT_LOCAL_PATCH,
        )
        if _streak >= max(1, int(RETRY_LIMITS.get("AGENT8_BLOCK_RESTRUCTURE_TRIGGER", 2)) - 1):
            return _REPAIR_UNIT_BLOCK_RESTRUCTURE
        if error_subtype == _SUBTYPE_PROOF_TACTIC_FAILURE:
            return _REPAIR_UNIT_BLOCK_RESTRUCTURE

    if error_subtype == _SUBTYPE_STRATEGY_MISMATCH:
        region_attempts = sum(
            1 for entry in decision_history
            if str(entry.get("target_region", "")) == target_region
        )
        if region_attempts >= int(RETRY_LIMITS.get("AGENT8_STATEMENT_GAP_REGION_THRESHOLD", 4)):
            return _REPAIR_UNIT_STATEMENT_GAP
        return _REPAIR_UNIT_GLOBAL_REPLAN

    if _proof_api_prefers_search_restructure(
        error_subtype=error_subtype,
        current_errors=current_errors,
        decision_history=decision_history,
        target_region=target_region,
        allowed_edit_lines=allowed_edit_lines,
    ):
        return _REPAIR_UNIT_BLOCK_RESTRUCTURE

    if error_subtype == _SUBTYPE_PROOF_API_MISMATCH and not allowed_edit_lines and "application type mismatch" in hay:
        _streak = _region_no_progress_streak(
            decision_history,
            target_region=target_region,
            repair_unit=_REPAIR_UNIT_LOCAL_PATCH,
        )
        if _streak >= int(RETRY_LIMITS.get("AGENT8_BLOCK_RESTRUCTURE_TRIGGER", 2)):
            return _REPAIR_UNIT_BLOCK_RESTRUCTURE

    return _REPAIR_UNIT_LOCAL_PATCH


def _count_error_lines(errors_text: str) -> int:
    """Count Lean-style error lines to measure per-tick error delta."""
    if not errors_text:
        return 0
    count = 0
    for ln in errors_text.splitlines():
        if re.search(r":\d+:\d+:", ln):
            count += 1
    return count


def _coerce_errors_text(errors: Any) -> str:
    """Normalize verify ``errors`` payload to a stable multi-line string."""
    if errors is None:
        return ""
    if isinstance(errors, str):
        return errors
    if isinstance(errors, list):
        lines: list[str] = []
        for item in errors:
            if isinstance(item, dict):
                lines.append(str(item.get("data", "")).strip())
            else:
                lines.append(str(item).strip())
        return "\n".join([ln for ln in lines if ln])
    return str(errors)


def _coerce_prompt_text(value: Any, fallback: str) -> str:
    """Normalize optional prompt fields to a guaranteed non-empty string."""
    if isinstance(value, str) and value.strip():
        return value
    return fallback if isinstance(fallback, str) else str(fallback or "")


def _resolve_decision_prompt(decision: Any, key: str, fallback: str) -> str:
    """Fetch optional prompt text from decision dict with None/empty safety."""
    if not isinstance(decision, dict):
        return _coerce_prompt_text(None, fallback)
    return _coerce_prompt_text(decision.get(key), fallback)


def _build_agent3_dispatch_brief(
    decision: dict[str, Any],
    *,
    error_subtype: str,
    repair_unit: str,
    target_region: str,
    current_errors: str,
) -> str:
    """Build a concise Agent3 brief from Agent8 metadata, not tactical protocol."""
    targeted_prompt = str(decision.get("targeted_prompt", "") or "").strip()
    reason = str(decision.get("reason", "") or "").strip()
    hypothesis = str(decision.get("hypothesis", "") or "").strip()
    evidence = _normalize_evidence(decision.get("evidence"))
    first_error = _extract_error_signature(current_errors)
    lines = [
        "[AGENT8 MODE-SELECTION BRIEF]",
        f"- error_subtype: {error_subtype or 'unknown'}",
        f"- repair_unit: {repair_unit or 'local_patch'}",
        f"- target_region: {target_region or 'unknown'}",
    ]
    allowed_edit_lines = str(decision.get("allowed_edit_lines", "") or "").strip()
    if allowed_edit_lines:
        lines.append(f"- allowed_edit_lines: {allowed_edit_lines}")
    if reason:
        lines.append(f"- policy_reason: {reason}")
    if hypothesis:
        lines.append(f"- hypothesis: {hypothesis}")
    if first_error:
        lines.append(f"- canonical_error: {first_error}")
    if targeted_prompt:
        lines.append(f"- diagnosis_brief: {targeted_prompt}")
    for idx, item in enumerate(evidence[:2], start=1):
        lines.append(
            f"- evidence_{idx}: {item.get('source', 'unknown')} :: {item.get('snippet', '')[:180]}"
        )
    lines.append(
        "- Agent8 selected the mode; Agent3 owns the tactical search/decomposition details."
    )
    return "\n".join(lines)


def _error_count_from_verify(verify_result: dict[str, Any], errors_text: str) -> int:
    """Get canonical error count from verify payload with text fallback."""
    try:
        if "error_count" in verify_result:
            return max(0, int(verify_result.get("error_count", 0)))
    except Exception:
        pass
    errs = verify_result.get("errors", [])
    if isinstance(errs, list):
        return len(errs)
    return _count_error_lines(errors_text)


def _normalize_error_signature(sig: str) -> str:
    """Normalize an error signature for stable cross-tick comparison."""
    if not sig:
        return ""
    # Remove obvious volatile fragments (line numbers, backticks, extra spaces).
    s = sig.lower()
    s = re.sub(r":\d+:\d+:", ":", s)
    s = s.replace("`", "").replace('"', "")
    s = re.sub(r"\s+", " ", s).strip()
    return s


def _signature_changed(errors_before: str, errors_after: str) -> bool:
    """Whether main error signature changed after dispatch."""
    _before = _normalize_error_signature(_extract_error_signature(errors_before))
    _after = _normalize_error_signature(_extract_error_signature(errors_after))
    if not _before and not _after:
        return False
    return _before != _after


_NETWORK_ERROR_MARKERS = (
    "remoteprotocolerror",
    "connectionerror",
    "connecttimeout",
    "readtimeout",
    "timeout",
    "temporarily unavailable",
    "connection reset",
)


def _is_network_error(text: str) -> bool:
    t = str(text).lower()
    return any(m in t for m in _NETWORK_ERROR_MARKERS)


def _compute_post_dispatch_observability(
    *,
    outcome: dict[str, Any],
    has_verified_after_state: bool,
    errors_before: str,
    errors_after_candidate: str,
    top_error_count_before: int,
    sorry_before: int,
    current_sorry_count: int,
) -> dict[str, Any]:
    """Compute coherent post-dispatch observability fields for one tick."""
    _dispatch_outcome = str(outcome.get("outcome", ""))
    _is_network = _dispatch_outcome == "network_failure"
    _is_dispatch_error = _dispatch_outcome == "dispatch_error"
    _verified = bool(has_verified_after_state) and not (_is_network or _is_dispatch_error)

    if _verified:
        errors_after = _coerce_errors_text(errors_after_candidate)
        top_error_count_after = int(
            outcome.get("error_count", _count_error_lines(errors_after))
        )
        error_count_delta = top_error_count_after - int(top_error_count_before)
        main_sig_changed = _signature_changed(errors_before, errors_after)
        sorry_after = int(outcome.get("sorry_count", current_sorry_count))
    else:
        errors_after = errors_before
        top_error_count_after = int(top_error_count_before)
        error_count_delta = 0
        main_sig_changed = False
        sorry_after = int(sorry_before)

    if _is_network:
        route_effective: bool | None = None
    elif not _verified:
        route_effective = False
    else:
        route_effective = (
            top_error_count_after < int(top_error_count_before)
            or main_sig_changed
        )

    return {
        "has_verified_after_state": _verified,
        "errors_after": errors_after,
        "top_error_count_after": top_error_count_after,
        "error_count_delta": error_count_delta,
        "main_error_signature_changed": main_sig_changed,
        "route_effective": route_effective,
        "sorry_after": sorry_after,
        "sorry_delta": sorry_after - int(sorry_before),
    }


def _has_informative_investigation(tool_names: list[Any]) -> bool:
    """True only when an informative investigation tool succeeded."""
    informative = {"read_file", "search_in_file", "search_codebase", "check_lean_expr"}
    for item in tool_names:
        if isinstance(item, dict):
            tool = str(item.get("tool", ""))
            success = bool(item.get("success"))
            if tool in informative and success:
                return True
            continue
        if str(item) in informative:
            return True
    return False


def _safe_llm_call(
    agent: "Agent",
    message: str,
    *,
    idempotent: bool = True,
    max_attempts: int = 3,
    base_sleep_s: float = 1.0,
) -> str:
    """Call agent with light retry for idempotent network failures only."""
    attempts = max(1, int(max_attempts))
    for i in range(1, attempts + 1):
        try:
            return agent.call(message)
        except Exception as exc:
            if not idempotent or not _is_network_error(str(exc)) or i >= attempts:
                raise
            _wait = base_sleep_s * (2 ** (i - 1))
            console.print(
                f"[yellow][Agent8] transient network error on call "
                f"({i}/{attempts}): {exc}. retrying in {_wait:.1f}s..."
            )
            time.sleep(_wait)
    # unreachable; keeps mypy happy
    return agent.call(message)


def _normalize_evidence(evidence: Any) -> list[dict]:
    """Normalize decision evidence to [{source, snippet}, ...]."""
    if not isinstance(evidence, list):
        return []
    out: list[dict] = []
    for item in evidence:
        if isinstance(item, dict):
            src = str(item.get("source", "")).strip()
            snip = str(item.get("snippet", "")).strip()
            if src and snip:
                out.append({"source": src, "snippet": snip})
        elif isinstance(item, str):
            txt = item.strip()
            if txt:
                out.append({"source": "unspecified", "snippet": txt})
    return out


def _evidence_hash(evidence: list[dict]) -> str:
    """Stable mini-hash for anti-loop grouping."""
    parts = [
        f"{e.get('source', '')}:{e.get('snippet', '')[:120]}"
        for e in evidence
    ]
    return "|".join(parts)[:500]


def _build_api_shape_contract(error_subtype: str, errors_text: str) -> str:
    """Build an API-shape repair contract to inject into Agent3's dispatch prompt.

    When the classified subtype indicates a proof-body API shape mismatch,
    this returns an explicit protocol block that forces Agent3 to:
    1. Look up the current signature of each failing lemma before patching.
    2. Construct a minimal diff matching the actual argument shape.
    3. Verify immediately after each edit.

    Returns empty string when not applicable.
    """
    if error_subtype != _SUBTYPE_PROOF_API_MISMATCH:
        return ""

    # Extract which API names appear in the error text for targeted lookup hints.
    hay = errors_text.lower()
    api_hints: list[str] = []
    for candidate in (
        "integral_nonneg", "integral_mono", "integral_add",
        "integral_sub", "integral_const_mul", "integral_const",
        "sum_range_succ", "sum_range_succ'", "finset.sum",
        "measure_theory",
    ):
        if candidate in hay:
            api_hints.append(f"`{candidate}`")

    hint_line = ""
    if api_hints:
        hint_line = (
            f"Failing APIs detected: {', '.join(api_hints[:5])}. "
            "Look up their current signatures first.\n"
        )

    return (
        "\n\n[API-SHAPE REPAIR CONTRACT — proof_api_mismatch]\n"
        f"{hint_line}"
        "Protocol (follow in order):\n"
        "  1. For EACH failing call site: issue search_in_file / search_codebase "
        "to retrieve the CURRENT signature (parameter count, implicit/explicit, binder order).\n"
        "  2. Compare actual vs expected: note exact arg count and which args are implicit {…} "
        "vs explicit (…).\n"
        "  3. Apply the MINIMAL patch — change only argument structure, not proof logic.\n"
        "  4. Run run_lean_verify immediately after each edit.\n"
        "  5. Fix at most 2 call sites per round; do not rewrite unrelated code.\n"
        "  6. Before signaling done, include a transaction_report with:\n"
        "     observed_signature, target_callsite, minimal_patch, verify_result.\n"
        "FORBIDDEN in this mode: guessing signatures from memory, introducing new theorems, "
        "large rewrites of proof bodies.\n"
    )


def _check_route_downweight(
    proposed_action: str,
    error_subtype: str,
    decision_history: "list[dict]",
    window: int = 3,
    *,
    compile_first_mode: bool = False,
    current_errors: str = "",
    target_region: str = "",
    allowed_edit_lines: str | None = None,
) -> tuple[str, str]:
    """Downweight a stale route if it produced no error-count improvement.

    Returns (action, override_reason).  When downweighting is not triggered,
    action equals proposed_action and override_reason is empty.

    Condition: same subtype + same action + all top_error_count_after >= before
    for the last *window* entries.
    """
    if (
        compile_first_mode
        and error_subtype == _SUBTYPE_PROOF_API_MISMATCH
        and proposed_action == "agent3_tactical"
        and not _proof_api_prefers_search_restructure(
            error_subtype=error_subtype,
            current_errors=current_errors,
            decision_history=decision_history,
            target_region=target_region,
            allowed_edit_lines=allowed_edit_lines,
        )
    ):
        return proposed_action, ""
    if len(decision_history) < window:
        return proposed_action, ""

    _recent = [
        e for e in decision_history[-window:]
        if e.get("outcome") != "network_failure"
    ]
    if len(_recent) < window:
        return proposed_action, ""
    _matching = [
        e for e in _recent
        if e.get("action") == proposed_action
        and e.get("error_subtype", "") == error_subtype
        and e.get("route_effective") is False
    ]
    if len(_matching) >= window:
        _reason = (
            f"action='{proposed_action}' with subtype='{error_subtype}' made zero "
            f"error-count progress across last {window} ticks — downweighting."
        )
        # Select next best action based on subtype
        _fallback = {
            _SUBTYPE_DECLARATION_SYNTAX_FAILURE: "agent3_tactical",
            _SUBTYPE_PROOF_API_MISMATCH: "agent7_signature",
            _SUBTYPE_DECLARATION_API_MISMATCH: "agent3_tactical",
            _SUBTYPE_PROOF_TACTIC_FAILURE: (
                "apollo_decompose_repair"
                if AGENT8_APOLLO_DECOMPOSE_ENABLED
                else "agent9_replan"
            ),
            _SUBTYPE_STRATEGY_MISMATCH: "human_missing_assumption",
        }.get(error_subtype, "agent9_replan")
        if _fallback == proposed_action:
            _fallback = "agent9_replan"
        return _fallback, _reason

    return proposed_action, ""


def _apply_subtype_route_policy(
    proposed_action: str,
    error_subtype: str,
    decision_history: list[dict],
) -> tuple[str, str, str, bool]:
    """Subtype-aware route policy with explicit first-try stage for declaration syntax.

    Returns (action, policy_stage, reason, forced_lock).
    """
    if error_subtype != _SUBTYPE_DECLARATION_SYNTAX_FAILURE:
        return proposed_action, "none", "", False

    same_subtype_history = [
        e
        for e in decision_history
        if e.get("error_subtype") == _SUBTYPE_DECLARATION_SYNTAX_FAILURE
    ]
    prior_agent7_attempts = sum(
        1
        for e in same_subtype_history
        if e.get("action") == "agent7_signature"
    )

    if prior_agent7_attempts == 0:
        # First shot keeps signature audit for conservative diagnosis.
        if proposed_action != "agent7_signature":
            return (
                "agent7_signature",
                "first_try_agent7",
                "declaration_syntax_failure first attempt uses agent7_signature.",
                False,
            )
        return proposed_action, "first_try_agent7", "", False

    if proposed_action == "agent7_signature":
        return (
            "agent3_tactical",
            "forced_to_agent3",
            "declaration_syntax_failure persisted after initial agent7 attempt.",
            True,
        )
    if proposed_action == "agent9_replan":
        return (
            "agent3_tactical",
            "forced_to_agent3",
            "declaration_syntax_failure prefers tactical syntax patch before replan.",
            True,
        )
    return proposed_action, "forced_to_agent3", "", False


def _apply_network_cooldown_fallback(
    proposed_action: str,
    error_subtype: str,
    decision_history: list[dict],
    action_cooldowns: dict[str, int],
    *,
    cooldown_ticks: int = 2,
) -> tuple[str, str, bool]:
    """If last tick had agent7 network/dispatch failure, cooldown agent7 and prefer agent3."""
    if error_subtype not in (
        _SUBTYPE_DECLARATION_SYNTAX_FAILURE,
        _SUBTYPE_DECLARATION_API_MISMATCH,
    ):
        return proposed_action, "", False
    if not decision_history:
        return proposed_action, "", False

    last = decision_history[-1]
    if (
        last.get("action") == "agent7_signature"
        and last.get("outcome") in {"network_failure", "dispatch_error"}
    ):
        action_cooldowns["agent7_signature"] = max(
            int(action_cooldowns.get("agent7_signature", 0)),
            max(1, int(cooldown_ticks)),
        )
        if proposed_action == "agent7_signature":
            return (
                "agent3_tactical",
                "network_cooldown: prior agent7 dispatch/network failure; forcing agent3_tactical.",
                True,
            )
        return proposed_action, "network_cooldown applied to agent7_signature.", True

    return proposed_action, "", False


def _apply_compile_first_subtype_gate(
    action: str,
    error_subtype: str,
    targeted_prompt: str,
    *,
    forced_route_lock: bool,
    current_errors: str = "",
    decision_history: list[dict] | None = None,
    target_region: str = "",
    allowed_edit_lines: str | None = None,
) -> tuple[str, str, str]:
    """Apply compile-first subtype policy unless force-lock is active."""
    if forced_route_lock:
        return action, targeted_prompt, ""

    _history = decision_history or []
    if error_subtype == _SUBTYPE_PROOF_API_MISMATCH:
        if _proof_api_prefers_search_restructure(
            error_subtype=error_subtype,
            current_errors=current_errors,
            decision_history=_history,
            target_region=target_region,
            allowed_edit_lines=allowed_edit_lines,
        ):
            if action == "agent7_signature":
                action = "agent3_tactical"
            targeted_prompt = (
                "[compile-first/proof_api_mismatch] Treat this as a proof-block "
                "shape failure. Prefer APOLLO sampled search, decomposition, or "
                "block-restructure over repeated transactional micro-patches.\n\n"
                + targeted_prompt
            )
            return action, targeted_prompt, "proof_api_mismatch -> sampled_search_or_restructure"
        if action not in ("agent3_tactical", "human_missing_assumption"):
            action = "agent3_tactical"
            targeted_prompt = (
                "[compile-first/proof_api_mismatch] Fix proof-body API shape "
                "error: look up the target lemma's current signature first, "
                "then apply a minimal patch matching actual arg count/order. "
                "Verify after each edit.\n\n"
                + targeted_prompt
            )
            return action, targeted_prompt, "proof_api_mismatch -> agent3_tactical"
    if error_subtype == _SUBTYPE_DECLARATION_API_MISMATCH and action == "agent9_replan":
        action = "agent7_signature"
        targeted_prompt = (
            "[compile-first/declaration_api_mismatch] Fix declaration-zone "
            "API/signature mismatch before replanning strategy.\n\n"
            + targeted_prompt
        )
        return action, targeted_prompt, "declaration_api_mismatch -> agent7_signature"
    if action == "agent9_replan" and error_subtype not in (
        _SUBTYPE_STRATEGY_MISMATCH,
    ):
        action = "agent7_signature"
        targeted_prompt = (
            "[compile-first guard] Focus on declaration/API/type alignment. "
            "Do not replan mathematical strategy in this tick.\n\n"
            + targeted_prompt
        )
        return action, targeted_prompt, "compile-first guard -> agent7_signature"

    return action, targeted_prompt, ""


def _apply_hard_route_gate(
    proposed_action: str,
    error_subtype: str,
    decision_history: "list[dict]",
    action_cooldowns: dict[str, int],
    *,
    window: int = 3,
    cooldown_ticks: int = 2,
    compile_first_mode: bool = False,
    current_errors: str = "",
    target_region: str = "",
    allowed_edit_lines: str | None = None,
) -> tuple[str, str]:
    """Hard gate: force route switch on repeated no-delta, with cooldown."""
    if (
        compile_first_mode
        and error_subtype == _SUBTYPE_PROOF_API_MISMATCH
        and proposed_action == "agent3_tactical"
        and not _proof_api_prefers_search_restructure(
            error_subtype=error_subtype,
            current_errors=current_errors,
            decision_history=decision_history,
            target_region=target_region,
            allowed_edit_lines=allowed_edit_lines,
        )
    ):
        return proposed_action, ""
    # 1) Cooldown block (prevents immediate oscillation).
    if action_cooldowns.get(proposed_action, 0) > 0:
        fallback, _ = _check_route_downweight(
            proposed_action,
            error_subtype,
            decision_history,
            window=max(2, window),
            compile_first_mode=compile_first_mode,
            current_errors=current_errors,
            target_region=target_region,
            allowed_edit_lines=allowed_edit_lines,
        )
        if fallback == proposed_action:
            fallback = "agent9_replan"
        return (
            fallback,
            f"hard_gate cooldown blocks action='{proposed_action}' "
            f"for {action_cooldowns.get(proposed_action, 0)} more tick(s).",
        )

    # 2) Repeated no-delta condition.
    fallback, reason = _check_route_downweight(
        proposed_action,
        error_subtype,
        decision_history,
        window=window,
        compile_first_mode=compile_first_mode,
        current_errors=current_errors,
        target_region=target_region,
        allowed_edit_lines=allowed_edit_lines,
    )
    if reason:
        action_cooldowns[proposed_action] = max(1, int(cooldown_ticks))
        return fallback, "hard_gate " + reason

    return proposed_action, ""


def _route_streak_len(decision_history: list[dict], action: str) -> int:
    """Return contiguous same-action streak length from history tail."""
    streak = 0
    for entry in reversed(decision_history):
        if entry.get("action") == action:
            streak += 1
        else:
            break
    return streak


def _is_no_progress_entry(entry: dict) -> bool:
    """No-progress rule: delta>=0 and main signature unchanged."""
    try:
        delta = int(entry.get("error_count_delta", 0))
    except Exception:
        delta = 0
    sig_changed = bool(entry.get("main_error_signature_changed", False))
    return delta >= 0 and not sig_changed


def _apply_delta_force_fallback(
    proposed_action: str,
    decision_history: list[dict],
    action_cooldowns: dict[str, int],
    *,
    error_subtype: str = "",
    compile_first_mode: bool = False,
    window: int = 2,
    cooldown_ticks: int = 2,
    current_errors: str = "",
    target_region: str = "",
    allowed_edit_lines: str | None = None,
) -> tuple[str, str]:
    """Force fallback chain under explicit two-tick no-progress rule.

    Rule:
    - agent3_tactical no-progress(window) -> agent7_signature
    - agent7_signature no-progress(window) -> agent9_replan
    """
    if (
        compile_first_mode
        and error_subtype == _SUBTYPE_PROOF_API_MISMATCH
        and proposed_action == "agent3_tactical"
        and not _proof_api_prefers_search_restructure(
            error_subtype=error_subtype,
            current_errors=current_errors,
            decision_history=decision_history,
            target_region=target_region,
            allowed_edit_lines=allowed_edit_lines,
        )
    ):
        return proposed_action, ""
    if proposed_action not in ("agent3_tactical", "agent7_signature"):
        return proposed_action, ""
    same_action_recent = [
        e for e in reversed(decision_history) if e.get("action") == proposed_action
    ]
    if len(same_action_recent) < max(1, window):
        return proposed_action, ""
    check_slice = same_action_recent[:window]
    if not all(_is_no_progress_entry(e) for e in check_slice):
        return proposed_action, ""

    forced = "agent7_signature" if proposed_action == "agent3_tactical" else "agent9_replan"
    action_cooldowns[proposed_action] = max(1, int(cooldown_ticks))
    return (
        forced,
        (
            f"delta_force_fallback: action='{proposed_action}' had "
            f"{window} consecutive no-progress ticks "
            "(delta>=0 and normalized-signature unchanged)"
        ),
    )


def _apollo_fallback_from_failure_kind(failure_kind: str) -> str:
    """Map APOLLO failure classification to deterministic next route."""
    return {
        "interface_failure": "agent7_signature",
        "instance_failure": "agent7_signature",
        "glue_failure": "agent7_then_agent6",
        "strategy_failure": "agent9_replan",
    }.get(failure_kind, "agent9_replan")


def _should_prefer_apollo_decompose(
    proposed_action: str,
    error_signature: str,
    decision_history: list[dict],
    blocked_sorry_count: int,
    action_cooldowns: dict[str, int],
    *,
    error_subtype: str = "",
    compile_first_mode: bool = False,
    current_errors: str = "",
    target_region: str = "",
    allowed_edit_lines: str | None = None,
) -> tuple[bool, str]:
    """Policy gate for when Agent8 should prefer APOLLO decomposition route.

    Primary trigger (prompt-aligned): if error signature is unchanged across the
    last N ticks (default N=2), prefer ``apollo_decompose_repair``.
    """
    if not AGENT8_APOLLO_DECOMPOSE_ENABLED:
        return False, ""
    if (
        compile_first_mode
        and error_subtype == _SUBTYPE_PROOF_API_MISMATCH
        and proposed_action == "agent3_tactical"
        and not _proof_api_prefers_search_restructure(
            error_subtype=error_subtype,
            current_errors=current_errors,
            decision_history=decision_history,
            target_region=target_region,
            allowed_edit_lines=allowed_edit_lines,
        )
    ):
        return False, ""
    if proposed_action in ("human_missing_assumption", "apollo_decompose_repair"):
        return False, ""
    if int(action_cooldowns.get("apollo_decompose_repair", 0)) > 0:
        return False, ""

    sig_window = max(1, RETRY_LIMITS.get("AGENT8_APOLLO_SAME_ERROR_WINDOW", 2))
    no_progress_window = max(1, RETRY_LIMITS.get("AGENT8_APOLLO_NO_PROGRESS_WINDOW", 2))
    blocked_threshold = max(1, RETRY_LIMITS.get("AGENT8_APOLLO_BLOCKED_SORRY_THRESHOLD", 1))

    reasons: list[str] = []
    normalized_sig = _normalize_error_signature(error_signature)
    _recent = [e for e in decision_history if e.get("outcome") != "network_failure"]
    if normalized_sig and len(_recent) >= sig_window:
        _tail = _recent[-sig_window:]
        if all(
            _normalize_error_signature(str(e.get("error_signature", ""))) == normalized_sig
            for e in _tail
        ):
            reasons.append(f"error_signature unchanged for {sig_window} consecutive ticks")

    if blocked_sorry_count >= blocked_threshold:
        reasons.append(
            f"blocked_sorry_count={blocked_sorry_count} >= threshold({blocked_threshold})"
        )

    if len(_recent) >= no_progress_window and all(
        _is_no_progress_entry(e) for e in _recent[-no_progress_window:]
    ):
        reasons.append(f"no-progress persisted for {no_progress_window} ticks")

    if reasons:
        return True, "; ".join(reasons)
    return False, ""


def _subproblem_kind_to_action(kind: str) -> str:
    """Deterministic serial dispatch mapping for APOLLO subproblem nodes."""
    return {
        "interface_signature": "agent7_signature",
        "proof_api_shape": "agent3_tactical",
        "proof_state_sublemma": "agent3_tactical",
        "missing_glue": "agent7_then_agent6",
        "local_tactic_repair": "agent3_tactical",
        "global_strategy": "agent9_replan",
        "assumption_gap": "human_missing_assumption",
    }.get(kind, "agent9_replan")


def _subproblem_kind_fallback_action(kind: str) -> str:
    """Fallback when a serial subproblem node exceeds its retry budget."""
    return {
        "interface_signature": "agent7_then_agent6",
        "proof_api_shape": "agent7_signature",
        "proof_state_sublemma": "agent9_replan",
        "missing_glue": "agent9_replan",
        "local_tactic_repair": "agent9_replan",
        "global_strategy": "human_missing_assumption",
        "assumption_gap": "human_missing_assumption",
    }.get(kind, "agent9_replan")


_DECL_SIGNATURE_RE = re.compile(
    r"^\s*(?:theorem|lemma|noncomputable\s+def|def)\s+\w+[^\n]*$",
    re.MULTILINE,
)


def _extract_decl_signatures(text: str) -> list[str]:
    """Extract normalized declaration header lines for signature stability checks."""
    return [m.group(0).strip() for m in _DECL_SIGNATURE_RE.finditer(text or "")]


def _estimate_patch_line_span(old_str: str, new_str: str) -> int:
    """Estimate patch line span from old/new replacement blocks."""
    old_n = len((old_str or "").splitlines()) or 1
    new_n = len((new_str or "").splitlines()) or 1
    return max(old_n, new_n)


def _patch_touches_decl_signature(old_str: str, new_str: str) -> bool:
    """Detect whether patch blocks contain declaration signature edits."""
    old_has = bool(_DECL_SIGNATURE_RE.search(old_str or ""))
    new_has = bool(_DECL_SIGNATURE_RE.search(new_str or ""))
    return old_has or new_has


def _sha256_text(content: str) -> str:
    """Return sha256 digest for text content."""
    return hashlib.sha256((content or "").encode("utf-8")).hexdigest()


def _parse_allowed_edit_lines(allowed_edit_lines: str | None) -> tuple[int, int] | None:
    """Parse Agent8 line-span text into inclusive bounds."""
    if allowed_edit_lines is None:
        return None
    raw = str(allowed_edit_lines).strip()
    if not raw:
        return None
    match = re.fullmatch(r"(\d+)(?:\s*-\s*(\d+))?", raw)
    if not match:
        raise ValueError(f"invalid allowed_edit_lines: {allowed_edit_lines!r}")
    start = int(match.group(1))
    end = int(match.group(2) or match.group(1))
    if start <= 0 or end <= 0 or start > end:
        raise ValueError(f"invalid allowed_edit_lines: {allowed_edit_lines!r}")
    return start, end


def _read_span_snippet(content: str, allowed_edit_lines: str | None) -> str:
    """Extract the current active span snippet for anchor/hash binding."""
    span = _parse_allowed_edit_lines(allowed_edit_lines)
    if span is None:
        return content
    lines = content.splitlines()
    if span[0] > len(lines):
        raise ValueError(
            f"allowed_edit_lines out of range: {allowed_edit_lines!r} for file with {len(lines)} line(s)"
        )
    end = min(len(lines), span[1])
    return "\n".join(lines[span[0] - 1 : end])


def _build_active_target(
    target_file: str,
    *,
    candidate_id: str,
    allowed_edit_lines: str | None,
    decl_name: str = "",
) -> dict[str, Any]:
    """Build the canonical active-target object used by Agent8/Agent3."""
    content = load_file(target_file)
    anchor_text = _read_span_snippet(content, allowed_edit_lines) if allowed_edit_lines else ""
    return {
        "source_file": target_file,
        "candidate_file": target_file,
        "decl_name": decl_name or "",
        "candidate_id": candidate_id or "",
        "allowed_span": allowed_edit_lines,
        "anchor_text": anchor_text,
        "anchor_hash": _sha256_text(anchor_text) if anchor_text else _sha256_text(content),
        "file_hash": _sha256_text(content),
    }


# ---------------------------------------------------------------------------
# Context builder for each Agent8 tick
# ---------------------------------------------------------------------------

def _build_agent8_tick_context(
    target_file: str,
    errors_text: str,
    agent2_plan: str,
    decision_history: list[dict],
    agent9_plan: dict | None = None,
    plan_updated_tick: int = 0,
    midcheck_mode: bool = False,
    midcheck_turns_elapsed: int = 0,
    pending_lemma_status: dict | None = None,
    baseline_errors: str = "",
    error_subtype: str = "",
    canonical_error_signature: str = "",
    stale_error_hint: str = "",
    reset_hypothesis_bias: bool = False,
    verify_backend_used: str = "",
    verify_backend_reason: str = "",
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
            elif (_delta is not None and _delta < 0) or bool(entry.get("main_error_signature_changed", False)):
                _outcome_tag = "[PROGRESS]"
            else:
                _outcome_tag = "[FAIL]"
            history_lines.append(
                f"  tick {entry['tick']} {_outcome_tag}: action={entry['action']}, "
                f"repair_unit={entry.get('repair_unit', '?')}, "
                f"target={entry.get('target_theorem', '?')}, "
                f"region={entry.get('target_region', '?')}, "
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
            "appropriate agent (agent7_signature, agent7_then_agent6, "
            "apollo_decompose_repair, or agent9_replan).\n"
            "Avoid agent9_replan unless truly necessary — prefer agent7 or agent3_tactical.\n\n"
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
            "NOTE: Agent9 is a non-binding prior. Prefer current compile evidence on conflicts.\n"
            f"```json\n{_a9_text[:_a9_chars]}\n```\n\n"
        )

    # Pending lemma status block — shows per-lemma progress for sorry-only ticks.
    _pending_lemma_block = ""
    if pending_lemma_status:
        _status_lines = [
            f"  {name}: {info.get('status', '?')} "
            f"(attempts={info.get('attempts', 0)})"
            for name, info in pending_lemma_status.items()
        ]
        _pending_lemma_block = (
            "## Pending Lemma Status\n"
            + "\n".join(_status_lines)
            + "\n\n"
        )

    # Baseline errors block: shown only when available and different from current errors.
    _baseline_block = ""
    if baseline_errors and baseline_errors.strip():
        _baseline_block = (
            "## Baseline Errors (BEFORE Agent3 started this attempt)\n"
            "These errors existed BEFORE Agent3 ran. They are the root cause to fix.\n"
            "```\n"
            f"{baseline_errors[:_err_chars]}\n"
            "```\n"
            "## Current Build Errors (AFTER Agent3 attempts)\n"
            "Compare with baseline to identify errors Agent3 introduced vs. pre-existing.\n"
            "**Route Agent7 to fix pre-existing (baseline) API errors, NOT Agent3-introduced errors.**\n"
            "**If a line that was clean in the baseline now has errors, Agent3 introduced them —\n"
            "prefer agent3_tactical or a rollback + replan rather than agent7_signature for those.**\n"
        )
    else:
        _baseline_block = "## Build Errors\n"

    _api_shape_hints = []
    _hay = errors_text.lower()
    if "integral_" in _hay:
        _api_shape_hints.append(
            "- For integral lemmas, verify current signature shape (implicit/explicit args, binder order) via search_in_file before editing."
        )
    if "sum_range" in _hay or "finset.sum" in _hay:
        _api_shape_hints.append(
            "- For Finset sums, verify exact rewrite lemma variant (`sum_range_succ`, `sum_range_succ'`, subtraction forms) in current Mathlib."
        )
    if "type mismatch" in _hay or "failed to synthesize" in _hay:
        _api_shape_hints.append(
            "- For mismatches, include API-shape evidence: expected type vs actual type and argument position."
        )
    _api_shape_block = ""
    if _api_shape_hints:
        _api_shape_block = "## API Shape Checklist\n" + "\n".join(_api_shape_hints) + "\n\n"

    # Subtype classification block (computed by caller and passed in)
    _subtype_block = ""
    if error_subtype:
        _subtype_routing = {
            _SUBTYPE_DECLARATION_SYNTAX_FAILURE: "→ Preferred action: agent7_signature (first attempt), then agent3_tactical if no-progress/network stall",
            _SUBTYPE_DECLARATION_API_MISMATCH: "→ Preferred action: agent7_signature (declaration zone fix)",
            _SUBTYPE_PROOF_API_MISMATCH:       "→ Preferred action: agent3_tactical (proof-body API shape patch; lookup signature first)",
            _SUBTYPE_PROOF_TACTIC_FAILURE:     "→ Preferred action: agent3_tactical (tactic / lemma name fix)",
            _SUBTYPE_STRATEGY_MISMATCH:        "→ Preferred action: agent9_replan (mathematical approach needs revision)",
        }.get(error_subtype, "")
        _subtype_block = (
            f"## Error Subtype (pre-classified)\n"
            f"Subtype: `{error_subtype}`\n"
            f"{_subtype_routing}\n"
            "This is a heuristic signal — override with compile evidence if conflicting.\n\n"
        )

    _canonical_block = ""
    if canonical_error_signature:
        _canonical_block = (
            "## Canonical Current Error (verifier-derived)\n"
            f"`{canonical_error_signature}`\n"
            "Treat this as the source of truth for routing and anti-loop logic.\n\n"
        )

    _reset_block = ""
    if reset_hypothesis_bias:
        _reset_block = (
            "## Hypothesis Reset\n"
            "The canonical primary error changed across recent ticks. Discard stale root-cause "
            "stories and re-diagnose from the current verifier output only.\n\n"
        )

    _stale_block = ""
    if stale_error_hint:
        _stale_block = f"{stale_error_hint}\n"

    _backend_block = ""
    if verify_backend_used or verify_backend_reason:
        _backend_block = (
            "## Verifier Backend\n"
            f"backend_used: `{verify_backend_used or 'unknown'}`\n"
            f"backend_reason: `{verify_backend_reason or 'unknown'}`\n\n"
        )

    return (
        f"{_midcheck_banner}"
        f"{_new_plan_banner}"
        f"{_reset_block}"
        "## Current Algorithm File (smart-truncated around error lines)\n"
        f"File: {target_file}\n"
        f"```lean\n{algo_display}\n```\n\n"
        f"{_baseline_block}"
        f"```\n{errors_text[:_err_chars]}\n```\n\n"
        f"{_canonical_block}"
        f"{_backend_block}"
        f"## Proof Plan (current)\n{agent2_plan[:_plan_chars]}\n\n"
        f"## Library Files Available\n{lib_desc}\n\n"
        f"{_a9_block}"
        f"{_subtype_block}"
        f"{_api_shape_block}"
        f"{_stale_block}"
        f"{_pending_lemma_block}"
        f"## Decision History (recent)\n{history_block}\n\n"
        f"{dep_sigs}"
        f"{algo_sigs}\n\n"
        "Analyze the errors and produce a single JSON decision following the "
        "priority rules in your system prompt."
    )


# ---------------------------------------------------------------------------
# JSON decision parser with retry logic
# ---------------------------------------------------------------------------

_VALID_ACTIONS = AGENT8_VALID_ACTIONS

_REQUIRED_DECISION_FIELDS = AGENT8_REQUIRED_DECISION_FIELDS

_VALID_ERROR_SUBTYPES = AGENT8_VALID_ERROR_SUBTYPES
_VALID_REPAIR_UNITS = AGENT8_VALID_REPAIR_UNITS
_VALID_BLOCKER_STATUSES = AGENT8_VALID_BLOCKER_STATUSES


def _validate_agent8_decision_schema(obj: dict) -> tuple[bool, str]:
    """Strict schema gate for evidence-driven Agent8 decisions."""
    missing = sorted(_REQUIRED_DECISION_FIELDS - set(obj.keys()))
    if missing:
        return False, f"missing required fields: {missing}"
    if obj.get("action") not in _VALID_ACTIONS:
        return False, f"invalid action: {obj.get('action')}"
    # error_subtype is optional but must be a valid value when present
    if "error_subtype" in obj and obj["error_subtype"] not in _VALID_ERROR_SUBTYPES:
        return False, f"invalid error_subtype: {obj.get('error_subtype')!r}"
    if "repair_unit" in obj and obj["repair_unit"] not in _VALID_REPAIR_UNITS:
        return False, f"invalid repair_unit: {obj.get('repair_unit')!r}"
    if "blocker_status" in obj and obj["blocker_status"] not in _VALID_BLOCKER_STATUSES:
        return False, f"invalid blocker_status: {obj.get('blocker_status')!r}"
    if not str(obj.get("hypothesis", "")).strip():
        return False, "hypothesis must be non-empty"
    evidence = _normalize_evidence(obj.get("evidence"))
    if len(evidence) < 2:
        return False, "evidence must contain at least 2 entries with source+snippet"
    obj["evidence"] = evidence
    try:
        conf = float(obj.get("confidence"))
    except Exception:
        return False, "confidence must be a number in [0,1]"
    if conf < 0.0 or conf > 1.0:
        return False, "confidence must be in [0,1]"
    obj["confidence"] = conf
    obj["targeted_prompt"] = _coerce_prompt_text(obj.get("targeted_prompt"), "")
    if not str(obj.get("counterfactual", "")).strip():
        return False, "counterfactual must be non-empty"
    return True, ""


def _parse_agent8_decision(raw_reply: str) -> tuple[dict | None, str]:
    """Parse and validate Agent8 JSON decision."""
    for candidate in _json_candidates(raw_reply.strip()):
        try:
            obj = json.loads(candidate)
        except json.JSONDecodeError:
            continue
        if isinstance(obj, dict):
            ok, reason = _validate_agent8_decision_schema(obj)
            if ok:
                return obj, ""
            return None, reason
    # Fallback: try the whole reply as JSON
    try:
        obj = json.loads(raw_reply.strip())
        if isinstance(obj, dict):
            ok, reason = _validate_agent8_decision_schema(obj)
            if ok:
                return obj, ""
            return None, reason
    except json.JSONDecodeError:
        pass
    return None, "response is not valid JSON"


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

    Field access is normalised: lean_statement_line falls back to line_number,
    estimated_difficulty falls back to difficulty, dependencies falls back to
    depends_on — to stay compatible across plan schema versions.
    """
    if not agent9_plan or not target_theorem:
        return ""
    for thm in agent9_plan.get("theorems", []):
        if thm.get("name") == target_theorem:
            # Normalise line-number field (prefer lean_statement_line, fall back
            # to legacy line_number used by some older plan versions).
            _line = thm.get("lean_statement_line", thm.get("line_number", "?"))
            _deps = thm.get("dependencies", thm.get("depends_on", []))
            _diff = thm.get("estimated_difficulty", thm.get("difficulty", "unknown"))
            _mgl = thm.get("missing_glue_lemmas", [])
            _dep_map = thm.get("dependency_map", {})

            # Format missing_glue_lemmas compactly for Agent3 readability.
            if isinstance(_mgl, list) and _mgl:
                _mgl_lines = []
                for entry in _mgl:
                    if isinstance(entry, dict):
                        _mgl_lines.append(
                            f"    • {entry.get('name', '?')}: "
                            f"{entry.get('proposed_lean_type', '(no type)')}"
                        )
                    else:
                        _mgl_lines.append(f"    • {entry}")
                _mgl_block = "[\n" + "\n".join(_mgl_lines) + "\n  ]"
            else:
                _mgl_block = "[]"

            lines = [
                f"\n\n## Agent9 Strategy for `{target_theorem}`",
                f"- lean_statement_line: {_line}",
                f"- proof_technique: {thm.get('proof_technique', 'unknown')}",
                f"- estimated_difficulty: {_diff}",
                f"- depends_on: {_deps}",
                f"- key_lib_lemmas: {thm.get('key_lib_lemmas', [])}",
                f"- missing_glue_lemmas: {_mgl_block}",
                f"- dependency_map: {_dep_map}",
                "- NOTE: Agent9 guidance is NON-BINDING; compile evidence takes precedence.",
                "- proof_strategy (EXECUTABLE REFERENCE):",
                f"  {thm.get('proof_strategy', 'N/A')}",
            ]
            return "\n".join(lines) + "\n"
    return ""


# ---------------------------------------------------------------------------
# Dispatch: Agent3 tactical fix
# ---------------------------------------------------------------------------

def _agent8_result_score(result: dict[str, Any]) -> tuple[int, int, int, int]:
    """Lower score is better for APOLLO-aligned candidate selection."""
    exit_code = int(result.get("exit_code", 1))
    sorry_count = int(result.get("sorry_count", 10**6))
    err_text = str(result.get("errors", "") or "")
    err_count = len([ln for ln in err_text.splitlines() if ln.strip()])
    is_clean = int(not (exit_code == 0 and sorry_count == 0))
    return (is_clean, max(0, sorry_count), err_count, int(exit_code != 0))


def _agent8_run_agent3_single(
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
    repair_unit: str = _REPAIR_UNIT_LOCAL_PATCH,
    target_region: str = "",
    candidate_index: int = 1,
    candidate_total: int = 1,
    candidate_id: str | None = None,
    decl_name: str = "",
) -> dict:
    """Run a fresh Agent3 with a targeted prompt and simplified tool loop.

    Returns {"exit_code": int, "sorry_count": int, "errors": str}.
    """
    max_turns = max_turns or RETRY_LIMITS.get("AGENT8_AGENT3_MAX_TURNS", 15)
    if transactional_mode and not patch_guard_mode:
        patch_guard_mode = True
    _ = search_allowed
    from orchestrator.apollo_repair import classify_failure_kind

    agent3 = Agent("sorry_closer", extra_files=[target_file])
    registry = ToolRegistry()
    registry.register_default_tools()
    algo_name = Path(target_file).stem
    _candidate_started = time.perf_counter()

    # Write full Agent2 plan to a temp file so Agent3 can read it without truncation
    plan_file = Path(tempfile.gettempdir()) / f"agent8_plan_{algo_name}.md"
    plan_file.write_text(agent2_plan, encoding="utf-8")

    _candidate_label = str(candidate_id or f"c{candidate_index}")
    try:
        _initial_active_target = _build_active_target(
            target_file,
            candidate_id=_candidate_label,
            allowed_edit_lines=allowed_edit_lines,
            decl_name=decl_name,
        )
    except Exception as exc:
        return {
            "exit_code": 1,
            "sorry_count": -1,
            "errors": f"active_target_bind_failed: {exc}",
            "candidate_id": _candidate_label,
            "active_target": {
                "candidate_file": target_file,
                "candidate_id": _candidate_label,
                "allowed_span": allowed_edit_lines,
                "decl_name": decl_name or "",
            },
        }

    scope_instruction = ""
    if allowed_edit_lines:
        scope_instruction = (
            f"\n\nSCOPE CONSTRAINT: You may ONLY edit lines {allowed_edit_lines} "
            "of the target file. Do not modify code outside this range."
        )

    transactional_instruction = ""
    if patch_guard_mode:
        transactional_instruction = (
            "\n\nTRANSACTIONAL EXECUTION CONTRACT (STRICT):\n"
            "1) Before patching API-lemma calls, lookup and confirm current signature.\n"
            "2) Keep edits minimal (1-2 callsites only).\n"
            "3) Run run_lean_verify after edits.\n"
            "4) When signaling done, arguments MUST include:\n"
            "   {\"transaction_report\": {\n"
            "      \"observed_signature\": \"...\",\n"
            "      \"target_callsite\": \"file:line expr\",\n"
            "      \"minimal_patch\": \"what exactly changed\",\n"
            "      \"verify_result\": \"exit/sorry/errors summary\"\n"
            "   }}\n"
            "If any field is missing, done will be rejected."
        )

    _sampling_hint = ""
    if candidate_total > 1:
        _sampling_hint = (
            "\n\nSAMPLING CANDIDATE MODE:\n"
            f"- You are candidate {candidate_index}/{candidate_total}.\n"
            "- Use a distinct tactical angle from generic simp-first attempts.\n"
            "- Keep edits minimal and verifiable.\n"
            "- Prioritize compile evidence over stylistic changes."
        )
    _mode_banner = "Block Restructure" if repair_unit == _REPAIR_UNIT_BLOCK_RESTRUCTURE else "Tactical Fix"
    initial_msg = (
        f"[AGENT8 DISPATCH — {_mode_banner}]\n\n"
        f"{targeted_prompt}\n\n"
        f"The full proof plan is available at: {plan_file}\n"
        f"(Read it with read_file if you need the complete mathematical strategy.)\n"
        f"Target file: {target_file}\n"
        f"Repair unit: {repair_unit}\n"
        f"Target region: {target_region or allowed_edit_lines or 'unknown'}\n"
        f"Active target object: {json.dumps(_initial_active_target, ensure_ascii=False)}\n"
        f"{scope_instruction}\n\n"
        f"{transactional_instruction}\n\n"
        f"{_sampling_hint}\n\n"
        "Fix the specified error. When done, signal tool=done. "
        "Output ONE JSON action per response: {{thought, tool, arguments}}."
    )

    _edit_calls = 0
    _verify_snapshots: list[dict] = []
    _last_observed_signature = ""
    _last_callsite = ""
    _candidate_metrics: dict[str, Any] = {
        "llm_ms": 0,
        "tool_ms": 0,
        "verify_ms": 0,
        "llm_calls": 0,
        "tool_calls": 0,
        "verify_calls": 0,
        "turn_count": 0,
    }
    _max_patch_lines = int(
        RETRY_LIMITS.get(
            "AGENT8_BLOCK_RESTRUCTURE_MAX_PATCH_LINES",
            160 if repair_unit == _REPAIR_UNIT_BLOCK_RESTRUCTURE else RETRY_LIMITS.get("AGENT8_MAX_PATCH_LINES", 60),
        )
    )
    _decl_snapshot = _extract_decl_signatures(load_file(target_file))

    def _call_agent3(msg: str) -> str:
        _start = time.perf_counter()
        reply = agent3.call(msg)
        _candidate_metrics["llm_ms"] += int((time.perf_counter() - _start) * 1000.0)
        _candidate_metrics["llm_calls"] += 1
        return reply

    def _blocked_state(errors_text: str, failure_kind: str = "") -> dict[str, Any]:
        _kind, _reason, _snippet = classify_failure_kind(errors_text)
        if failure_kind:
            _kind = failure_kind
        return {
            "failure_kind": _kind,
            "classifier_reason": _reason,
            "observed_signature": _snippet or _extract_error_signature(errors_text),
            "target_region": target_region or allowed_edit_lines or "unknown",
            "candidate_id": _candidate_label,
            "route_hint": {
                "interface_failure": "agent7_signature",
                "instance_failure": "agent7_signature",
                "glue_failure": "agent7_then_agent6",
                "strategy_failure": "agent3_tactical",
            }.get(_kind, "agent3_tactical"),
        }

    raw_reply = _call_agent3(initial_msg)

    for turn in range(max_turns):
        _candidate_metrics["turn_count"] += 1
        try:
            payload = json.loads(raw_reply)
        except json.JSONDecodeError:
            raw_reply = _call_agent3(
                "Invalid JSON. Return valid JSON: {thought, tool, arguments}."
            )
            continue
        if not isinstance(payload, dict):
            raw_reply = _call_agent3("JSON must be an object. Retry.")
            continue

        tool_name = str(payload.get("tool", ""))
        arguments = payload.get("arguments", {}) or {}

        if tool_name == "done":
            if patch_guard_mode:
                _tx = {}
                if isinstance(arguments, dict):
                    _tx = arguments.get("transaction_report", {}) or {}
                _required = (
                    "observed_signature",
                    "target_callsite",
                    "minimal_patch",
                    "verify_result",
                )
                _missing = [k for k in _required if not str(_tx.get(k, "")).strip()]
                if _missing:
                    raw_reply = _call_agent3(
                        "done rejected — transactional report missing fields: "
                        f"{_missing}. Please return tool=done with "
                        "arguments.transaction_report including all required fields."
                    )
                    continue
                _decl_now = _extract_decl_signatures(load_file(target_file))
                if _decl_now != _decl_snapshot:
                    raw_reply = _call_agent3(
                        "done rejected — declaration type signatures changed in transactional "
                        "mode. Revert declaration header edits and keep proof-body/API-shape "
                        "fixes only."
                    )
                    continue
            verify = registry.call("run_lean_verify", target_file)
            _candidate_metrics["verify_calls"] += 1
            _candidate_metrics["verify_ms"] += int(float(verify.get("verify_wall_ms", 0) or 0))
            exit_code = int(verify.get("exit_code", 1))
            sorry_count = int(verify.get("sorry_count", -1))
            _verify_snapshots.append(
                {
                    "exit_code": exit_code,
                    "sorry_count": sorry_count,
                    "error_sig": _extract_error_signature(str(verify.get("errors", ""))),
                }
            )
            if exit_code == 0 and sorry_count == 0:
                return {
                    "exit_code": exit_code,
                    "sorry_count": sorry_count,
                    "errors": "",
                    "transaction_valid": bool(patch_guard_mode),
                    "observed_signature": _last_observed_signature,
                    "target_callsite": _last_callsite,
                    "minimal_patch": f"edit_calls={_edit_calls}",
                    "verify_result": _verify_snapshots[-1],
                    "candidate_id": _candidate_label,
                    "active_target": _initial_active_target,
                    "candidate_metrics": {
                        **_candidate_metrics,
                        "candidate_total_ms": int((time.perf_counter() - _candidate_started) * 1000.0),
                    },
                    "blocked_state": {},
                }
            # Reject done if not clean
            raw_reply = _call_agent3(
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
            raw_reply = _call_agent3(
                f"Tool `{tool_name}` is not available in Agent8 dispatch mode. "
                "Agent8 handles routing. Focus on the tactical fix described in "
                "your instructions."
            )
            continue

        # Compile-first mode: constrain tool usage to minimal repair loop.
        if compile_first_mode:
            _compile_first_allowed = {
                "read_file",
                "search_in_file",
                "search_codebase",
                "edit_file_patch",
                "run_lean_verify",
                "done",
            }
            if repair_unit == _REPAIR_UNIT_BLOCK_RESTRUCTURE:
                _compile_first_allowed.update({"get_lean_goal", "check_lean_have"})
            if tool_name not in _compile_first_allowed:
                raw_reply = _call_agent3(
                    f"Compile-first mode active. Tool `{tool_name}` is not allowed. "
                    "Use only: read_file, search_in_file, search_codebase, edit_file_patch, "
                    "run_lean_verify, done (plus get_lean_goal/check_lean_have in block-restructure mode)."
                )
                continue

        # Execute tool
        args = dict(arguments)
        if tool_name == "edit_file_patch":
            _requested_path = str(args.get("path", target_file))
            if _requested_path != target_file:
                raw_reply = _call_agent3(
                    "Candidate isolation active: edit_file_patch path must match the "
                    f"target file exactly ({target_file}). "
                    f"Requested path was: {_requested_path}"
                )
                continue
            args["path"] = target_file
            try:
                _active_target = _build_active_target(
                    target_file,
                    candidate_id=_candidate_label,
                    allowed_edit_lines=allowed_edit_lines,
                    decl_name=decl_name,
                )
            except Exception as exc:
                raw_reply = _call_agent3(
                    "Patch rejected — active target is stale or invalid: "
                    f"{exc}. Re-read the candidate file and rebind the current target span."
                )
                continue
            if allowed_edit_lines:
                args["allowed_line_range"] = allowed_edit_lines
            args["required_file_hash"] = _active_target["file_hash"]
            args["anchor_text"] = _active_target["anchor_text"]
            args["anchor_hash"] = _active_target["anchor_hash"]
        if transactional_mode and tool_name == "edit_file_patch":
            _edit_calls += 1
            if _edit_calls > 2:
                raw_reply = _call_agent3(
                    "Transactional mode: too many edits in one round (>2). "
                    "Revert to minimal patching and verify before further edits."
                )
                continue
            _old = str(args.get("old_str", "") or "")
            _new = str(args.get("new_str", "") or "")
            _patch_span = _estimate_patch_line_span(_old, _new)
            if _patch_span > _max_patch_lines:
                raw_reply = _call_agent3(
                    "Patch rejected — changed line span "
                    f"({_patch_span}) exceeds AGENT8_MAX_PATCH_LINES={_max_patch_lines}. "
                    "Submit a smaller patch."
                )
                continue
            if transactional_mode and _patch_touches_decl_signature(_old, _new):
                raw_reply = _call_agent3(
                    "Patch rejected — declaration signature edits are not allowed in "
                    "transactional API-shape mode."
                )
                continue
        # Normalize path/file_path
        if "path" in args and "file_path" not in args:
            for k in ("get_lean_goal", "check_lean_have", "run_lean_verify"):
                if tool_name == k:
                    args["file_path"] = args.pop("path")
                    break

        try:
            _tool_started = time.perf_counter()
            result = registry.call(tool_name, **args)
            _elapsed_tool_ms = int((time.perf_counter() - _tool_started) * 1000.0)
            _candidate_metrics["tool_ms"] += _elapsed_tool_ms
            _candidate_metrics["tool_calls"] += 1
            if tool_name == "run_lean_verify" and isinstance(result, dict):
                _candidate_metrics["verify_calls"] += 1
                _candidate_metrics["verify_ms"] += int(float(result.get("verify_wall_ms", 0) or 0))
        except KeyError:
            raw_reply = _call_agent3(
                f"Unknown tool `{tool_name}`. Available: "
                "read_file, search_codebase, search_in_file, edit_file_patch, "
                "write_new_file, run_lean_verify, get_lean_goal, check_lean_have."
            )
            continue
        except Exception as exc:
            raw_reply = _call_agent3(f"Tool error: {exc}")
            continue

        if isinstance(result, dict):
            result_text = json.dumps(result, indent=2, ensure_ascii=False)
        else:
            result_text = str(result)
        if transactional_mode and tool_name in ("search_in_file", "search_codebase", "read_file"):
            _last_observed_signature = result_text[:500]
        if transactional_mode and tool_name == "edit_file_patch":
            _last_callsite = str(args.get("path", target_file))
        if transactional_mode and tool_name == "run_lean_verify":
            _verify_snapshots.append(
                {
                    "exit_code": int(getattr(result, "get", lambda *_: 1)("exit_code", 1))
                    if isinstance(result, dict) else 1,
                    "sorry_count": int(getattr(result, "get", lambda *_: -1)("sorry_count", -1))
                    if isinstance(result, dict) else -1,
                    "error_sig": _extract_error_signature(
                        str(getattr(result, "get", lambda *_: "")("errors", ""))
                    ) if isinstance(result, dict) else "",
                }
            )
        raw_reply = _call_agent3(f"## {tool_name} result\n```\n{result_text}\n```\n")

    # Turns exhausted — verify final state
    final = registry.call("run_lean_verify", target_file)
    _candidate_metrics["verify_calls"] += 1
    _candidate_metrics["verify_ms"] += int(float(final.get("verify_wall_ms", 0) or 0))
    final_errors = str(final.get("errors", ""))
    return {
        "exit_code": int(final.get("exit_code", 1)),
        "sorry_count": int(final.get("sorry_count", -1)),
        "errors": final_errors,
        "transaction_valid": False if patch_guard_mode else True,
        "observed_signature": _last_observed_signature,
        "target_callsite": _last_callsite,
        "minimal_patch": f"edit_calls={_edit_calls}",
        "verify_result": _verify_snapshots[-1] if _verify_snapshots else {},
        "candidate_id": str(final.get("candidate_id", _candidate_label)),
        "active_target": final.get("active_target", _initial_active_target),
        "candidate_metrics": {
            **_candidate_metrics,
            "candidate_total_ms": int((time.perf_counter() - _candidate_started) * 1000.0),
        },
        "blocked_state": _blocked_state(final_errors),
    }


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
) -> dict:
    """Dispatch Agent3 through Agent3-owned search kernel (Agent8 budget wrapper)."""
    from orchestrator.phase3_agent3 import run_agent3_search_kernel

    max_turns = max_turns or RETRY_LIMITS.get("AGENT8_AGENT3_MAX_TURNS", 15)
    if repair_unit == _REPAIR_UNIT_BLOCK_RESTRUCTURE and not transactional_mode:
        max_turns = min(
            max_turns,
            int(RETRY_LIMITS.get("AGENT8_AGENT3_SAMPLE_MAX_TURNS_PER_CANDIDATE", 8)),
        )
    return run_agent3_search_kernel(
        target_file,
        agent2_plan,
        targeted_prompt,
        allowed_edit_lines,
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
        f"Current file (full when ≤500 lines):\n```lean\n{snippet[:20000]}\n```\n\n"
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
    errors_text: str,
    agent7_targeted_prompt: str,
    agent6_targeted_prompt: str,
    *,
    agent9_plan: dict | None = None,
) -> dict:
    """Run Agent7 for signature check/stub creation, then Agent6 to fill the proof.

    Returns a dict with keys:
      exit_code, sorry_count, errors  — final state of target_file
      stub_compile_failed (bool)      — always False (no separate staging file)
      lemma_proven (bool)             — True when target file sorry count decreased
    """
    from orchestrator.verify import count_sorrys as _count_sorrys

    # Snapshot target sorry count before Agent6 so we can detect lemma-level progress.
    _sorry_before = _count_sorrys(target_file)

    # Phase 1: Agent7 signature audit / stub creation
    a7_plan, _a7_raw = _agent8_run_agent7(
        target_file, errors_text, agent7_targeted_prompt
    )

    if a7_plan and isinstance(a7_plan, dict):
        console.print(
            f"  [Agent8→Agent7] Root cause: {a7_plan.get('root_cause', '?')}"
        )
        # If Agent7 is in CREATE_STUB mode, strip any request_agent6_glue steps
        # to prevent double-dispatch (Agent8 handles Agent6 dispatch itself).
        if a7_plan.get("create_stubs"):
            ordered_steps = a7_plan.get("ordered_steps", [])
            if isinstance(ordered_steps, list):
                a7_plan["ordered_steps"] = [
                    s for s in ordered_steps
                    if isinstance(s, dict) and s.get("tool") != "request_agent6_glue"
                ]

        # Execute direct_apply steps from Agent7 protocol
        exec_registry = ToolRegistry()
        exec_registry.register_default_tools()
        ordered_steps = a7_plan.get("ordered_steps", [])
        if isinstance(ordered_steps, list):
            for step in ordered_steps:
                if isinstance(step, dict) and step.get("direct_apply"):
                    _tool = step.get("tool", "")
                    req_args = step.get("required_args", {})
                    if isinstance(req_args, dict) and _tool == "edit_file_patch" and req_args.get("old_str") and req_args.get("new_str"):
                        try:
                            exec_registry.call(
                                "edit_file_patch",
                                path=req_args.get("path", target_file),
                                old_str=req_args["old_str"],
                                new_str=req_args["new_str"],
                            )
                        except Exception:
                            pass

    # Phase 1.5: Validate target file compiles after Agent7's writes.
    from orchestrator.tools import run_lean_verify as _stub_verify
    _target_check = _stub_verify(target_file)
    _stub_exit = int(_target_check.get("exit_code", 1)) if isinstance(_target_check, dict) else 1
    if _stub_exit != 0:
        console.print(
            f"  [Agent7 stub] Target compile FAILED (exit={_stub_exit}) — "
            "skipping Agent6, returning stub_compile_failed."
        )
        return {
            "exit_code": 1,
            "sorry_count": -1,
            "errors": str(_target_check.get("errors", "")) if isinstance(_target_check, dict) else "",
            "stub_compile_failed": True,
            "lemma_proven": False,
        }

    # Phase 2: Extract proposed_signature from agent9_plan for the targeted lemma.
    _proposed_sig: str | None = None
    if agent9_plan:
        for _thm in agent9_plan.get("theorems", []):
            for _mgl in _thm.get("missing_glue_lemmas", []):
                if isinstance(_mgl, dict):
                    _mname = _mgl.get("name", "")
                    if _mname and _mname in agent6_targeted_prompt:
                        _proposed_sig = _mgl.get("proposed_lean_type") or None
                        break
            if _proposed_sig:
                break

    # Phase 2: Agent6 helper lemma proof
    algo_name = Path(target_file).stem
    agent6 = Agent("glue_filler", extra_files=[target_file])
    agent6_registry = ToolRegistry()
    agent6_registry.register_default_tools()

    _run_agent6_glue_loop(
        agent6,
        agent6_registry,
        target_file,
        goal=agent6_targeted_prompt,
        error_message=errors_text[:500],
        diagnosis=agent6_targeted_prompt,
        target_algo=algo_name,
        proposed_signature=_proposed_sig,
    )

    # Determine lemma_proven by comparing target sorry count before/after Agent6.
    _sorry_after = _count_sorrys(target_file)
    _lemma_proven = _sorry_after < _sorry_before

    # Verify final state of the target file.
    from orchestrator.tools import run_lean_verify
    final = run_lean_verify(target_file)
    return {
        "exit_code": int(final.get("exit_code", 1)),
        "sorry_count": int(final.get("sorry_count", -1)),
        "errors": str(final.get("errors", "")),
        "stub_compile_failed": False,
        "lemma_proven": _lemma_proven,
    }


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


def _print_diagnostic_card(
    *,
    tick: int,
    error_sig: str,
    hypothesis: str,
    evidence: list[dict],
    chosen_action: str,
    counterfactual: str,
    outcome: str = "",
    error_subtype: str = "",
    api_shape_verified: bool = False,
    top_error_count_before: int | None = None,
    top_error_count_after: int | None = None,
    error_count_delta: int | None = None,
    main_error_signature_changed: bool | None = None,
    route_ticks_in_row: int | None = None,
    route_status: str = "Active",
    node_id: str = "",
    node_kind: str = "",
    node_attempt: int = 0,
    queue_remaining: int = 0,
    forced_route_lock: bool = False,
    forced_route_reason: str = "",
    network_cooldown_triggered: bool = False,
    subtype_policy_stage: str = "none",
    investigation_success: bool | None = None,
    allowed_span: str = "",
    candidate_id: str = "",
) -> None:
    """Emit a structured per-tick diagnostic card."""
    ev_lines = [
        f"{idx + 1}. [{e.get('source', 'unknown')}] {e.get('snippet', '')[:140]}"
        for idx, e in enumerate(evidence)
    ]
    subtype_line = f"ErrorSubtype: {error_subtype}  (api_shape_verified={api_shape_verified})\n" if error_subtype else ""
    _before = "?" if top_error_count_before is None else str(top_error_count_before)
    _after = "?" if top_error_count_after is None else str(top_error_count_after)
    if error_count_delta is None and top_error_count_before is not None and top_error_count_after is not None:
        _delta_num = top_error_count_after - top_error_count_before
    else:
        _delta_num = error_count_delta
    _delta = "?" if _delta_num is None else f"{_delta_num:+d}"
    _sigchg = bool(main_error_signature_changed) if main_error_signature_changed is not None else False
    _sig_label = "Yes" if _sigchg else "No"
    _route_ticks = route_ticks_in_row if route_ticks_in_row is not None else 1
    trend_line = f"[Trend] Before: {_before} | After: {_after} | Delta: {_delta}\n"
    sig_line = f"[Signature] Changed: {_sig_label} (Normalized)\n"
    route_line = (
        f"[Route] Current: {chosen_action} | Ticks in Route: {_route_ticks} | "
        f"Status: {route_status}\n"
    )
    policy_line = (
        f"[Policy] forced_route_lock={forced_route_lock} "
        f"| network_cooldown={network_cooldown_triggered} "
        f"| subtype_stage={subtype_policy_stage}\n"
    )
    investigation_line = ""
    if investigation_success is not None:
        investigation_line = f"[Investigation] success={investigation_success}\n"
    forced_line = ""
    if forced_route_reason:
        forced_line = f"[ForcedRouteReason] {forced_route_reason[:220]}\n"
    node_line = ""
    if node_id or node_kind:
        node_line = (
            f"[Subproblem] id={node_id or '?'} kind={node_kind or '?'} "
            f"attempt={node_attempt} queue_remaining={queue_remaining}\n"
        )
    target_line = ""
    if allowed_span or candidate_id:
        target_line = (
            f"[Target] candidate_id={candidate_id or '?'} "
            f"allowed_span={allowed_span or 'full-file'}\n"
        )
    body = (
        f"{subtype_line}"
        f"{trend_line}"
        f"{sig_line}"
        f"{route_line}"
        f"{policy_line}"
        f"{investigation_line}"
        f"{forced_line}"
        f"{node_line}"
        f"{target_line}"
        f"ErrorSig: {error_sig[:120]}\n"
        f"Hypothesis: {hypothesis[:220]}\n"
        f"Evidence:\n" + ("\n".join(ev_lines) if ev_lines else "  (none)") + "\n"
        f"ChosenAction: {chosen_action}\n"
        f"WhyNotOtherAction: {counterfactual[:220]}"
    )
    if outcome:
        body += f"\nOutcome: {outcome}"
    console.print(
        Panel(
            body,
            title=f"[cyan]Agent8 Diagnostic Card — Tick {tick}",
            border_style="cyan",
        )
    )


# ---------------------------------------------------------------------------
# Behavior-driven anti-loop check
# ---------------------------------------------------------------------------

def _check_anti_loop(
    decision: dict,
    decision_history: list[dict],
    *,
    pending_lemma_status: dict | None = None,
) -> tuple[str, str]:
    """Decide whether the proposed action should be overridden to break a loop.

    Returns ``(action, override_reason)``.  When no override is needed,
    ``override_reason`` is empty and ``action`` equals ``decision["action"]``.

    Logic (evaluated in priority order):
    1. **Zero-progress repeat** — the same action was used in the last N
       history entries, all of which had ``sorry_delta == 0`` AND
       ``errors_after[:120] == errors_before[:120]``.  Escalate to
       ``agent9_replan`` (or ``human_missing_assumption`` if the proposed
       action is already ``agent9_replan``).
    2. **Error frozen across all recent actions** — the last 3 history entries
       (regardless of action) all share the same ``errors_after[:120]``.
       Escalate to ``human_missing_assumption`` UNLESS there are known pending
       lemmas that have not yet exhausted their per-lemma attempt budget
       (``pending_lemma_status`` exemption).
    3. **Classic heuristic fallback** — ``(action, error_sig[:LEN])`` pair
       repeated too many times (uses ``AGENT8_ERROR_SIG_FULL_LEN`` instead of
       the old 40-char truncation).
    """
    _no_progress_n = RETRY_LIMITS.get("AGENT8_NO_PROGRESS_ESCALATE_AFTER", 2)
    _sig_len = RETRY_LIMITS.get("AGENT8_ERROR_SIG_FULL_LEN", 120)
    proposed_action = decision.get("action", "agent3_tactical")
    error_sig = decision.get("error_signature", "")
    _escapable = proposed_action not in ("agent9_replan", "human_missing_assumption")
    proposed_hypothesis = str(decision.get("hypothesis", "")).strip()

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
            if proposed_action == "agent9_replan":
                return "human_missing_assumption", _reason
            return "agent9_replan", _reason

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
            # Exemption: if there are known pending lemmas that still have attempt
            # budget remaining, let Agent8 continue dispatching instead of gating.
            _max_lemma_att = RETRY_LIMITS.get("AGENT8_MAX_LEMMA_ATTEMPTS", 3)
            _has_pending_budget = pending_lemma_status and any(
                v.get("status") == "pending"
                and v.get("attempts", 0) < _max_lemma_att
                for v in pending_lemma_status.values()
            )
            if _has_pending_budget:
                # Do not gate; let the next tick continue with lemma proofs.
                pass
            else:
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
            return "agent9_replan", _reason

    # --- Condition 4: same error_signature + same hypothesis repeated failures ---
    if proposed_hypothesis and len(decision_history) >= 2:
        _same_hyp_recent = [
            e for e in decision_history[-3:]
            if str(e.get("hypothesis", "")).strip() == proposed_hypothesis
            and e.get("error_signature", "")[:120] == error_sig[:120]
            and e.get("outcome") in ("failed", "dispatch_error")
            and int(e.get("top_error_count_after", 0)) >= int(e.get("top_error_count_before", 0))
        ]
        if len(_same_hyp_recent) >= 2:
            _reason = (
                "same error_signature + same hypothesis failed repeatedly "
                "(no error-count improvement)"
            )
            if proposed_action in ("agent9_replan", "human_missing_assumption"):
                return "agent7_signature", _reason
            return "agent9_replan", _reason

    return proposed_action, ""


# ---------------------------------------------------------------------------
# Main state-machine loop
# ---------------------------------------------------------------------------

def run_agent8_loop(
    agent2: Agent,
    target_file: str,
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
    _baseline_errors = last_errors
    _consecutive_parse_failures = 0
    _consecutive_same_error: int = 0
    _last_error_sig: str = ""
    _force_lookup_next_tick: bool = False
    _action_cooldowns: dict[str, int] = {}
    _decompose_attempted_for_signature: set[str] = set()
    _serial_subproblem_queue: list[dict[str, Any]] = []
    _serial_subproblem_attempts: dict[str, int] = {}
    _serial_max_attempts = max(1, int(RETRY_LIMITS.get("AGENT8_SUBPROBLEM_MAX_ATTEMPTS", 2)))

    # Per-lemma attempt tracking for sorry-only scenarios.
    # Populated from agent9_plan's missing_glue_lemmas at startup and after replans.
    # key = lemma name, value = {"attempts": int, "status": "pending"|"success"|"failed"}
    _pending_lemma_status: dict[str, dict] = {}

    def _init_lemma_status_from_plan(plan: dict) -> None:
        """Populate _pending_lemma_status from a (re-)plan without overwriting existing entries."""
        for _thm in plan.get("theorems", []):
            for _mgl in _thm.get("missing_glue_lemmas", []):
                _name = _mgl["name"] if isinstance(_mgl, dict) else str(_mgl)
                if _name and _name not in _pending_lemma_status:
                    _pending_lemma_status[_name] = {"attempts": 0, "status": "pending"}

    if agent9_plan:
        _init_lemma_status_from_plan(agent9_plan)

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
        _tick_started = time.perf_counter()
        _tick_timing: dict[str, int] = {
            "fresh_verify_ms": 0,
            "context_build_ms": 0,
            "decision_llm_ms": 0,
            "investigation_ms": 0,
            "dispatch_ms": 0,
            "post_observability_ms": 0,
            "success_recheck_ms": 0,
            "tick_total_ms": 0,
        }
        _active_subproblem_node: dict[str, Any] | None = None
        # Decrement action cooldowns at the start of each tick.
        for _a in list(_action_cooldowns.keys()):
            _action_cooldowns[_a] = max(0, int(_action_cooldowns.get(_a, 0)) - 1)
            if _action_cooldowns[_a] <= 0:
                _action_cooldowns.pop(_a, None)

        # 0. Fresh verify — always rebuild errors from the current file state
        # so that smart-truncation line numbers match the actual file content.
        from orchestrator.tools import run_lean_verify as _tick_verify
        _fresh_started = time.perf_counter()
        _fresh = _tick_verify(target_file)
        _tick_timing["fresh_verify_ms"] = int((time.perf_counter() - _fresh_started) * 1000.0)
        _fresh_exit = int(_fresh.get("exit_code", 1))
        _fresh_errors = _coerce_errors_text(_fresh.get("errors", ""))
        _fresh_error_count = _error_count_from_verify(_fresh, _fresh_errors)
        _fresh_sorry = int(_fresh.get("sorry_count", _current_sorry_count))
        _fresh_blocked = int(_fresh.get("blocked_sorry_count", 0))
        _fresh_backend_used = str(_fresh.get("verify_backend_used", ""))
        _fresh_backend_reason = str(_fresh.get("verify_backend_reason", ""))
        _compile_first_mode = (_fresh_exit != 0 and _fresh_sorry == 0)
        # Always use fresh verifier output as the source of truth.
        current_errors = _fresh_errors
        _current_structured_errors = _parse_lean_errors(current_errors)
        _current_error_line = _extract_first_error_line(current_errors)
        _prioritized_current_errors = _prioritize_error_text(
            _current_structured_errors,
            current_errors,
            _current_error_line,
            target_file,
        )
        _baseline_structured_errors = _parse_lean_errors(_baseline_errors)
        _baseline_error_line = _extract_first_error_line(_baseline_errors)
        _prioritized_baseline_errors = _prioritize_error_text(
            _baseline_structured_errors,
            _baseline_errors,
            _baseline_error_line,
            target_file,
        )
        _canonical_sig = _canonical_error_signature(current_errors)
        _current_sorry_count = _fresh_sorry

        # Classify error subtype before building context so it can be injected.
        _error_subtype = _classify_error_subtype(
            current_errors, target_file,
            decision_history=decision_history,
        )

        console.print(
            f"  [Agent8] Fresh verify: exit={_fresh_exit}, "
            f"sorry={_fresh_sorry} | subtype={_error_subtype}"
        )
        if _compile_first_mode and not _active_subproblem_node:
            console.print(
                f"  [Agent8] Compile-First mode active (exit=1, sorry=0): "
                f"subtype={_error_subtype} — "
                "prioritizing API/signature/type alignment over strategy debate."
            )

        # 1. Build context
        _recent_canonicals = [
            str(e.get("canonical_error_signature", "")).strip()
            for e in decision_history[-2:]
            if str(e.get("canonical_error_signature", "")).strip()
        ]
        _reset_hypothesis_bias = (
            len(_recent_canonicals) == 2
            and _recent_canonicals[0] != _recent_canonicals[1]
            and _recent_canonicals[1] != _canonical_sig
        )
        _same_sig_streak = 1
        for _entry in reversed(decision_history):
            if str(_entry.get("canonical_error_signature", "")) == _canonical_sig:
                _same_sig_streak += 1
            else:
                break
        _stale_hint = ""
        if _same_sig_streak >= 3:
            try:
                _ctx_registry = ToolRegistry()
                _ctx_registry.register_readonly_tools()
                _stale_hint = _build_stale_error_hint(
                    _ctx_registry,
                    target_file,
                    current_errors,
                    _current_error_line,
                    _same_sig_streak,
                )
            except Exception:  # noqa: BLE001
                _stale_hint = ""
        _ctx_started = time.perf_counter()
        ctx = _build_agent8_tick_context(
            target_file, _prioritized_current_errors, current_plan, decision_history,
            agent9_plan=agent9_plan,
            plan_updated_tick=_plan_updated_tick,
            pending_lemma_status=_pending_lemma_status,
            baseline_errors=_prioritized_baseline_errors,
            error_subtype=_error_subtype,
            canonical_error_signature=_canonical_sig,
            stale_error_hint=_stale_hint,
            reset_hypothesis_bias=_reset_hypothesis_bias,
            verify_backend_used=_fresh_backend_used,
            verify_backend_reason=_fresh_backend_reason,
        )
        _tick_timing["context_build_ms"] = int((time.perf_counter() - _ctx_started) * 1000.0)
        if _force_lookup_next_tick:
            ctx += (
                "\n\n## Mandatory Investigation This Tick\n"
                "Last tick had replan failure / zero-progress. "
                "You MUST perform at least one lookup before final decision."
            )

        # 2. Call Agent8 with optional investigation rounds
        agent8 = Agent("decision_hub")
        _inv_registry = ToolRegistry()
        _inv_registry.register_investigation_tools()
        _max_inv = RETRY_LIMITS.get("AGENT8_INVESTIGATION_TURNS", 3)
        _investigation_rounds_this_tick = 0
        _investigation_tools_this_tick: list[dict[str, Any]] = []
        _llm_started = time.perf_counter()
        raw_reply = _safe_llm_call(agent8, ctx, idempotent=True, max_attempts=3)
        _tick_timing["decision_llm_ms"] += int((time.perf_counter() - _llm_started) * 1000.0)

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
                    _inv_started = time.perf_counter()
                    _tr = _inv_registry.call(_tn, **_ta)
                    _tick_timing["investigation_ms"] += int((time.perf_counter() - _inv_started) * 1000.0)
                except Exception as _exc:
                    _tr = {"error": str(_exc)}
                _inv_results.append({"tool": _tn, "result": _tr})
                _success = not (isinstance(_tr, dict) and _tr.get("error"))
                _investigation_tools_this_tick.append(
                    {
                        "tool": str(_tn),
                        "success": _success,
                        "error": str(_tr.get("error", "")) if isinstance(_tr, dict) else "",
                    }
                )
            _investigation_rounds_this_tick += 1
            _llm_started = time.perf_counter()
            raw_reply = _safe_llm_call(
                agent8,
                "Investigation results:\n"
                + json.dumps(_inv_results, indent=2, ensure_ascii=False)
                + "\n\nNow output your final JSON decision.",
                idempotent=True,
                max_attempts=3,
            )
            _tick_timing["decision_llm_ms"] += int((time.perf_counter() - _llm_started) * 1000.0)

        # 3. Parse decision (with retry)
        decision, _parse_error = _parse_agent8_decision(raw_reply)
        if decision is None:
            _consecutive_parse_failures += 1
            console.print(
                f"  [Agent8] JSON parse failed ({_consecutive_parse_failures}/3). "
                f"Retrying... reason: {_parse_error}"
            )
            if _consecutive_parse_failures >= 3:
                console.print(
                    "[yellow][Agent8] 3 consecutive parse failures — "
                    "defaulting to agent9_replan"
                )
                decision = {
                    "action": "agent9_replan",
                    "priority_level": "P2",
                    "reason": "Agent8 JSON parse failures — falling back to replan",
                    "targeted_prompt": "Revise the proof strategy.",
                    "error_signature": _canonical_sig,
                    "hypothesis": "Current decision protocol output is malformed; regenerate a fresh structured plan.",
                    "evidence": [
                        {"source": "agent8_parse", "snippet": _parse_error},
                        {"source": "lean_verify", "snippet": _canonical_sig},
                    ],
                    "confidence": 0.4,
                    "counterfactual": "Do not keep local tactical loop when decision JSON is repeatedly invalid.",
                }
            else:
                # Retry with explicit instruction
                _llm_started = time.perf_counter()
                raw_reply = _safe_llm_call(
                    agent8,
                    "Your response was not valid JSON. Return ONLY a single JSON "
                    "object with the required fields: action, priority_level, reason, "
                    "error_signature, hypothesis, evidence, confidence, "
                    "counterfactual. targeted_prompt is optional. No markdown fences.",
                    idempotent=True,
                    max_attempts=2,
                )
                _tick_timing["decision_llm_ms"] += int((time.perf_counter() - _llm_started) * 1000.0)
                decision, _parse_error = _parse_agent8_decision(raw_reply)
                if decision is None:
                    continue
        _consecutive_parse_failures = 0
        decision["error_signature"] = _canonical_sig
        decision["canonical_error_signature"] = _canonical_sig

        _has_real_investigation = _has_informative_investigation(_investigation_tools_this_tick)
        _investigation_tool_names = [
            str(item.get("tool", "")) if isinstance(item, dict) else str(item)
            for item in _investigation_tools_this_tick
        ]
        _investigation_failures = [
            item for item in _investigation_tools_this_tick
            if isinstance(item, dict) and not bool(item.get("success"))
        ]
        if _is_structural_error(
            _canonical_sig,
            current_errors,
        ) and not _has_real_investigation:
            console.print(
                "  [Agent8] Mandatory lookup gate: structural error requires at least "
                "one investigation lookup before routing."
            )
            _llm_started = time.perf_counter()
            raw_reply = _safe_llm_call(
                agent8,
                "Structural error detected. Before final decision, you MUST output at least "
                "one lookup request using supported read-only tools.",
                idempotent=True,
                max_attempts=2,
            )
            _tick_timing["decision_llm_ms"] += int((time.perf_counter() - _llm_started) * 1000.0)
            for _ in range(min(_max_inv, 2)):
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
                _inv_results = []
                for _tc in _inv_payload["tool_calls"]:
                    _tn = _tc.get("tool", "")
                    _ta = _tc.get("arguments", {}) or {}
                    try:
                        _inv_started = time.perf_counter()
                        _tr = _inv_registry.call(_tn, **_ta)
                        _tick_timing["investigation_ms"] += int((time.perf_counter() - _inv_started) * 1000.0)
                    except Exception as _exc:
                        _tr = {"error": str(_exc)}
                    _inv_results.append({"tool": _tn, "result": _tr})
                    _success = not (isinstance(_tr, dict) and _tr.get("error"))
                    _investigation_tools_this_tick.append(
                        {
                            "tool": str(_tn),
                            "success": _success,
                            "error": str(_tr.get("error", "")) if isinstance(_tr, dict) else "",
                        }
                    )
                _investigation_rounds_this_tick += 1
                _llm_started = time.perf_counter()
                raw_reply = _safe_llm_call(
                    agent8,
                    "Investigation results:\n"
                    + json.dumps(_inv_results, indent=2, ensure_ascii=False)
                    + "\n\nNow output your final JSON decision.",
                    idempotent=True,
                    max_attempts=2,
                )
                _tick_timing["decision_llm_ms"] += int((time.perf_counter() - _llm_started) * 1000.0)
            decision2, parse_err2 = _parse_agent8_decision(raw_reply)
            if decision2 is not None:
                decision = decision2
                decision["error_signature"] = _canonical_sig
                decision["canonical_error_signature"] = _canonical_sig
            else:
                console.print(f"  [Agent8] Mandatory lookup re-parse failed: {parse_err2}")
        if _has_informative_investigation(_investigation_tools_this_tick):
            _force_lookup_next_tick = False

        action = decision.get("action", "agent3_tactical")
        error_sig = _canonical_sig
        targeted_prompt = decision.get("targeted_prompt", "")
        hypothesis = str(decision.get("hypothesis", "")).strip()
        evidence = _normalize_evidence(decision.get("evidence"))
        counterfactual = str(decision.get("counterfactual", "")).strip()
        _active_subproblem_node = None
        _forced_route_lock = False
        _forced_route_reason = ""
        _network_cooldown_triggered = False
        _subtype_policy_stage = "none"
        if _serial_subproblem_queue:
            _active_subproblem_node = _serial_subproblem_queue.pop(0)
            _node_id = str(_active_subproblem_node.get("id", f"node-{tick}"))
            _node_kind = str(_active_subproblem_node.get("kind", "global_strategy"))
            _node_attempt = _serial_subproblem_attempts.get(_node_id, 0) + 1
            _serial_subproblem_attempts[_node_id] = _node_attempt
            _node_evidence = str(_active_subproblem_node.get("evidence", "")).strip()
            if _node_attempt > _serial_max_attempts:
                action = _subproblem_kind_fallback_action(_node_kind)
                targeted_prompt = (
                    f"[SERIAL NODE RETRY EXHAUSTED] node={_node_id} kind={_node_kind} "
                    f"attempt={_node_attempt}>{_serial_max_attempts}. "
                    "Switching to deterministic fallback route."
                )
            else:
                action = _subproblem_kind_to_action(_node_kind)
                targeted_prompt = (
                    f"[SERIAL SUBPROBLEM] node={_node_id} kind={_node_kind} "
                    f"attempt={_node_attempt}/{_serial_max_attempts}.\n"
                    f"Target: {str(_active_subproblem_node.get('target', ''))}\n"
                    f"Evidence: {_node_evidence}\n"
                    "Follow deterministic routing for this node."
                )
            decision["action"] = action
            decision["targeted_prompt"] = targeted_prompt
            decision["reason"] = (
                f"serial subproblem dispatcher active ({_node_kind})"
            )
            decision["subproblem_node"] = _active_subproblem_node
            if not evidence:
                evidence = [{
                    "source": "apollo_subproblem_queue",
                    "snippet": f"{_node_id}:{_node_kind} {_node_evidence[:120]}",
                }]
        _route_ticks_pre = _route_streak_len(decision_history, action) + 1
        _route_status_pre = (
            "Cooldown"
            if int(_action_cooldowns.get(action, 0)) > 0
            else "Active"
        )
        _target_region = _target_region_from_errors(
            current_errors,
            fallback_span=str(decision.get("allowed_edit_lines", "") or "")
            or (
                str(_active_subproblem_node.get("target", ""))
                if _active_subproblem_node
                else ""
            ),
        )
        _repair_unit = _classify_repair_unit(
            action=action,
            error_subtype=_error_subtype,
            current_errors=current_errors,
            decision_history=decision_history,
            target_region=_target_region,
            allowed_edit_lines=decision.get("allowed_edit_lines"),
            subproblem_kind=str(_active_subproblem_node.get("kind", "")) if _active_subproblem_node else "",
        )
        decision["repair_unit"] = _repair_unit
        decision["target_region"] = _target_region
        decision["agent3_execution_mode"] = _agent3_execution_mode_for_repair(
            error_subtype=_error_subtype,
            repair_unit=_repair_unit,
            current_errors=current_errors,
            decision_history=decision_history,
            target_region=_target_region,
            allowed_edit_lines=decision.get("allowed_edit_lines"),
        )
        if _force_lookup_next_tick and not evidence:
            evidence = [{"source": "system_gate", "snippet": "lookup was required due to prior zero-progress"}]

        _print_diagnostic_card(
            tick=tick,
            error_sig=error_sig,
            hypothesis=hypothesis,
            evidence=evidence,
            chosen_action=action,
            counterfactual=counterfactual,
            error_subtype=_error_subtype,
            route_ticks_in_row=_route_ticks_pre,
            route_status=_route_status_pre,
            node_id=(
                str(_active_subproblem_node.get("id", ""))
                if _active_subproblem_node
                else ""
            ),
            node_kind=(
                str(_active_subproblem_node.get("kind", ""))
                if _active_subproblem_node
                else ""
            ),
            node_attempt=(
                int(_serial_subproblem_attempts.get(str(_active_subproblem_node.get("id", "")), 0))
                if _active_subproblem_node
                else 0
            ),
            queue_remaining=len(_serial_subproblem_queue),
            forced_route_lock=_forced_route_lock,
            forced_route_reason=_forced_route_reason,
            network_cooldown_triggered=_network_cooldown_triggered,
            subtype_policy_stage=_subtype_policy_stage,
            investigation_success=_has_real_investigation,
            allowed_span=str(decision.get("allowed_edit_lines", "") or ""),
            candidate_id=f"{_repair_unit}:{_target_region}",
        )

        console.print(
            f"  [Agent8] Decision: {action} "
            f"(P={decision.get('priority_level', '?')}) "
            f"| subtype={_error_subtype} "
            f"| error_sig=\"{error_sig[:60]}\""
        )
        console.print(f"  [Agent8] Reason: {decision.get('reason', '?')}")

        if not _active_subproblem_node:
            # 4a0. Subtype-specific route policy (first-try vs forced tactical fallback).
            action, _subtype_policy_stage, _subtype_policy_reason, _subtype_force = (
                _apply_subtype_route_policy(action, _error_subtype, decision_history)
            )
            if _subtype_policy_reason:
                console.print(f"  [SubtypePolicy] {action} ← {_subtype_policy_reason}")
                decision["action"] = action
                targeted_prompt = (
                    f"[SUBTYPE POLICY: {_subtype_policy_reason}] " + targeted_prompt
                )
            if _subtype_force:
                _forced_route_lock = True
                _forced_route_reason = _subtype_policy_reason

            # 4a. Anti-loop check (behavior-driven)
            action, _antiloop_reason = _check_anti_loop(
                decision, decision_history,
                pending_lemma_status=_pending_lemma_status,
            )
            if _antiloop_reason:
                console.print(f"  [AntiLoop] {action} ← {_antiloop_reason}")
                decision["action"] = action
                targeted_prompt = (
                    f"[FORCED by anti-loop: {_antiloop_reason}] " + targeted_prompt
                )

            # 4b. Route downweight: subtype + action with zero error-count progress
            action, _downweight_reason = _check_route_downweight(
                action,
                _error_subtype,
                decision_history,
                compile_first_mode=_compile_first_mode,
                current_errors=current_errors,
                target_region=_target_region,
                allowed_edit_lines=decision.get("allowed_edit_lines"),
            )
            if _downweight_reason:
                console.print(f"  [RouteDownweight] {action} ← {_downweight_reason}")
                decision["action"] = action
                targeted_prompt = (
                    f"[ROUTE DOWNWEIGHTED: {_downweight_reason}] " + targeted_prompt
                )

            # 4c. Explicit delta-based force fallback chain (2 ticks by default).
            action, _delta_force_reason = _apply_delta_force_fallback(
                action,
                decision_history,
                _action_cooldowns,
                error_subtype=_error_subtype,
                compile_first_mode=_compile_first_mode,
                window=RETRY_LIMITS.get("AGENT8_FORCE_FALLBACK_WINDOW", 2),
                cooldown_ticks=RETRY_LIMITS.get("AGENT8_ROUTE_COOLDOWN_TICKS", 2),
                current_errors=current_errors,
                target_region=_target_region,
                allowed_edit_lines=decision.get("allowed_edit_lines"),
            )
            if _delta_force_reason:
                console.print(f"  [DeltaForceFallback] {action} ← {_delta_force_reason}")
                decision["action"] = action
                targeted_prompt = (
                    f"[DELTA FORCE FALLBACK: {_delta_force_reason}] " + targeted_prompt
                )
                _forced_route_lock = True
                _forced_route_reason = _delta_force_reason

            # 4d. Hard route gate with cooldown (falsifiable routing).
            action, _hard_reason = _apply_hard_route_gate(
                action,
                _error_subtype,
                decision_history,
                _action_cooldowns,
                compile_first_mode=_compile_first_mode,
                window=RETRY_LIMITS.get("AGENT8_ROUTE_NO_DELTA_WINDOW", 3),
                cooldown_ticks=RETRY_LIMITS.get("AGENT8_ROUTE_COOLDOWN_TICKS", 2),
                current_errors=current_errors,
                target_region=_target_region,
                allowed_edit_lines=decision.get("allowed_edit_lines"),
            )
            if _hard_reason:
                console.print(f"  [HardRouteGate] {action} ← {_hard_reason}")
                decision["action"] = action
                targeted_prompt = (
                    f"[HARD ROUTE GATE: {_hard_reason}] " + targeted_prompt
                )
                _forced_route_lock = True
                _forced_route_reason = _hard_reason

            # 4d1. Network-failure cooldown fallback for agent7 loops.
            action, _net_cooldown_reason, _net_cooldown_on = _apply_network_cooldown_fallback(
                action,
                _error_subtype,
                decision_history,
                _action_cooldowns,
                cooldown_ticks=RETRY_LIMITS.get("AGENT8_ROUTE_COOLDOWN_TICKS", 2),
            )
            if _net_cooldown_reason:
                console.print(f"  [NetworkCooldown] {action} ← {_net_cooldown_reason}")
                decision["action"] = action
                targeted_prompt = (
                    f"[NETWORK COOLDOWN: {_net_cooldown_reason}] " + targeted_prompt
                )
            if _net_cooldown_on:
                _network_cooldown_triggered = True
                _forced_route_lock = True
                if not _forced_route_reason:
                    _forced_route_reason = _net_cooldown_reason

        # Compile-first subtype routing:
        # When exit=1 && sorry=0, route based on classified error subtype
        # rather than forcing everything to agent7_signature.
        if _compile_first_mode:
            action, targeted_prompt, _cf_reason = _apply_compile_first_subtype_gate(
                action,
                _error_subtype,
                targeted_prompt,
                forced_route_lock=_forced_route_lock,
                current_errors=current_errors,
                decision_history=decision_history,
                target_region=_target_region,
                allowed_edit_lines=decision.get("allowed_edit_lines"),
            )
            if _cf_reason:
                console.print(
                    "  [Agent8] Compile-First subtype gate: "
                    f"{_cf_reason}."
                )
                decision["action"] = action
            elif _forced_route_lock:
                console.print(
                    "  [Agent8] Compile-First gate skipped due to forced_route_lock: "
                    f"{_forced_route_reason or 'route already force-switched'}"
                )

        # 4e. Stage-2 APOLLO decomposition policy gate.
        if not _active_subproblem_node:
            _prefer_apollo, _apollo_policy_reason = _should_prefer_apollo_decompose(
                action,
                error_sig,
                decision_history,
                blocked_sorry_count=_fresh_blocked,
                action_cooldowns=_action_cooldowns,
                error_subtype=_error_subtype,
                compile_first_mode=_compile_first_mode,
                current_errors=current_errors,
                target_region=_target_region,
                allowed_edit_lines=decision.get("allowed_edit_lines"),
            )
            if _prefer_apollo:
                action = "apollo_decompose_repair"
                decision["action"] = action
                decision["trigger_reason"] = _apollo_policy_reason
                console.print(
                    "  [Agent8] APOLLO policy trigger: "
                    f"{_apollo_policy_reason} -> action=apollo_decompose_repair"
                )
                targeted_prompt = (
                    f"[APOLLO POLICY TRIGGER: {_apollo_policy_reason}] " + targeted_prompt
                )

        # Hard trigger: same signature should attempt APOLLO decomposition once
        # before escalating to human gate.
        _norm_sig = _normalize_error_signature(error_sig)
        if error_sig and error_sig == _last_error_sig:
            _consecutive_same_error += 1
        else:
            _consecutive_same_error = 1
            _last_error_sig = error_sig
        if not _active_subproblem_node and _consecutive_same_error >= AGENT8_HUMAN_GATE_CONSECUTIVE_THRESHOLD:
            if (
                AGENT8_APOLLO_DECOMPOSE_ENABLED
                and _norm_sig
                and _norm_sig not in _decompose_attempted_for_signature
                and int(_action_cooldowns.get("apollo_decompose_repair", 0)) <= 0
            ):
                action = "apollo_decompose_repair"
                decision["action"] = action
                decision["trigger_reason"] = (
                    f"hard-trigger signature freeze {_consecutive_same_error}×; "
                    "forcing one APOLLO decomposition attempt before human gate"
                )
                targeted_prompt = (
                    f"[FORCED DECOMPOSE BEFORE HUMAN GATE] "
                    f"signature={_norm_sig[:80]}\n\n{targeted_prompt}"
                )
            elif action != "human_missing_assumption":
                console.print(
                    f"  [Agent8] HARD TRIGGER: same error {_consecutive_same_error}× "
                    "→ forcing human_missing_assumption"
                )
                action = "human_missing_assumption"
                decision["action"] = action

        _target_region = _target_region_from_errors(
            current_errors,
            fallback_span=str(decision.get("allowed_edit_lines", "") or "")
            or (
                str(_active_subproblem_node.get("target", ""))
                if _active_subproblem_node
                else ""
            ),
        )
        _repair_unit = _classify_repair_unit(
            action=action,
            error_subtype=_error_subtype,
            current_errors=current_errors,
            decision_history=decision_history,
            target_region=_target_region,
            allowed_edit_lines=decision.get("allowed_edit_lines"),
            subproblem_kind=str(_active_subproblem_node.get("kind", "")) if _active_subproblem_node else "",
        )
        decision["repair_unit"] = _repair_unit
        decision["target_region"] = _target_region
        _region_streak = _region_no_progress_streak(
            decision_history,
            target_region=_target_region,
            repair_unit=_repair_unit,
        )
        _blocker_status = ""
        _blocker_report: dict[str, Any] | None = None
        if (
            action == "human_missing_assumption"
            or (
                _repair_unit == _REPAIR_UNIT_STATEMENT_GAP
                and _region_streak >= int(RETRY_LIMITS.get("AGENT8_STATEMENT_GAP_REGION_THRESHOLD", 4)) - 1
            )
        ):
            _blocker_status = (
                _BLOCKER_CERTIFIED_STATEMENT_GAP
                if _repair_unit == _REPAIR_UNIT_STATEMENT_GAP
                else _BLOCKER_CERTIFIED_STRUCTURAL_BLOCK
            )
            _blocker_report = _build_blocker_report(
                blocker_status=_blocker_status,
                repair_unit=_repair_unit,
                target_region=_target_region,
                error_subtype=_error_subtype,
                error_signature=error_sig,
                decision_history=decision_history,
                apollo_attempted=bool(_norm_sig and _norm_sig in _decompose_attempted_for_signature),
                current_errors=current_errors,
            )
            decision["blocker_status"] = _blocker_status
            decision["blocker_report"] = _blocker_report

        _light_action, _light_reason = _prefer_agent3_search_owner(
            action=action,
            error_subtype=_error_subtype,
            current_errors=current_errors,
            decision_history=decision_history,
            target_region=_target_region,
            allowed_edit_lines=decision.get("allowed_edit_lines"),
        )
        if _light_reason:
            action = _light_action
            decision["action"] = action
            targeted_prompt = f"[AGENT8 LIGHT ROUTER] {_light_reason} {targeted_prompt}".strip()
            _repair_unit = _classify_repair_unit(
                action=action,
                error_subtype=_error_subtype,
                current_errors=current_errors,
                decision_history=decision_history,
                target_region=_target_region,
                allowed_edit_lines=decision.get("allowed_edit_lines"),
                subproblem_kind=str(_active_subproblem_node.get("kind", "")) if _active_subproblem_node else "",
            )
            decision["repair_unit"] = _repair_unit
            decision["agent3_execution_mode"] = _agent3_execution_mode_for_repair(
                error_subtype=_error_subtype,
                repair_unit=_repair_unit,
                current_errors=current_errors,
                decision_history=decision_history,
                target_region=_target_region,
                allowed_edit_lines=decision.get("allowed_edit_lines"),
            )

        # 5. Dispatch — capture state BEFORE action for delta computation.
        _errors_before: str = current_errors
        _sorry_before: int = _current_sorry_count
        _top_error_count_before = _fresh_error_count
        outcome: dict = {"outcome": "unknown"}
        result: dict = {}
        _direct_apply_errors: list[str] = []
        _has_verified_after_state = False

        _dispatch_started = time.perf_counter()
        try:
            # Safety check: ensure decision is a valid dict
            if not isinstance(decision, dict):
                console.print("  [Agent8] WARNING: decision is not a dict, defaulting to agent3_tactical")
                action = "agent3_tactical"
                decision = {
                    "action": action,
                    "priority_level": "P2",
                    "reason": "Decision dict was invalid",
                    "targeted_prompt": "Fix the proof",
                    "error_signature": error_sig,
                    "hypothesis": "Decision parsing failed",
                    "evidence": [],
                    "confidence": 0.5,
                    "counterfactual": "",
                }
            
            if action == "agent3_tactical":
                console.print("  [Agent8→Agent3] Dispatching tactical fix...")
                _a9_thm_ctx = _build_agent9_theorem_context(
                    agent9_plan, decision.get("target_theorem", "")
                )
                _dispatch_brief = _build_agent3_dispatch_brief(
                    decision,
                    error_subtype=_error_subtype,
                    repair_unit=_repair_unit,
                    target_region=_target_region,
                    current_errors=current_errors,
                )
                _compile_first_note = ""
                if _compile_first_mode:
                    _compile_first_note = (
                        "\n\n[COMPILE-FIRST REPAIR MODE]\n"
                        "- Fix only the top 1-2 compiler/type/API errors in declaration/proof body.\n"
                        "- Verify immediately after edits.\n"
                        "- Do NOT introduce new theorems or large rewrites.\n"
                    )
                result = _agent8_run_agent3(
                    target_file,
                    current_plan,
                    _dispatch_brief + _a9_thm_ctx + _compile_first_note,
                    decision.get("allowed_edit_lines"),
                    compile_first_mode=_compile_first_mode,
                    patch_guard_mode=(
                        _error_subtype == _SUBTYPE_PROOF_API_MISMATCH
                        and _repair_unit != _REPAIR_UNIT_BLOCK_RESTRUCTURE
                    ),
                    search_allowed=True,
                    transactional_mode=(
                        _error_subtype == _SUBTYPE_PROOF_API_MISMATCH
                        and _repair_unit != _REPAIR_UNIT_BLOCK_RESTRUCTURE
                    ),
                    error_subtype=_error_subtype,
                    repair_unit=_repair_unit,
                    target_region=_target_region,
                )
                # Safety check for result dict
                if not isinstance(result, dict):
                    result = {"exit_code": 1, "sorry_count": -1, "errors": "Agent3 result was not a dict"}
                outcome = {
                    "outcome": "success" if result.get("exit_code", 1) == 0 and result.get("sorry_count", -1) == 0 else "failed",
                    "exit_code": result.get("exit_code", 1),
                    "sorry_count": result.get("sorry_count", -1),
                    "error_count": _count_error_lines(_coerce_errors_text(result.get("errors", ""))),
                    "failure_kind": str(result.get("failure_kind", "")),
                    "observed_signature": str(result.get("observed_signature", "")),
                    "best_failed_candidate_summary": result.get("best_failed_candidate_summary", {}),
                    "candidate_id": str(result.get("candidate_id", "")),
                    "active_target": result.get("active_target", {}),
                    "candidate_score": result.get("candidate_score", []),
                    "recursion_depth": int(result.get("recursion_depth", 0) or 0),
                    "budget_remaining": result.get("budget_remaining", {}),
                    "blocked_state": result.get("blocked_state", {}),
                    "candidate_timings": result.get("candidate_timings", []),
                    "search_timing": result.get("search_timing", {}),
                }
                current_errors = _coerce_errors_text(result.get("errors", current_errors))
                _has_verified_after_state = True

            elif action == "agent7_signature":
                console.print("  [Agent8→Agent7] Dispatching signature audit...")
                a7_prompt = _resolve_decision_prompt(
                    decision, "agent7_targeted_prompt", targeted_prompt
                )
                a7_plan, _a7_raw = _agent8_run_agent7(
                    target_file, current_errors, a7_prompt
                )
                # Execute direct_apply steps
                if a7_plan and isinstance(a7_plan, dict):
                    exec_registry = ToolRegistry()
                    exec_registry.register_default_tools()
                    ordered_steps = a7_plan.get("ordered_steps", [])
                    if isinstance(ordered_steps, list):
                        for step in ordered_steps:
                            if isinstance(step, dict) and step.get("direct_apply") and step.get("tool") == "edit_file_patch":
                                req = step.get("required_args", {})
                                if isinstance(req, dict) and req.get("old_str") and req.get("new_str"):
                                    try:
                                        exec_registry.call(
                                            "edit_file_patch",
                                            path=req.get("path", target_file),
                                            old_str=req["old_str"],
                                            new_str=req["new_str"],
                                        )
                                    except Exception as _exc:
                                        _direct_apply_errors.append(
                                            f"agent7_signature direct_apply failed: {_exc}"
                                        )

                from orchestrator.tools import run_lean_verify
                verify = run_lean_verify(target_file)
                verify_exit = int(verify.get("exit_code", 1)) if isinstance(verify, dict) else 1
                verify_sorry = int(verify.get("sorry_count", -1)) if isinstance(verify, dict) else -1
                outcome = {
                    "outcome": "success" if verify_exit == 0 and verify_sorry == 0 else "failed",
                    "exit_code": verify_exit,
                    "sorry_count": verify_sorry,
                    "error_count": _error_count_from_verify(
                        verify if isinstance(verify, dict) else {},
                        _coerce_errors_text(verify.get("errors", "") if isinstance(verify, dict) else ""),
                    ),
                }
                current_errors = _coerce_errors_text(verify.get("errors", current_errors) if isinstance(verify, dict) else current_errors)
                _has_verified_after_state = True

            elif action == "agent7_then_agent6":
                console.print("  [Agent8→Agent7→Agent6] Dispatching signature + glue...")
                a7_prompt = _resolve_decision_prompt(
                    decision, "agent7_targeted_prompt", targeted_prompt
                )
                a6_prompt = _resolve_decision_prompt(
                    decision, "agent6_targeted_prompt", targeted_prompt
                )
                result = _agent8_run_agent7_then_agent6(
                    target_file, current_errors, a7_prompt, a6_prompt,
                    agent9_plan=agent9_plan,
                )
                # Safety check for result dict
                if not isinstance(result, dict):
                    result = {"exit_code": 1, "sorry_count": -1, "errors": "Agent7→Agent6 result was not a dict"}
                outcome = {
                    "outcome": "success" if result.get("exit_code", 1) == 0 and result.get("sorry_count", -1) == 0 else "failed",
                    "exit_code": result.get("exit_code", 1),
                    "sorry_count": result.get("sorry_count", -1),
                    "error_count": _count_error_lines(_coerce_errors_text(result.get("errors", ""))),
                }
                current_errors = _coerce_errors_text(result.get("errors", current_errors))
                _has_verified_after_state = True

                # Update per-lemma status from the dispatch result.
                _max_lemma_att = RETRY_LIMITS.get("AGENT8_MAX_LEMMA_ATTEMPTS", 3)
                for _lname in list(_pending_lemma_status.keys()):
                    if _lname in a6_prompt:
                        if result.get("stub_compile_failed"):
                            # Stub itself didn't compile — mark failed immediately.
                            _pending_lemma_status[_lname]["status"] = "failed"
                            console.print(
                                f"  [Agent8] Stub compile failed for '{_lname}' "
                                "— marking lemma as failed."
                            )
                        elif result.get("lemma_proven"):
                            _pending_lemma_status[_lname]["status"] = "success"
                        elif outcome.get("outcome") != "dispatch_error":
                            # A real attempt was made but lemma is not proven yet.
                            _pending_lemma_status[_lname]["attempts"] += 1
                            if _pending_lemma_status[_lname]["attempts"] >= _max_lemma_att:
                                _pending_lemma_status[_lname]["status"] = "failed"
                                console.print(
                                    f"  [Agent8] Lemma '{_lname}' exhausted "
                                    f"{_max_lemma_att} attempt(s) — marking failed."
                                )

            elif action == "apollo_decompose_repair":
                console.print("  [Agent8→APOLLO] Dispatching decomposition repair...")
                from orchestrator.apollo_repair import run_apollo_decompose_repair
                from orchestrator.tools import run_lean_verify

                if _norm_sig:
                    _decompose_attempted_for_signature.add(_norm_sig)
                apollo_result = run_apollo_decompose_repair(
                    target_file=target_file,
                    current_errors=current_errors,
                    error_subtype=_error_subtype,
                    policy_context={
                        "trigger_reason": decision.get("trigger_reason", ""),
                        "tick": tick,
                    },
                )
                _apollo_status = str(apollo_result.get("status", "failed"))
                _apollo_failure_kind = str(apollo_result.get("failure_kind", "strategy_failure"))
                if _apollo_status == "success":
                    verify = run_lean_verify(target_file)
                    outcome = {
                        "outcome": "success"
                        if int(verify.get("exit_code", 1)) == 0
                        and int(verify.get("sorry_count", -1)) == 0
                        else "failed",
                        "exit_code": int(verify.get("exit_code", 1)),
                        "sorry_count": int(verify.get("sorry_count", -1)),
                        "apollo_trigger_reason": decision.get("trigger_reason", ""),
                        "apollo_summary": apollo_result.get("summary", ""),
                        "error_count": _error_count_from_verify(
                            verify,
                            _coerce_errors_text(verify.get("errors", "")),
                        ),
                    }
                    current_errors = _coerce_errors_text(verify.get("errors", current_errors))
                    _has_verified_after_state = True
                else:
                    _graph_nodes = apollo_result.get("subproblem_graph", []) or []
                    if isinstance(_graph_nodes, list) and _graph_nodes:
                        _serial_subproblem_queue = [n for n in _graph_nodes if isinstance(n, dict)]
                    # Deterministic fallback map required by Stage-2 policy.
                    _fallback_action = _apollo_fallback_from_failure_kind(
                        _apollo_failure_kind
                    )
                    console.print(
                        "  [Agent8→APOLLO] failed "
                        f"(kind={_apollo_failure_kind}); fallback={_fallback_action}"
                    )
                    if _fallback_action == "agent7_signature":
                        _base_a7_prompt = _resolve_decision_prompt(
                            decision, "agent7_targeted_prompt", targeted_prompt
                        )
                        a7_prompt = (
                            f"[APOLLO fallback from {_apollo_failure_kind}] "
                            + _base_a7_prompt
                        )
                        a7_plan, _a7_raw = _agent8_run_agent7(
                            target_file, current_errors, a7_prompt
                        )
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
                                        except Exception as _exc:
                                            _direct_apply_errors.append(
                                                f"apollo_fallback(agent7) direct_apply failed: {_exc}"
                                            )
                        verify = run_lean_verify(target_file)
                        outcome = {
                            "outcome": "success"
                            if int(verify.get("exit_code", 1)) == 0
                            and int(verify.get("sorry_count", -1)) == 0
                            else "failed",
                            "exit_code": int(verify.get("exit_code", 1)),
                            "sorry_count": int(verify.get("sorry_count", -1)),
                            "apollo_fallback_action": _fallback_action,
                            "apollo_failure_kind": _apollo_failure_kind,
                            "error_count": _error_count_from_verify(
                                verify,
                                _coerce_errors_text(verify.get("errors", "")),
                            ),
                        }
                        current_errors = _coerce_errors_text(verify.get("errors", current_errors))
                        _has_verified_after_state = True
                    elif _fallback_action == "agent7_then_agent6":
                        _base_a7_prompt = _resolve_decision_prompt(
                            decision, "agent7_targeted_prompt", targeted_prompt
                        )
                        a7_prompt = (
                            f"[APOLLO fallback from {_apollo_failure_kind}] "
                            + _base_a7_prompt
                        )
                        a6_prompt = _resolve_decision_prompt(
                            decision, "agent6_targeted_prompt", targeted_prompt
                        )
                        result = _agent8_run_agent7_then_agent6(
                            target_file,
                            current_errors,
                            a7_prompt,
                            a6_prompt,
                            agent9_plan=agent9_plan,
                        )
                        outcome = {
                            "outcome": "success"
                            if result["exit_code"] == 0 and result["sorry_count"] == 0
                            else "failed",
                            "exit_code": result["exit_code"],
                            "sorry_count": result["sorry_count"],
                            "apollo_fallback_action": _fallback_action,
                            "apollo_failure_kind": _apollo_failure_kind,
                            "error_count": _count_error_lines(
                                _coerce_errors_text(result.get("errors", ""))
                            ),
                        }
                        current_errors = _coerce_errors_text(result.get("errors", current_errors))
                        _has_verified_after_state = True
                    else:
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
                            _init_lemma_status_from_plan(_new_plan)
                        _replan_verify = run_lean_verify(target_file)
                        outcome = {
                            "outcome": "replan_done",
                            "exit_code": int(_replan_verify.get("exit_code", 1)),
                            "sorry_count": int(_replan_verify.get("sorry_count", _current_sorry_count)),
                            "apollo_fallback_action": _fallback_action,
                            "apollo_failure_kind": _apollo_failure_kind,
                            "error_count": _error_count_from_verify(
                                _replan_verify,
                                _coerce_errors_text(_replan_verify.get("errors", "")),
                            ),
                        }
                        current_errors = _coerce_errors_text(_replan_verify.get("errors", current_errors))
                        _has_verified_after_state = True

            elif action == "agent9_replan":
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
                    _init_lemma_status_from_plan(_new_plan)
                    console.print(
                        "  [Agent8→Agent9] Re-plan succeeded. "
                        "Agent8 retains control for next tick."
                    )
                else:
                    console.print(
                        "  [Agent8→Agent9] Re-plan failed — keeping current plan and forcing investigation next tick."
                    )
                    _force_lookup_next_tick = True
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
                    "error_count": _error_count_from_verify(
                        _replan_verify,
                        _coerce_errors_text(_replan_verify.get("errors", "")),
                    ),
                }
                current_errors = _coerce_errors_text(_replan_verify.get("errors", current_errors))
                _has_verified_after_state = True

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
                _tick_timing["tick_total_ms"] = int((time.perf_counter() - _tick_started) * 1000.0)
                decision_history.append({
                    "tick": tick,
                    "action": action,
                    "repair_unit": _repair_unit,
                    "target_region": _target_region,
                    "target_theorem": decision.get("target_theorem"),
                    "allowed_span": decision.get("allowed_edit_lines"),
                    "candidate_id": str(outcome.get("candidate_id", "")),
                    "active_target": outcome.get("active_target", {}),
                    "error_signature": error_sig,
                    "canonical_error_signature": _canonical_sig,
                    "hypothesis": hypothesis,
                    "evidence_hash": _evidence_hash(evidence),
                    "investigation_tools": list(_investigation_tool_names),
                    "investigation_success": _has_real_investigation,
                    "investigation_failures": list(_investigation_failures),
                    "error_subtype": _error_subtype,
                    "verify_backend_used": _fresh_backend_used,
                    "verify_backend_reason": _fresh_backend_reason,
                    "route_effective": False,
                    "api_shape_verified": False,
                    "main_error_signature_changed": False,
                    "errors_before": _errors_before,
                    "errors_after": _errors_before,  # no dispatch happened
                    "top_error_count_before": _top_error_count_before,
                    "top_error_count_after": _top_error_count_before,
                    "error_count_delta": 0,
                    "action_cooldowns": dict(_action_cooldowns),
                    "sorry_delta": 0,
                    "forced_route_lock": _forced_route_lock,
                    "route_locked": _forced_route_lock,
                    "forced_route_reason": _forced_route_reason,
                    "network_cooldown_triggered": _network_cooldown_triggered,
                    "subtype_policy_stage": _subtype_policy_stage,
                    "blocker_status": _blocker_status,
                    "blocker_report": dict(_blocker_report or {}),
                    "tick_timing": dict(_tick_timing),
                    **outcome,
                })
                _debug_log(
                    algo_name, tick, decision, outcome,
                    ctx_char_len=len(ctx),
                    first_error_line=_extract_first_error_line(current_errors),
                    error_sig=error_sig,
                    investigation_rounds=_investigation_rounds_this_tick,
                    dispatch_prompt_len=len(targeted_prompt),
                    tick_timing=dict(_tick_timing),
                )
                return False, current_plan, current_errors

        except Exception as exc:
            console.print(f"  [Agent8] Dispatch error: {exc}")
            _is_net = _is_network_error(str(exc))
            outcome = {
                "outcome": "network_failure" if _is_net else "dispatch_error",
                "error": str(exc),
            }
            if action == "agent7_signature" and outcome["outcome"] in {"network_failure", "dispatch_error"}:
                _action_cooldowns["agent7_signature"] = max(
                    int(_action_cooldowns.get("agent7_signature", 0)),
                    max(1, int(RETRY_LIMITS.get("AGENT8_ROUTE_COOLDOWN_TICKS", 2))),
                )
                _network_cooldown_triggered = True
                _forced_route_lock = True
                _forced_route_reason = (
                    "agent7_signature dispatch/network failure: apply cooldown and force alternate route next tick."
                )
        _tick_timing["dispatch_ms"] = int((time.perf_counter() - _dispatch_started) * 1000.0)
        if _direct_apply_errors:
            outcome["direct_apply_errors"] = list(_direct_apply_errors)

        _post_obs_started = time.perf_counter()
        _obs = _compute_post_dispatch_observability(
            outcome=outcome,
            has_verified_after_state=_has_verified_after_state,
            errors_before=_errors_before,
            errors_after_candidate=current_errors,
            top_error_count_before=_top_error_count_before,
            sorry_before=_sorry_before,
            current_sorry_count=_current_sorry_count,
        )
        _has_verified_after_state = bool(_obs["has_verified_after_state"])
        _errors_after = str(_obs["errors_after"])
        _top_error_count_after = int(_obs["top_error_count_after"])
        _error_count_delta = int(_obs["error_count_delta"])
        _main_sig_changed = bool(_obs["main_error_signature_changed"])
        _route_effective = _obs["route_effective"]
        _current_sorry_count = int(_obs["sorry_after"])
        _sorry_delta = int(_obs["sorry_delta"])
        _tick_timing["post_observability_ms"] = int((time.perf_counter() - _post_obs_started) * 1000.0)
        if (
            _active_subproblem_node
            and outcome.get("outcome") not in {"success", "replan_done"}
        ):
            _node_id = str(_active_subproblem_node.get("id", ""))
            _attempts = int(_serial_subproblem_attempts.get(_node_id, 0))
            if _attempts < _serial_max_attempts:
                _serial_subproblem_queue.append(_active_subproblem_node)
        # api_shape_verified: True if Agent3 was dispatched for proof_api_mismatch
        # and transactional report contains required proof of lookup/patch/verify.
        _tx_valid = bool(isinstance(result, dict) and result.get("transaction_valid"))
        _api_shape_verified = (
            action == "agent3_tactical"
            and _error_subtype == _SUBTYPE_PROOF_API_MISMATCH
            and _tx_valid
        )

        _print_diagnostic_card(
            tick=tick,
            error_sig=error_sig,
            hypothesis=hypothesis,
            evidence=evidence,
            chosen_action=action,
            counterfactual=counterfactual,
            outcome=outcome.get("outcome", "?"),
            error_subtype=_error_subtype,
            api_shape_verified=_api_shape_verified,
            top_error_count_before=_top_error_count_before,
            top_error_count_after=_top_error_count_after,
            error_count_delta=_error_count_delta,
            main_error_signature_changed=_main_sig_changed,
            route_ticks_in_row=_route_streak_len(decision_history, action) + 1,
            route_status=(
                "Cooldown"
                if int(_action_cooldowns.get(action, 0)) > 0
                else "Active"
            ),
            node_id=(
                str(_active_subproblem_node.get("id", ""))
                if _active_subproblem_node
                else ""
            ),
            node_kind=(
                str(_active_subproblem_node.get("kind", ""))
                if _active_subproblem_node
                else ""
            ),
            node_attempt=(
                int(_serial_subproblem_attempts.get(str(_active_subproblem_node.get("id", "")), 0))
                if _active_subproblem_node
                else 0
            ),
            queue_remaining=len(_serial_subproblem_queue),
            forced_route_lock=_forced_route_lock,
            forced_route_reason=_forced_route_reason,
            network_cooldown_triggered=_network_cooldown_triggered,
            subtype_policy_stage=_subtype_policy_stage,
            investigation_success=_has_real_investigation,
            allowed_span=str(decision.get("allowed_edit_lines", "") or ""),
            candidate_id=str(outcome.get("candidate_id", "")),
        )

        # 6. Record decision
        _tick_timing["tick_total_ms"] = int((time.perf_counter() - _tick_started) * 1000.0)
        decision_history.append({
            "tick": tick,
            "action": action,
            "repair_unit": _repair_unit,
            "target_region": _target_region,
            "target_theorem": decision.get("target_theorem"),
            "allowed_span": decision.get("allowed_edit_lines"),
            "candidate_id": str(outcome.get("candidate_id", "")),
            "active_target": outcome.get("active_target", {}),
            "error_signature": error_sig,
            "canonical_error_signature": _canonical_sig,
            "hypothesis": hypothesis,
            "evidence_hash": _evidence_hash(evidence),
            "investigation_tools": list(_investigation_tool_names),
            "investigation_success": _has_real_investigation,
            "investigation_failures": list(_investigation_failures),
            "error_subtype": _error_subtype,
            "verify_backend_used": _fresh_backend_used,
            "verify_backend_reason": _fresh_backend_reason,
            "route_effective": _route_effective,
            "api_shape_verified": _api_shape_verified,
            "main_error_signature_changed": _main_sig_changed,
            "errors_before": _errors_before,
            "errors_after": _errors_after,
            "top_error_count_before": _top_error_count_before,
            "top_error_count_after": _top_error_count_after,
            "error_count_delta": _error_count_delta,
            "action_cooldowns": dict(_action_cooldowns),
            "sorry_delta": _sorry_delta,
            "forced_route_lock": _forced_route_lock,
            "route_locked": _forced_route_lock,
            "forced_route_reason": _forced_route_reason,
            "network_cooldown_triggered": _network_cooldown_triggered,
            "subtype_policy_stage": _subtype_policy_stage,
            "blocker_status": _blocker_status,
            "blocker_report": dict(_blocker_report or {}),
            "lemma_status": dict(_pending_lemma_status),  # snapshot at this tick
            "tick_timing": dict(_tick_timing),
            "subproblem_node_id": (
                str(_active_subproblem_node.get("id", ""))
                if _active_subproblem_node
                else ""
            ),
            "subproblem_kind": (
                str(_active_subproblem_node.get("kind", ""))
                if _active_subproblem_node
                else ""
            ),
            "subproblem_queue_remaining": len(_serial_subproblem_queue),
            **outcome,
        })
        _debug_log(
            algo_name, tick, decision, outcome,
            ctx_char_len=len(ctx),
            first_error_line=_extract_first_error_line(current_errors),
            error_sig=error_sig,
            investigation_rounds=_investigation_rounds_this_tick,
            dispatch_prompt_len=len(targeted_prompt),
            tick_timing=dict(_tick_timing),
        )

        # 7. Check success
        if outcome.get("outcome") == "success":
            # Double-check with run_lean_verify
            from orchestrator.tools import run_lean_verify, run_repo_verify
            _recheck_started = time.perf_counter()
            verify = run_lean_verify(target_file)
            _tick_timing["success_recheck_ms"] = int((time.perf_counter() - _recheck_started) * 1000.0)
            exit_code = int(verify.get("exit_code", 1))
            sorry_count = int(verify.get("sorry_count", -1))
            if exit_code == 0 and sorry_count == 0:
                console.print(
                    f"[green bold][Agent8] Success at tick {tick}! "
                    "Build clean, 0 sorry."
                )
                return True, current_plan, ""
            # Not actually clean — update errors and continue
            current_errors = _coerce_errors_text(verify.get("errors", current_errors))
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
            "  [Agent8] Convergence: "
            f"subtype={_error_subtype} action={action} "
            f"delta={_error_count_delta:+d} "
            f"signature_changed={_main_sig_changed} "
            f"route_effective={_route_effective}"
        )
        _tick_timing["tick_total_ms"] = int((time.perf_counter() - _tick_started) * 1000.0)

    console.print(
        f"[yellow][Agent8] Exhausted {max_steps} steps without success."
    )
    return False, current_plan, current_errors


# ---------------------------------------------------------------------------
# Mid-check entry point (soft gate)
# ---------------------------------------------------------------------------

def run_agent8_midcheck(
    target_file: str,
    current_plan: str,
    current_errors: str,
    *,
    agent2: "Agent | None" = None,
    agent9_plan: dict | None = None,
    decision_history: list[dict] | None = None,
    turns_elapsed: int = 0,
    baseline_errors: str = "",
) -> dict:
    """Make a single Agent8 routing decision during the Agent3 per-sorry loop.

    This is the "soft gate" mid-check: it does NOT dispatch any agents itself.
    It returns a decision dict so the caller (main.py) can choose whether to
    let Agent3 continue or hand off to the appropriate specialized agent.

    Returns a dict with at least:
        {
            "action":          str,   # agent3_tactical | agent7_signature |
                                      # agent7_then_agent6 | apollo_decompose_repair |
                                      # agent9_replan |
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
    from orchestrator.tools import run_lean_verify as _midcheck_verify

    console.print(
        f"\n[bold magenta][Agent8 MidCheck] Soft-gate at turn {turns_elapsed} "
        f"for {algo_name}"
    )

    _fresh = _midcheck_verify(target_file)
    current_errors = _coerce_errors_text(_fresh.get("errors", current_errors))
    _fresh_backend_used = str(_fresh.get("verify_backend_used", ""))
    _fresh_backend_reason = str(_fresh.get("verify_backend_reason", ""))
    _structured_errors = _parse_lean_errors(current_errors)
    _current_error_line = _extract_first_error_line(current_errors)
    _prioritized_current_errors = _prioritize_error_text(
        _structured_errors,
        current_errors,
        _current_error_line,
        target_file,
    )
    _baseline_structured_errors = _parse_lean_errors(baseline_errors)
    _baseline_error_line = _extract_first_error_line(baseline_errors)
    _prioritized_baseline_errors = _prioritize_error_text(
        _baseline_structured_errors,
        baseline_errors,
        _baseline_error_line,
        target_file,
    )
    _canonical_sig = _canonical_error_signature(current_errors)

    # Classify error subtype for mid-check (same logic as main loop).
    _mc_error_subtype = _classify_error_subtype(
        current_errors, target_file,
        decision_history=_decision_history,
    )
    console.print(f"  [Agent8 MidCheck] error_subtype={_mc_error_subtype}")

    # Build context — reuse existing helper, no plan-update banner needed here.
    _same_sig_streak = 1
    for _entry in reversed(_decision_history):
        if str(_entry.get("canonical_error_signature", "")) == _canonical_sig:
            _same_sig_streak += 1
        else:
            break
    _stale_hint = ""
    if _same_sig_streak >= 3:
        try:
            _ctx_registry = ToolRegistry()
            _ctx_registry.register_readonly_tools()
            _stale_hint = _build_stale_error_hint(
                _ctx_registry,
                target_file,
                current_errors,
                _current_error_line,
                _same_sig_streak,
            )
        except Exception:  # noqa: BLE001
            _stale_hint = ""
    ctx = _build_agent8_tick_context(
        target_file,
        _prioritized_current_errors,
        current_plan,
        _decision_history,
        agent9_plan=agent9_plan,
        plan_updated_tick=0,
        midcheck_mode=True,
        midcheck_turns_elapsed=turns_elapsed,
        baseline_errors=_prioritized_baseline_errors,
        error_subtype=_mc_error_subtype,
        canonical_error_signature=_canonical_sig,
        stale_error_hint=_stale_hint,
        verify_backend_used=_fresh_backend_used,
        verify_backend_reason=_fresh_backend_reason,
    )

    # Call Agent8 (single round, reduced investigation budget for speed).
    agent8 = Agent("decision_hub")
    _inv_registry = ToolRegistry()
    _inv_registry.register_investigation_tools()
    _max_inv = min(RETRY_LIMITS.get("AGENT8_INVESTIGATION_TURNS", 3), 2)
    _investigation_tools_this_tick: list[dict[str, Any]] = []
    raw_reply = _safe_llm_call(agent8, ctx, idempotent=True, max_attempts=3)

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
            _success = not (isinstance(_tr, dict) and _tr.get("error"))
            _investigation_tools_this_tick.append(
                {
                    "tool": str(_tn),
                    "success": _success,
                    "error": str(_tr.get("error", "")) if isinstance(_tr, dict) else "",
                }
            )
        raw_reply = _safe_llm_call(
            agent8,
            "Investigation results:\n"
            + json.dumps(_inv_results, indent=2, ensure_ascii=False)
            + "\n\nNow output your final JSON decision.",
            idempotent=True,
            max_attempts=2,
        )

    # Parse with one retry attempt before falling back.
    decision, _ = _parse_agent8_decision(raw_reply)
    if decision is None:
        # One explicit retry.
        raw_reply = _safe_llm_call(
            agent8,
            "Your response was not valid JSON. Return ONLY a single JSON "
            "object with the required fields: action, priority_level, reason, "
            "error_signature, hypothesis, evidence, confidence, "
            "counterfactual. targeted_prompt is optional. No markdown fences.",
            idempotent=True,
            max_attempts=2,
        )
        decision, _ = _parse_agent8_decision(raw_reply)

    if decision is None:
        console.print(
            "[yellow][Agent8 MidCheck] Parse failed — defaulting to agent3_tactical"
        )
        return {
            "action": "agent3_tactical",
            "reason": "Mid-check parse failure — letting Agent3 continue",
            "targeted_prompt": "",
            "error_signature": _canonical_sig,
            "priority_level": "P3",
            "hypothesis": "Keep local tactical iteration when mid-check response is malformed.",
            "repair_unit": _REPAIR_UNIT_LOCAL_PATCH,
            "target_region": _target_region_from_errors(current_errors),
            "evidence": [
                {"source": "midcheck", "snippet": "decision parse failed"},
                {"source": "lean_verify", "snippet": _canonical_sig},
            ],
            "confidence": 0.2,
            "counterfactual": "Do not escalate based on malformed routing response.",
        }

    if _is_structural_error(_canonical_sig, current_errors) and not _has_informative_investigation(
        _investigation_tools_this_tick
    ):
        console.print(
            "  [Agent8 MidCheck] Mandatory lookup gate: structural error requires "
            "a real read/search/check_lean_expr investigation."
        )
        decision["action"] = "agent3_tactical"
        decision["reason"] = (
            "Mid-check blocked: structural error without informative investigation."
        )
        decision["targeted_prompt"] = (
            "Perform read_file/search_in_file/search_codebase/check_lean_expr on the "
            "current failing declaration before deciding whether to escalate."
        )

    # Anti-loop check using the shared history.
    action, _antiloop_reason = _check_anti_loop(decision, _decision_history)
    if _antiloop_reason:
        console.print(f"  [AntiLoop/MidCheck] {action} ← {_antiloop_reason}")
        decision["action"] = action

    _mc_forced_route_lock = False
    _mc_forced_route_reason = ""

    # Consistent compile-first subtype routing (mirrors main loop).
    # derive from context if the decision carries the subtype
    _mc_subtype = decision.get("error_subtype") or _mc_error_subtype
    if _mc_subtype == _SUBTYPE_PROOF_API_MISMATCH and action == "agent7_signature":
        console.print(
            "  [Agent8 MidCheck subtype gate] proof_api_mismatch → "
            "overriding agent7_signature to agent3_tactical"
        )
        decision["action"] = "agent3_tactical"
        action = "agent3_tactical"
    elif _mc_subtype == _SUBTYPE_DECLARATION_API_MISMATCH and action == "agent3_tactical":
        # Only upgrade to agent7 if the error is clearly declaration-zone, not if mid-check
        # simply defaulted to agent3 due to the soft-gate preference.
        pass  # preserve soft-gate bias; agent3 can also fix declaration errors tactically

    # Route downweight for mid-check (same window as main loop).
    _midcheck_compile_first = int(_fresh.get("exit_code", 1)) != 0 and int(_fresh.get("sorry_count", 0)) == 0
    action, _mc_dw_reason = _check_route_downweight(
        action,
        _mc_subtype,
        _decision_history,
        compile_first_mode=_midcheck_compile_first,
        current_errors=current_errors,
        target_region=_target_region_from_errors(
            current_errors,
            fallback_span=str(decision.get("allowed_edit_lines", "") or ""),
        ),
        allowed_edit_lines=decision.get("allowed_edit_lines"),
    )
    if _mc_dw_reason:
        console.print(f"  [RouteDownweight/MidCheck] {action} ← {_mc_dw_reason}")
        decision["action"] = action

    # Explicit delta-based fallback in mid-check.
    _mc_cooldowns = {}
    if _decision_history:
        _mc_cooldowns = dict(_decision_history[-1].get("action_cooldowns", {}) or {})
    action, _mc_delta_reason = _apply_delta_force_fallback(
        action,
        _decision_history,
        _mc_cooldowns,
        error_subtype=_mc_subtype,
        compile_first_mode=_midcheck_compile_first,
        window=RETRY_LIMITS.get("AGENT8_FORCE_FALLBACK_WINDOW", 2),
        cooldown_ticks=RETRY_LIMITS.get("AGENT8_ROUTE_COOLDOWN_TICKS", 2),
        current_errors=current_errors,
        target_region=_target_region_from_errors(
            current_errors,
            fallback_span=str(decision.get("allowed_edit_lines", "") or ""),
        ),
        allowed_edit_lines=decision.get("allowed_edit_lines"),
    )
    if _mc_delta_reason:
        console.print(f"  [DeltaForceFallback/MidCheck] {action} ← {_mc_delta_reason}")
        decision["action"] = action
        _mc_forced_route_lock = True
        _mc_forced_route_reason = _mc_delta_reason

    # Hard gate + cooldown in mid-check, reusing latest cooldown snapshot.
    action, _mc_hard_reason = _apply_hard_route_gate(
        action,
        _mc_subtype,
        _decision_history,
        _mc_cooldowns,
        compile_first_mode=_midcheck_compile_first,
        window=RETRY_LIMITS.get("AGENT8_ROUTE_NO_DELTA_WINDOW", 3),
        cooldown_ticks=RETRY_LIMITS.get("AGENT8_ROUTE_COOLDOWN_TICKS", 2),
        current_errors=current_errors,
        target_region=_target_region_from_errors(
            current_errors,
            fallback_span=str(decision.get("allowed_edit_lines", "") or ""),
        ),
        allowed_edit_lines=decision.get("allowed_edit_lines"),
    )
    if _mc_hard_reason:
        console.print(f"  [HardRouteGate/MidCheck] {action} ← {_mc_hard_reason}")
        decision["action"] = action
        _mc_forced_route_lock = True
        _mc_forced_route_reason = _mc_hard_reason

    action, _mc_net_reason, _ = _apply_network_cooldown_fallback(
        action,
        _mc_subtype,
        _decision_history,
        _mc_cooldowns,
        cooldown_ticks=RETRY_LIMITS.get("AGENT8_ROUTE_COOLDOWN_TICKS", 2),
    )
    if _mc_net_reason:
        console.print(f"  [NetworkCooldown/MidCheck] {action} ← {_mc_net_reason}")
        decision["action"] = action
        _mc_forced_route_lock = True
        if not _mc_forced_route_reason:
            _mc_forced_route_reason = _mc_net_reason
    decision["error_signature"] = _canonical_sig
    decision["canonical_error_signature"] = _canonical_sig
    decision["investigation_tools"] = [
        str(item.get("tool", "")) for item in _investigation_tools_this_tick
    ]
    decision["investigation_success"] = _has_informative_investigation(_investigation_tools_this_tick)
    decision["investigation_failures"] = [
        item for item in _investigation_tools_this_tick if not bool(item.get("success"))
    ]
    decision["verify_backend_used"] = _fresh_backend_used
    decision["verify_backend_reason"] = _fresh_backend_reason

    # Compile-first guard in mid-check must respect forced-route lock.
    _action_before_cf = action
    action, _unused_prompt, _mc_cf_reason = _apply_compile_first_subtype_gate(
        action,
        _mc_subtype,
        "",
        forced_route_lock=_mc_forced_route_lock,
        current_errors=current_errors,
        decision_history=_decision_history,
        target_region=_target_region_from_errors(
            current_errors,
            fallback_span=str(decision.get("allowed_edit_lines", "") or ""),
        ),
        allowed_edit_lines=decision.get("allowed_edit_lines"),
    )
    if _mc_cf_reason:
        decision["action"] = action
        console.print(f"  [CompileFirst/MidCheck] {action} ← {_mc_cf_reason}")
    elif _mc_forced_route_lock and _action_before_cf != action:
        action = _action_before_cf
        decision["action"] = action
        console.print(
            "  [CompileFirst/MidCheck] skipped due to forced route lock: "
            f"{_mc_forced_route_reason}"
        )

    _mc_target_region = _target_region_from_errors(
        current_errors,
        fallback_span=str(decision.get("allowed_edit_lines", "") or ""),
    )
    _mc_repair_unit = _classify_repair_unit(
        action=action,
        error_subtype=_mc_subtype,
        current_errors=current_errors,
        decision_history=_decision_history,
        target_region=_mc_target_region,
        allowed_edit_lines=decision.get("allowed_edit_lines"),
    )
    decision["repair_unit"] = _mc_repair_unit
    decision["target_region"] = _mc_target_region
    decision["agent3_execution_mode"] = _agent3_execution_mode_for_repair(
        error_subtype=_mc_subtype,
        repair_unit=_mc_repair_unit,
        current_errors=current_errors,
        decision_history=_decision_history,
        target_region=_mc_target_region,
        allowed_edit_lines=decision.get("allowed_edit_lines"),
    )
    _mc_region_streak = _region_no_progress_streak(
        _decision_history,
        target_region=_mc_target_region,
        repair_unit=_mc_repair_unit,
    )
    if action == "human_missing_assumption" or (
        _mc_repair_unit == _REPAIR_UNIT_STATEMENT_GAP
        and _mc_region_streak >= int(RETRY_LIMITS.get("AGENT8_STATEMENT_GAP_REGION_THRESHOLD", 4)) - 1
    ):
        _mc_blocker_status = (
            _BLOCKER_CERTIFIED_STATEMENT_GAP
            if _mc_repair_unit == _REPAIR_UNIT_STATEMENT_GAP
            else _BLOCKER_CERTIFIED_STRUCTURAL_BLOCK
        )
        decision["blocker_status"] = _mc_blocker_status
        decision["blocker_report"] = _build_blocker_report(
            blocker_status=_mc_blocker_status,
            repair_unit=_mc_repair_unit,
            target_region=_mc_target_region,
            error_subtype=_mc_subtype,
            error_signature=_canonical_sig,
            decision_history=_decision_history,
            current_errors=current_errors,
        )

    _prev_errors = (
        str(_decision_history[-1].get("errors_after", ""))
        if _decision_history else current_errors
    )
    _mc_before = _count_error_lines(_prev_errors)
    _mc_after = _count_error_lines(current_errors)
    _mc_delta = _mc_after - _mc_before
    _mc_sig_changed = _signature_changed(_prev_errors, current_errors)

    console.print(
        f"  [Agent8 MidCheck] Decision: {decision.get('action')} "
        f"(P={decision.get('priority_level', '?')}) "
        f"| subtype={_mc_subtype} "
        f"| delta={_mc_delta:+d} "
        f"| signature_changed={_mc_sig_changed} "
        f"| reason=\"{decision.get('reason', '')[:80]}\""
    )

    return decision
