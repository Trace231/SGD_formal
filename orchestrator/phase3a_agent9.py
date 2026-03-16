"""Agent9 Strategy Planner — Phase 3a post-scaffold step.

After Agent2's scaffold gate passes (exit_code=0, sorry-only), Agent9 reads the
compiled scaffold and produces a structured JSON proof plan.  This plan is threaded
into Agent8's context so the Decision Hub can make better-informed dispatch decisions.

The plan is strictly additive: if Agent9 fails (JSON parse error, exception, etc.)
the system logs a warning and Phase 3 continues with an empty plan dict.
"""
from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from rich.console import Console
from rich.panel import Panel

from orchestrator.agents import Agent, ToolRegistry
from orchestrator.contracts import (
    AGENT9_ALLOWED_DIFFICULTIES,
    AGENT9_REQUIRED_KEYS,
    AGENT9_REQUIRED_THEOREM_FIELDS,
)
from orchestrator.config import RETRY_LIMITS
from orchestrator.file_io import load_file

console = Console()

# Re-export local names for backward compatibility with tests/importers.
_REQUIRED_KEYS = AGENT9_REQUIRED_KEYS
_REQUIRED_THEOREM_FIELDS = AGENT9_REQUIRED_THEOREM_FIELDS
_ALLOWED_DIFFICULTIES = AGENT9_ALLOWED_DIFFICULTIES

# Max characters per console panel when printing the full plan.
_PLAN_PRINT_CHUNK = 8000


def _validate_agent9_plan(obj: Any) -> tuple[bool, str]:
    """Validate a parsed Agent9 plan dict with strict, executable-quality checks.

    Returns (True, "") on success.
    Returns (False, feedback_msg) on failure where feedback_msg is a targeted
    correction instruction to be fed back to Agent9 for a retry.

    Hard requirements (all must pass for (True, "") to be returned):
    - Top-level keys: theorems (non-empty list), recommended_order (list).
    - recommended_order is a permutation of all theorem names (no extras, no gaps).
    - Each theorem has: name, proof_strategy, key_lib_lemmas, dependencies.
    - Each theorem has a line-number field (lean_statement_line OR line_number).
    - missing_glue_lemmas entries are dicts with name + proposed_lean_type.
    Optional fields:
    - first_action_patch_hint: string
    - expected_lean_shape: string
    """
    if not isinstance(obj, dict):
        return False, "Response is not a JSON object."

    missing_top = _REQUIRED_KEYS - set(obj.keys())
    if missing_top:
        return False, (
            f"Missing required top-level keys: {sorted(missing_top)}. "
            "Required: theorems (non-empty list), recommended_order (list)."
        )

    theorems = obj.get("theorems")
    if not isinstance(theorems, list) or len(theorems) == 0:
        return False, (
            "'theorems' must be a non-empty list. "
            "List every theorem/lemma that appears in the scaffold file."
        )

    recommended_order = obj.get("recommended_order")
    if not isinstance(recommended_order, list):
        return False, "'recommended_order' must be a list of theorem name strings."
    if any(not isinstance(x, str) or not x.strip() for x in recommended_order):
        return False, "'recommended_order' must contain only non-empty theorem name strings."
    if len(recommended_order) != len(set(recommended_order)):
        return False, "'recommended_order' contains duplicate theorem names."

    # recommended_order must be a permutation of all theorem names.
    theorem_name_list = [
        thm.get("name") for thm in theorems if isinstance(thm, dict)
    ]
    if any(not isinstance(n, str) or not n.strip() for n in theorem_name_list):
        return False, "Each theorem in 'theorems' must have a non-empty string name."
    if len(theorem_name_list) != len(set(theorem_name_list)):
        return False, "'theorems' contains duplicate theorem names."
    theorem_names = set(theorem_name_list)
    order_set = set(recommended_order)
    if theorem_names != order_set:
        extra = sorted(order_set - theorem_names)
        missing = sorted(theorem_names - order_set)
        return False, (
            f"'recommended_order' must be a permutation of all theorem names. "
            f"Extra entries not in theorems: {extra}. "
            f"Theorems missing from order: {missing}. "
            "Fix so recommended_order contains exactly the same names as in 'theorems'."
        )

    # Validate each theorem entry for executable-quality fields.
    for thm in theorems:
        if not isinstance(thm, dict):
            return False, "Each entry in 'theorems' must be a JSON object."
        name = thm.get("name", "<unnamed>")

        missing_fields = _REQUIRED_THEOREM_FIELDS - set(thm.keys())
        if missing_fields:
            return False, (
                f"Theorem '{name}' is missing required fields: {sorted(missing_fields)}. "
                "Every theorem must have: name, proof_strategy, key_lib_lemmas, "
                "dependencies, estimated_difficulty."
            )
        if not isinstance(name, str) or not name.strip():
            return False, "Each theorem entry must have a non-empty string 'name'."

        # Line number: accept lean_statement_line (preferred) or legacy line_number.
        if "lean_statement_line" not in thm and "line_number" not in thm:
            return False, (
                f"Theorem '{name}' is missing a line number. "
                "Call search_in_file to obtain the exact lean_statement_line value."
            )
        _line = thm.get("lean_statement_line", thm.get("line_number"))
        try:
            _line_i = int(_line)
        except Exception:
            return False, (
                f"Theorem '{name}' has non-numeric line number '{_line}'. "
                "Provide an exact integer line from search_in_file."
            )
        if _line_i <= 0:
            return False, f"Theorem '{name}' line number must be >= 1."

        # proof_strategy must be a non-empty, non-placeholder string.
        strategy = str(thm.get("proof_strategy", "")).strip()
        if not strategy:
            return False, (
                f"Theorem '{name}' has an empty proof_strategy. "
                "Provide an executable strategy: name the key tactic/lemma chain, "
                "the goal reduction steps, and any have sub-goals needed."
            )
        if strategy.lower() in {"todo", "tbd", "n/a", "unknown"}:
            return False, (
                f"Theorem '{name}' has placeholder proof_strategy '{strategy}'. "
                "Provide an executable, theorem-specific strategy."
            )

        if not isinstance(thm.get("dependencies"), list):
            return False, f"Theorem '{name}': dependencies must be a list."
        if any(not isinstance(d, str) or not d.strip() for d in thm.get("dependencies", [])):
            return False, (
                f"Theorem '{name}': dependencies must be non-empty theorem-name strings."
            )
        if not isinstance(thm.get("key_lib_lemmas"), list):
            return False, f"Theorem '{name}': key_lib_lemmas must be a list."
        if any(not isinstance(k, str) or not k.strip() for k in thm.get("key_lib_lemmas", [])):
            return False, (
                f"Theorem '{name}': key_lib_lemmas must be non-empty identifier strings."
            )
        difficulty = str(thm.get("estimated_difficulty", "")).strip().lower()
        if difficulty not in _ALLOWED_DIFFICULTIES:
            return False, (
                f"Theorem '{name}': estimated_difficulty must be one of "
                f"{sorted(_ALLOWED_DIFFICULTIES)}."
            )

        # missing_glue_lemmas entries must be dicts with required fields.
        if not isinstance(thm.get("missing_glue_lemmas", []), list):
            return False, f"Theorem '{name}': missing_glue_lemmas must be a list."
        for mgl in thm.get("missing_glue_lemmas", []):
            if isinstance(mgl, str):
                return False, (
                    f"Theorem '{name}': missing_glue_lemmas entry is a plain "
                    f"string '{mgl}'. "
                    "Each entry must be a dict with 'name', 'description', "
                    "and 'proposed_lean_type'."
                )
            if isinstance(mgl, dict):
                mgl_name = mgl.get("name", "<unnamed>")
                if not mgl.get("proposed_lean_type"):
                    return False, (
                        f"Theorem '{name}': missing_glue_lemma '{mgl_name}' "
                        "has no proposed_lean_type. "
                        "Provide a complete Lean 4 type signature ending with "
                        "':= by sorry'."
                    )

        # Optional executable hints, when present, must be strings.
        if "first_action_patch_hint" in thm and not isinstance(thm.get("first_action_patch_hint"), str):
            return False, (
                f"Theorem '{name}': first_action_patch_hint must be a string when provided."
            )
        if "expected_lean_shape" in thm and not isinstance(thm.get("expected_lean_shape"), str):
            return False, (
                f"Theorem '{name}': expected_lean_shape must be a string when provided."
            )

    return True, ""


def _build_agent9_prompt(
    target_file: str,
    guidance_snippet: str,
    algo_name: str,
    *,
    verify_state: dict | None = None,
) -> str:
    """Build the initial prompt sent to Agent9.

    Always includes the full scaffold Lean source.  When *verify_state* is
    provided (a dict returned by run_lean_verify) the current build state
    (exit_code, sorry_count, first build errors) is prepended so Agent9 knows
    exactly which goals remain open and which compilation errors must be resolved.
    """
    try:
        scaffold_content = load_file(target_file)
    except FileNotFoundError:
        scaffold_content = "(scaffold file not found)"

    # Build current build-state block so Agent9 knows what errors remain.
    if verify_state:
        _exit = verify_state.get("exit_code", "?")
        _sorry = verify_state.get("sorry_count", "?")
        _errs = verify_state.get("errors") or []
        if isinstance(_errs, list) and _errs:
            _err_lines = "\n".join(f"  - {str(e)[:200]}" for e in _errs[:5])
            _err_block = f"Build errors (first 5):\n{_err_lines}"
        else:
            _err_block = "Build: clean (no errors reported)"
        _verify_block = (
            f"## Current Build State\n"
            f"exit_code={_exit} | sorry_count={_sorry}\n"
            f"{_err_block}\n\n"
        )
    else:
        _verify_block = ""

    return (
        f"[AGENT9 — STRATEGY PLANNING]\n\n"
        f"Target algorithm: {algo_name}\n"
        f"Target file: {target_file}\n\n"
        "## Compiled Scaffold (full file — do NOT skip any theorem)\n"
        f"```lean\n{scaffold_content}\n```\n\n"
        f"{_verify_block}"
        "## Approved Mathematical Plan (summary)\n"
        f"{guidance_snippet}\n\n"
        "Follow the protocol in your system prompt:\n"
        "1. Call search_in_file for EVERY theorem/lemma to get the exact line number.\n"
        "2. After all lookups are complete, output ONLY the JSON object — no prose, "
        "no markdown fences."
    )


def _print_agent9_plan(obj: dict, title: str = "Agent9 — Full Proof Plan") -> None:
    """Print the full Agent9 plan JSON to the console in bounded chunks.

    Uses only the already-parsed dict — no extra API calls.  Large plans are
    split into _PLAN_PRINT_CHUNK-character panels so the terminal is not
    overwhelmed by a single enormous block.
    """
    plan_json = json.dumps(obj, indent=2, ensure_ascii=False)
    total = len(plan_json)
    if total <= _PLAN_PRINT_CHUNK:
        console.print(Panel(
            plan_json,
            title=f"[bold green]{title}",
            border_style="green",
        ))
    else:
        chunks = [plan_json[i:i + _PLAN_PRINT_CHUNK]
                  for i in range(0, total, _PLAN_PRINT_CHUNK)]
        console.print(
            f"  [Agent9] Full plan {total:,} chars "
            f"({len(chunks)} chunks follow):"
        )
        for idx, chunk in enumerate(chunks, 1):
            console.print(Panel(
                chunk,
                title=f"[bold green]{title}  [{idx}/{len(chunks)}]",
                border_style="green",
            ))


def run_agent9_plan(
    target_file: str,
    guidance: str,
    algo_name: str,
    *,
    verify_state: dict | None = None,
) -> dict:
    """Run Agent9 to produce a structured proof plan from the compiled scaffold.

    *verify_state* is an optional dict from run_lean_verify — when provided it
    is injected into the prompt so Agent9 knows which errors remain open.

    Returns a plan dict on success, or ``{}`` on any failure (graceful degradation).
    The caller (``phase3_prove`` in ``main.py``) should log a warning when ``{}``
    is returned but must NOT abort Phase 3.
    """
    max_rounds = RETRY_LIMITS.get("AGENT9_MAX_ROUNDS", 3)
    guidance_chars = RETRY_LIMITS.get("AGENT9_GUIDANCE_CHARS", 4000)
    guidance_snippet = guidance[:guidance_chars]

    console.rule("[bold blue]Agent9 — Strategy Planning")
    console.print(f"  Target: {target_file} | max_parse_retries: {max_rounds}")

    # Build read-only tool registry for Agent9.
    registry = ToolRegistry()
    registry.register_readonly_tools()

    agent9 = Agent("strategy_planner", extra_files=[target_file])

    initial_prompt = _build_agent9_prompt(
        target_file, guidance_snippet, algo_name,
        verify_state=verify_state,
    )

    # Agent9 may issue lookup rounds (same pattern as Agent8's investigation protocol).
    raw_reply = agent9.call(initial_prompt)

    # Handle lookup rounds: Agent9 may call search_in_file etc. before giving JSON.
    _max_lookup_rounds = 10  # generous budget; Agent9 needs one call per theorem
    for _ in range(_max_lookup_rounds):
        try:
            payload = json.loads(raw_reply)
        except (json.JSONDecodeError, ValueError):
            break  # not JSON at all → treat as final prose, parse below
        if not (
            isinstance(payload, dict)
            and payload.get("type") == "lookup"
            and isinstance(payload.get("tool_calls"), list)
        ):
            break  # valid JSON but not a lookup request → treat as final answer
        # Execute tool calls
        results: list[dict] = []
        for tc in payload["tool_calls"]:
            tool_name = tc.get("tool", "")
            tool_args = tc.get("arguments", {}) or {}
            try:
                result = registry.call(tool_name, **tool_args)
            except Exception as exc:
                result = {"error": str(exc)}
            results.append({"tool": tool_name, "result": result})
        raw_reply = agent9.call(
            "Lookup results:\n"
            + json.dumps(results, indent=2, ensure_ascii=False)
            + "\n\nNow output your final JSON plan (no markdown fences)."
        )

    # Attempt to parse the final JSON output, with retries.
    for attempt in range(max_rounds):
        # Strip accidental markdown fences.
        text = raw_reply.strip()
        if text.startswith("```"):
            lines = text.splitlines()
            text = "\n".join(
                ln for ln in lines if not ln.strip().startswith("```")
            ).strip()

        try:
            obj = json.loads(text)
            _valid, _feedback = _validate_agent9_plan(obj)
            if _valid:
                theorem_count = len(obj.get("theorems", []))
                console.print(
                    f"  [Agent9] Plan ready: {theorem_count} theorem(s), "
                    f"order: {obj.get('recommended_order', [])}"
                )
                # Print full plan to CLI — zero extra API cost.
                _print_agent9_plan(obj)
                return obj
            # Parsed but schema invalid — send targeted feedback.
            feedback = (
                f"Your JSON failed schema validation: {_feedback} "
                "Output ONLY the corrected JSON object — no prose, no fences."
            )
        except (json.JSONDecodeError, ValueError):
            feedback = (
                "Your response is not valid JSON. "
                "Output ONLY a single JSON object — no prose, no markdown fences."
            )

        if attempt < max_rounds - 1:
            console.print(
                f"  [Agent9] Parse attempt {attempt + 1}/{max_rounds} failed — retrying."
            )
            raw_reply = agent9.call(feedback)

    console.print(
        "[yellow][Agent9] All parse attempts failed — returning empty plan. "
        "Phase 3 will continue without Agent9 structured plan."
    )
    return {}


def run_agent9_replan(
    target_file: str,
    current_errors: str,
    current_plan: dict,
    algo_name: str,
    guidance: str,
) -> dict:
    """Re-run Agent9 with updated error context to produce a revised proof plan.

    Called by Agent8 when the current strategy is failing.  The prompt includes the
    current file state, the live errors, and the outdated plan so Agent9 can revise
    its JSON output in light of what actually went wrong.

    Returns a new plan dict on success, or ``{}`` on failure (graceful degradation).
    """
    max_rounds = RETRY_LIMITS.get("AGENT9_MAX_ROUNDS", 3)
    guidance_chars = RETRY_LIMITS.get("AGENT9_GUIDANCE_CHARS", 4000)

    try:
        scaffold_content = load_file(target_file)
    except FileNotFoundError:
        scaffold_content = "(file not found)"

    _current_plan_text = (
        json.dumps(current_plan, indent=2, ensure_ascii=False)
        if current_plan
        else "(none)"
    )

    console.rule("[bold blue]Agent9 — Strategy Re-Planning")
    console.print(
        f"  Target: {target_file} | Triggered by Agent8 (errors detected)"
    )

    registry = ToolRegistry()
    registry.register_readonly_tools()

    agent9 = Agent("strategy_planner", extra_files=[target_file])

    initial_prompt = (
        "[AGENT9 — STRATEGY RE-PLANNING]\n\n"
        f"Target algorithm: {algo_name}\n"
        f"Target file: {target_file}\n\n"
        "## Current File State\n"
        f"```lean\n{scaffold_content}\n```\n\n"
        "## Current Build Errors\n"
        f"```\n{current_errors[:2000]}\n```\n\n"
        "## Previous Plan (outdated — Agent8 called you because this failed)\n"
        f"{_current_plan_text[:2000]}\n\n"
        "## Original Mathematical Guidance\n"
        f"{guidance[:guidance_chars]}\n\n"
        "Revise the proof plan based on the current errors and file state. "
        "Follow the protocol in your system prompt:\n"
        "1. Call search_in_file for EVERY theorem/lemma to confirm exact line numbers.\n"
        "2. After all lookups, output ONLY the JSON plan object — no prose, no fences."
    )

    raw_reply = agent9.call(initial_prompt)

    # Same lookup-round protocol as run_agent9_plan.
    _max_lookup_rounds = 10
    for _ in range(_max_lookup_rounds):
        try:
            payload = json.loads(raw_reply)
        except (json.JSONDecodeError, ValueError):
            break
        if not (
            isinstance(payload, dict)
            and payload.get("type") == "lookup"
            and isinstance(payload.get("tool_calls"), list)
        ):
            break
        results: list[dict] = []
        for tc in payload["tool_calls"]:
            tool_name = tc.get("tool", "")
            tool_args = tc.get("arguments", {}) or {}
            try:
                result = registry.call(tool_name, **tool_args)
            except Exception as exc:
                result = {"error": str(exc)}
            results.append({"tool": tool_name, "result": result})
        raw_reply = agent9.call(
            "Lookup results:\n"
            + json.dumps(results, indent=2, ensure_ascii=False)
            + "\n\nNow output your revised JSON plan (no markdown fences)."
        )

    # Parse with retries — same logic as run_agent9_plan.
    for attempt in range(max_rounds):
        text = raw_reply.strip()
        if text.startswith("```"):
            lines = text.splitlines()
            text = "\n".join(
                ln for ln in lines if not ln.strip().startswith("```")
            ).strip()

        try:
            obj = json.loads(text)
            _valid, _feedback = _validate_agent9_plan(obj)
            if _valid:
                theorem_count = len(obj.get("theorems", []))
                console.print(
                    f"  [Agent9] Re-plan ready: {theorem_count} theorem(s), "
                    f"order: {obj.get('recommended_order', [])}"
                )
                # Print full re-plan for observability — zero extra API cost.
                _print_agent9_plan(obj, title="Agent9 — Full Re-Plan")
                return obj
            feedback = (
                f"Your JSON failed schema validation: {_feedback} "
                "Output ONLY the corrected JSON object — no prose, no fences."
            )
        except (json.JSONDecodeError, ValueError):
            feedback = (
                "Your response is not valid JSON. "
                "Output ONLY a single JSON object — no prose, no markdown fences."
            )

        if attempt < max_rounds - 1:
            console.print(
                f"  [Agent9] Re-plan parse attempt {attempt + 1}/{max_rounds} failed — retrying."
            )
            raw_reply = agent9.call(feedback)

    console.print(
        "[yellow][Agent9] Re-plan failed — returning empty dict. "
        "Agent8 will fall back to Agent2 re-planning."
    )
    return {}
