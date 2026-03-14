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

from orchestrator.agents import Agent, ToolRegistry
from orchestrator.config import RETRY_LIMITS
from orchestrator.file_io import load_file

console = Console()

# Required top-level keys that must appear in a valid Agent9 output.
_REQUIRED_KEYS = {"theorems", "recommended_order"}


def _validate_agent9_plan(obj: Any) -> bool:
    """Return True if *obj* is a well-formed Agent9 plan dict."""
    if not isinstance(obj, dict):
        return False
    if not _REQUIRED_KEYS.issubset(obj.keys()):
        return False
    if not isinstance(obj.get("theorems"), list):
        return False
    if not isinstance(obj.get("recommended_order"), list):
        return False
    return True


def _build_agent9_prompt(
    target_file: str,
    guidance_snippet: str,
    algo_name: str,
) -> str:
    """Build the initial prompt sent to Agent9."""
    try:
        scaffold_content = load_file(target_file)
    except FileNotFoundError:
        scaffold_content = "(scaffold file not found)"

    return (
        f"[AGENT9 — STRATEGY PLANNING]\n\n"
        f"Target algorithm: {algo_name}\n"
        f"Target file: {target_file}\n\n"
        "## Compiled Scaffold\n"
        f"```lean\n{scaffold_content}\n```\n\n"
        "## Approved Mathematical Plan (summary)\n"
        f"{guidance_snippet}\n\n"
        "Follow the protocol in your system prompt:\n"
        "1. Call search_in_file for EVERY theorem/lemma to get the exact line number.\n"
        "2. After all lookups are complete, output ONLY the JSON object — no prose, "
        "no markdown fences."
    )


def run_agent9_plan(
    target_file: str,
    guidance: str,
    algo_name: str,
) -> dict:
    """Run Agent9 to produce a structured proof plan from the compiled scaffold.

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

    initial_prompt = _build_agent9_prompt(target_file, guidance_snippet, algo_name)

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
            if _validate_agent9_plan(obj):
                theorem_count = len(obj.get("theorems", []))
                console.print(
                    f"  [Agent9] Plan ready: {theorem_count} theorem(s), "
                    f"order: {obj.get('recommended_order', [])}"
                )
                return obj
            # Parsed but schema invalid.
            feedback = (
                "Your JSON was parsed but failed schema validation. "
                "Required top-level keys: theorems (list), recommended_order (list). "
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
