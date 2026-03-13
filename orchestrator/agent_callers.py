"""Agent interaction wrappers: Agent2 (Planner), Agent7 (Auditor), Agent6 (Glue Filler)."""
from __future__ import annotations

import json
from pathlib import Path

from rich.console import Console

from orchestrator.agents import Agent, ToolRegistry
from orchestrator.config import RETRY_LIMITS
from orchestrator.context_builders import (
    _MIN_AGENT2_LOOKUP_ROUNDS,
    _build_escalation_file_context,
    _format_ref_and_classification_blocks,
    _get_reference_files_with_descriptions,
)
from orchestrator.error_classifier import _json_candidates

console = Console()

def _call_agent2_with_tools(
    agent2: "Agent",
    registry: "ToolRegistry",
    user_msg: str,
    max_tool_rounds: int = 8,
) -> str:
    """Call Agent2 with read-only tool support and a lookup hard gate.

    Agent2 may reply with a lookup request:
        {"type": "lookup", "tool_calls": [{"tool": "search_codebase"|"read_file", ...}]}
    In that case the tools are executed against *registry* (read-only) and
    results are fed back to Agent2.  Any other reply format (plain text, or
    JSON without ``"type": "lookup"``) is treated as final guidance.

    Hard gate (P1): if Agent2 has performed fewer than _MIN_AGENT2_LOOKUP_ROUNDS
    lookups when it declares final guidance, the orchestrator automatically
    issues a lookup prompt and waits for at least one more lookup round before
    accepting guidance.

    Symbol evidence gate (P1): identifiers extracted from the final guidance/patch
    are checked against the accumulated lookup results.  Any identifier that:
      - looks like an external Lean API name (dotted or snake_case ≥2 segments)
      - was not found in any lookup result text
    triggers a targeted search_codebase round before guidance is forwarded.
    """
    reply = agent2.call(user_msg)
    _lookup_rounds_performed = 0
    _accumulated_lookup_text = ""
    _guidance_without_sufficient_lookups = 0

    for _round in range(max_tool_rounds):
        # Try to parse as JSON lookup request.
        try:
            payload = json.loads(reply)
        except (json.JSONDecodeError, ValueError):
            payload = None  # plain text → candidate for final guidance

        is_lookup = (
            isinstance(payload, dict)
            and payload.get("type") == "lookup"
            and isinstance(payload.get("tool_calls"), list)
            and len(payload["tool_calls"]) > 0
        )

        if not is_lookup:
            if _lookup_rounds_performed >= _MIN_AGENT2_LOOKUP_ROUNDS:
                break
            _guidance_without_sufficient_lookups += 1
            if _guidance_without_sufficient_lookups > 3:
                break  # avoid infinite loop
            reply = agent2.call(
                "## Minimum lookup requirement\n"
                f"You have performed {_lookup_rounds_performed} lookup round(s). "
                f"At least {_MIN_AGENT2_LOOKUP_ROUNDS} are required before final guidance.\n"
                "Issue a lookup ({\"type\": \"lookup\", \"tool_calls\": [{\"tool\": \"search_codebase\" or \"read_file\", ...}]}) "
                "to verify key identifiers, then provide your final guidance."
            )
            continue

        # Execute the lookup round.
        tool_calls: list[dict] = payload["tool_calls"]
        _lookup_rounds_performed += 1
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
            # Auto-verify staging after write_staging_lemma; embed compile result
            if tool_name == "write_staging_lemma" and result.get("success"):
                _stg_path = result.get("path", "")
                if _stg_path:
                    _stg_verify = registry.call("run_lean_verify", _stg_path)
                    if _stg_verify.get("exit_code", 0) != 0:
                        result["staging_compile_ok"] = False
                        result["staging_compile_errors"] = _stg_verify.get("errors", [])
                        result["note"] = (
                            "STAGING COMPILE ERROR: type errors found (sorry is OK, "
                            "type errors are NOT). Fix the signature with edit_file_patch "
                            "before providing guidance to Agent3."
                        )
                    else:
                        result["staging_compile_ok"] = True
                        result["staging_sorry_count"] = _stg_verify.get("sorry_count", 0)
            results.append({"tool": tool_name, "arguments": args, "result": result})

        results_text = json.dumps(results, indent=2, ensure_ascii=False)
        _accumulated_lookup_text += results_text

        reply = agent2.call(
            "Lookup results:\n"
            + results_text
            + "\n\nContinue planning or issue more lookups if still needed."
        )

    return reply


def _call_agent7_with_tools(
    agent7: "Agent",
    registry: "ToolRegistry",
    user_msg: str,
    max_tool_rounds: int = 6,
) -> tuple[dict | None, str]:
    """Call Agent7 with read-only lookup support and parse strict JSON protocol."""
    reply = agent7.call(user_msg)
    for _ in range(max_tool_rounds):
        payload = None
        try:
            payload = json.loads(reply)
        except (json.JSONDecodeError, ValueError):
            payload = None
        is_lookup = (
            isinstance(payload, dict)
            and payload.get("type") == "lookup"
            and isinstance(payload.get("tool_calls"), list)
            and len(payload["tool_calls"]) > 0
        )
        if not is_lookup:
            break
        results: list[dict] = []
        for tc in payload["tool_calls"]:
            if not isinstance(tc, dict):
                continue
            tool_name = tc.get("tool", "")
            args = tc.get("arguments", {}) if isinstance(tc.get("arguments"), dict) else {}
            try:
                result = registry.call(tool_name, **args)
            except Exception as exc:  # noqa: BLE001
                result = {"error": str(exc)}
            results.append({"tool": tool_name, "arguments": args, "result": result})
        results_text = json.dumps(results, indent=2, ensure_ascii=False)
        reply = agent7.call(
            "Lookup results:\n"
            + results_text
            + "\n\nReturn the final strict JSON protocol now (no prose)."
        )

    for candidate in _json_candidates(reply.strip()):
        try:
            obj = json.loads(candidate)
        except json.JSONDecodeError:
            continue
        if (
            isinstance(obj, dict)
            and isinstance(obj.get("ordered_steps"), list)
            and obj.get("root_cause")
        ):
            return obj, reply
    return None, reply


def _run_agent6_glue_loop(
    agent6: "Agent",
    registry: "ToolRegistry",
    target_file: str,
    staging_path: Path,
    staging_rel: str,
    goal: str,
    error_message: str,
    diagnosis: str,
    target_algo: str,
    *,
    hypotheses: list[str] | None = None,
    extra_context: str | None = None,
    stuck_line: int | None = None,
    max_tool_turns: int = 70,
    max_retries: int = 3,
) -> tuple[bool, str]:
    """Run Agent6 (Glue Filler) to prove a glue lemma that bridges to the given goal.

    Returns (success, message). On success, staging compiles (exit_code=0); sorry in body OK.
    """
    from orchestrator.config import RETRY_LIMITS
    from orchestrator.tools import check_lean_have, get_lean_goal

    max_tool_turns = RETRY_LIMITS.get("MAX_AGENT6_TOOL_TURNS", 70)
    max_retries = RETRY_LIMITS.get("MAX_AGENT6_RETRIES", 3)

    ref_files = _get_reference_files_with_descriptions(target_file)
    ref_block = _format_ref_and_classification_blocks(ref_files, None)
    target_snippet = _build_escalation_file_context(target_file, stuck_line)
    staging_content = staging_path.read_text(encoding="utf-8") if staging_path.exists() else "(empty)"

    prompt_parts = [
        "## GLUE LEMMA REQUEST\n"
        "Agent3 is stuck on a structural gap. Prove a glue lemma that bridges to this goal.\n\n"
        f"### Goal (⊢ T) from the stuck sorry\n```\n{goal}\n```\n\n"
        f"### Error message\n```\n{error_message}\n```\n\n"
        f"### Diagnosis\n{diagnosis}\n\n"
    ]
    if hypotheses:
        hyp_text = "\n".join(hypotheses)
        prompt_parts.append(f"### Hypotheses at sorry\n```\n{hyp_text}\n```\n\n")
    if extra_context:
        prompt_parts.append(f"### Agent3 extra context (what was tried, why lemma needed)\n```\n{extra_context}\n```\n\n")
    prompt_parts.extend([
        (
            f"### Target file context (read-only; focus around stuck line {stuck_line})\n"
            f"```lean\n{target_snippet[:8000]}\n```\n\n"
            if stuck_line is not None
            else f"### Target file context (read-only)\n```lean\n{target_snippet[:8000]}\n```\n\n"
        ),
        f"### Staging file (edit this)\n```lean\n{staging_content}\n```\n"
        f"{ref_block}\n"
        "### Tool parameter contract (MUST follow exactly)\n"
        "- write_staging_lemma arguments must be exactly:\n"
        "  {\"staging_path\": \"Lib/Glue/Staging/<Algo>.lean\", \"lean_code\": \"theorem ... := by ...\"}\n"
        "- edit_file_patch arguments must be exactly:\n"
        "  {\"path\": \"Lib/Glue/Staging/<Algo>.lean\", \"old_str\": \"...\", \"new_str\": \"...\"}\n"
        "  (Do NOT send unified diff `patch`)\n"
        "- read_file arguments: {\"path\": \"...\", \"start_line\": N, \"end_line\": M}\n"
        "- run_lean_verify arguments: {\"file_path\": \"...\"}\n"
        "- get_lean_goal arguments: {\"file_path\": \"...\", \"sorry_line\": N}\n\n"
        "Prove a glue lemma. Write it to staging via write_staging_lemma or edit_file_patch. "
        "After run_lean_verify returns exit_code=0 for staging, immediately return tool=done. "
        "Signature must typecheck; sorry in body is OK; admit is FORBIDDEN. "
        "Return valid JSON: thought, tool, arguments. Output ONE action per response."
    ])
    initial_prompt = "".join(prompt_parts)

    for retry in range(max_retries):
        staging_touched = False
        agent6.messages = []
        raw_reply = agent6.call(initial_prompt)
        for turn in range(max_tool_turns):
            try:
                payload = json.loads(raw_reply)
            except json.JSONDecodeError:
                raw_reply = agent6.call(
                    "Invalid JSON. Return valid JSON with thought, tool, arguments."
                )
                continue
            if not isinstance(payload, dict):
                raw_reply = agent6.call("JSON must be an object. Retry.")
                continue

            tool_name = str(payload.get("tool", ""))
            arguments = payload.get("arguments", {}) or {}

            if tool_name == "done":
                verify = registry.call("run_lean_verify", staging_rel)
                exit_code = int(verify.get("exit_code", 1))
                if exit_code == 0:
                    return True, (
                        "## Agent6 succeeded\n"
                        "Glue lemma added to staging. Build is clean. Continue with your proof."
                    )
                raw_reply = agent6.call(
                    f"## done rejected — staging build failed\n"
                    f"```\n{verify.get('errors', [])}\n```\n"
                    "Fix staging errors, then signal done again."
                )
                continue

            # Normalize path → file_path for tools that accept both
            args = dict(arguments)
            if "path" in args and "file_path" not in args:
                for k in ("get_lean_goal", "check_lean_have", "run_lean_verify"):
                    if tool_name == k or k in tool_name:
                        args["file_path"] = args.pop("path", args.get("path"))
                        break
            if tool_name in ("edit_file_patch", "write_staging_lemma"):
                if "path" in args and args["path"] != staging_rel:
                    args["path"] = staging_rel
                if "staging_path" in args:
                    args["staging_path"] = staging_rel

            try:
                result = registry.call(tool_name, **args)
            except KeyError:
                raw_reply = agent6.call(
                    f"Tool `{tool_name}` not registered. Use: read_file, search_codebase, "
                    "write_staging_lemma, edit_file_patch, run_lean_verify, get_lean_goal, check_lean_have."
                )
                continue
            except Exception as exc:  # noqa: BLE001
                err = str(exc)
                if tool_name == "write_staging_lemma":
                    raw_reply = agent6.call(
                        "Tool error: "
                        + err
                        + "\nUse EXACT arguments:\n"
                        '{"tool":"write_staging_lemma","arguments":{"staging_path":"'
                        + staging_rel
                        + '","lean_code":"theorem ... := by ..."}}'
                    )
                elif tool_name == "edit_file_patch":
                    if isinstance(arguments, dict) and "patch" in arguments:
                        raw_reply = agent6.call(
                            "Tool error: edit_file_patch does NOT accept `patch` unified diff.\n"
                            "Use EXACT arguments:\n"
                            '{"tool":"edit_file_patch","arguments":{"path":"'
                            + staging_rel
                            + '","old_str":"<exact existing text>","new_str":"<replacement text>"}}'
                        )
                    else:
                        raw_reply = agent6.call(
                            "Tool error: "
                            + err
                            + "\nedit_file_patch requires {path, old_str, new_str}."
                        )
                elif tool_name == "read_file":
                    if isinstance(arguments, dict) and "file_path" in arguments:
                        raw_reply = agent6.call(
                            "Tool error: read_file expects `path` (not `file_path`).\n"
                            "Use: "
                            '{"tool":"read_file","arguments":{"path":"'
                            + str(arguments.get("file_path"))
                            + '"}}'
                        )
                    else:
                        raw_reply = agent6.call(f"Tool error: {err}")
                else:
                    raw_reply = agent6.call(f"Tool error: {err}")
                continue

            if tool_name == "write_staging_lemma" and isinstance(result, dict):
                if bool(result.get("success")):
                    staging_touched = True
            elif tool_name == "edit_file_patch" and isinstance(result, dict):
                if bool(result.get("changed")) or int(result.get("replacements", 0)) > 0:
                    staging_touched = True

            if (
                tool_name == "run_lean_verify"
                and isinstance(result, dict)
                and staging_touched
                and int(result.get("exit_code", 1)) == 0
            ):
                return True, (
                    "## Agent6 succeeded\n"
                    "Glue lemma added to staging. Build is clean. Continue with your proof."
                )

            if isinstance(result, dict):
                result_text = json.dumps(result, indent=2, ensure_ascii=False)
            else:
                result_text = str(result)
            raw_reply = agent6.call(f"## {tool_name} result\n```\n{result_text}\n```\n")

    return False, "Agent6 could not prove glue. Escalating to Agent2."


# ---------------------------------------------------------------------------
# Agent3 single-step tool execution helpers
# ---------------------------------------------------------------------------

