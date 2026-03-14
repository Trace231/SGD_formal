"""Agent10 Scaffold Verifier — Phase 3a post-scaffold quality gate.

After Agent2 finishes the scaffold step (whether it compiled or not), Agent10
performs systematic verification and correction BEFORE sorry-filling begins.

Operating modes:
  Full-Correction  (scaffold_succeeded=False): runs all Phase A–E checks;
                   reads every import, traces every API access, fixes errors.
  Semantic-Verify  (scaffold_succeeded=True):  runs Phase D–E only (cross-
                   theorem consistency + plan alignment); applies light patches.

Protocol: lookup-then-batch-patch.
  1. Agent10 issues READ-ONLY lookup rounds until it has all imported APIs.
  2. Agent10 outputs a single JSON verdict with issues + patches.
  3. This module applies patches atomically via edit_file_patch.
  4. Final run_lean_verify confirms exit=0.
  5. If exit≠0 after 3 patch rounds, returns False (triggers abort).
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

# Required top-level keys in Agent10's JSON output.
_REQUIRED_KEYS = {"verdict", "issues", "patches"}
_VALID_VERDICTS = {"PASS", "PATCHED", "NEEDS_HUMAN"}

# Maximum lookup rounds before forcing a verdict.
_MAX_LOOKUP_ROUNDS = 12
# Maximum patch-apply-verify cycles.
_MAX_PATCH_ROUNDS = 3


def _register_agent10_tools(registry: ToolRegistry) -> None:
    """Register the tools Agent10 is allowed to use.

    Read-only access (for import tracing) + edit_file_patch + run_lean_verify.
    Explicitly excludes write_new_file to prevent wholesale rewrites.
    """
    from orchestrator.tools import edit_file_patch, run_lean_verify

    registry.register_readonly_tools()
    registry.register("edit_file_patch", edit_file_patch)
    registry.register("run_lean_verify", run_lean_verify)


def _validate_verdict(obj: Any) -> bool:
    """Return True if *obj* is a well-formed Agent10 verdict dict."""
    if not isinstance(obj, dict):
        return False
    if not _REQUIRED_KEYS.issubset(obj.keys()):
        return False
    if obj.get("verdict") not in _VALID_VERDICTS:
        return False
    if not isinstance(obj.get("issues"), list):
        return False
    if not isinstance(obj.get("patches"), list):
        return False
    return True


def _apply_patches(registry: ToolRegistry, patches: list[dict]) -> list[str]:
    """Apply a list of patch dicts via edit_file_patch.

    Each patch dict must have keys: file, old_str, new_str.
    Returns a list of error strings for any patches that failed.
    """
    errors: list[str] = []
    for i, patch in enumerate(patches):
        file_path = patch.get("file", "")
        old_str = patch.get("old_str", "")
        new_str = patch.get("new_str", "")
        if not file_path or old_str == new_str:
            continue
        try:
            result = registry.call(
                "edit_file_patch",
                path=file_path,
                old_str=old_str,
                new_str=new_str,
            )
            if isinstance(result, dict) and result.get("error"):
                errors.append(
                    f"Patch {i} on {file_path}: {result['error']}"
                )
        except Exception as exc:
            errors.append(f"Patch {i} on {file_path}: {exc}")
    return errors


def _build_agent10_prompt(
    target_file: str,
    guidance_snippet: str,
    algo_name: str,
    scaffold_succeeded: bool,
    build_errors: str,
) -> str:
    """Build the initial prompt sent to Agent10."""
    try:
        scaffold_content = load_file(target_file)
    except FileNotFoundError:
        scaffold_content = "(scaffold file not found or not yet written)"

    mode = (
        "Semantic-Verify (scaffold compiled — run Phase D and E only)"
        if scaffold_succeeded
        else "Full-Correction (scaffold did NOT compile — run Phase A through E)"
    )

    error_block = ""
    if not scaffold_succeeded and build_errors:
        error_block = (
            "## Build Errors Reported by Agent2\n"
            f"```\n{build_errors[:3000]}\n```\n\n"
        )

    return (
        f"[AGENT10 — SCAFFOLD VERIFICATION]\n\n"
        f"Target algorithm: {algo_name}\n"
        f"Target file: {target_file}\n"
        f"Operating mode: {mode}\n\n"
        f"## Scaffold Content\n"
        f"```lean\n{scaffold_content}\n```\n\n"
        f"{error_block}"
        "## Approved Mathematical Plan (summary)\n"
        f"{guidance_snippet}\n\n"
        "Follow the verification protocol in your system prompt.\n"
        "Step 1: Issue lookup rounds to read all import files (Phase A).\n"
        "Step 2: Run the applicable phases against what you read.\n"
        "Step 3: Output ONLY the final JSON verdict object — no prose, no markdown fences."
    )


def run_agent10_verify(
    target_file: str,
    guidance: str,
    algo_name: str,
    scaffold_succeeded: bool,
    build_errors: str = "",
) -> bool:
    """Run Agent10 to verify and correct the compiled scaffold.

    Parameters
    ----------
    target_file:
        Path to the scaffold file (relative to project root).
    guidance:
        The approved mathematical plan text from Phase 2.
    algo_name:
        Algorithm name (used only for display/logging).
    scaffold_succeeded:
        True if Agent2 produced a compiling scaffold (exit=0).
        False if Agent2 failed (exit=1); Agent10 will attempt correction.
    build_errors:
        Build error text from Agent2's final attempt (empty when succeeded).

    Returns
    -------
    bool
        True if the scaffold is verified (exit=0) after Agent10's work.
        False if Agent10 exhausts its budget without achieving exit=0.
    """
    guidance_chars = RETRY_LIMITS.get("AGENT10_GUIDANCE_CHARS", 4000)
    max_parse_retries = RETRY_LIMITS.get("AGENT10_MAX_PARSE_RETRIES", 3)
    guidance_snippet = guidance[:guidance_chars]

    mode_label = "Semantic-Verify" if scaffold_succeeded else "Full-Correction"
    console.rule(f"[bold blue]Agent10 — Scaffold Verifier ({mode_label})")
    console.print(f"  Target: {target_file}")

    # If Agent2 failed and did not even create the file, there is nothing for
    # Agent10 to patch.  Abort immediately.
    if not scaffold_succeeded and not Path(target_file).exists():
        console.print(
            "[yellow][Agent10] Target file does not exist — "
            "Agent2 never created it. Verification impossible."
        )
        return False

    registry = ToolRegistry()
    _register_agent10_tools(registry)

    agent10 = Agent("scaffold_verifier", extra_files=[target_file])

    initial_prompt = _build_agent10_prompt(
        target_file, guidance_snippet, algo_name, scaffold_succeeded, build_errors
    )

    raw_reply = agent10.call(initial_prompt)

    # -----------------------------------------------------------------------
    # Lookup rounds: Agent10 may call read_file / search_in_file before
    # producing the final verdict JSON.
    # -----------------------------------------------------------------------
    for _round in range(_MAX_LOOKUP_ROUNDS):
        try:
            payload = json.loads(raw_reply.strip())
        except (json.JSONDecodeError, ValueError):
            break  # not JSON → treat as final prose, attempt parse below

        if not (
            isinstance(payload, dict)
            and payload.get("type") == "lookup"
            and isinstance(payload.get("tool_calls"), list)
        ):
            break  # valid JSON but not a lookup request → treat as verdict

        # Execute lookup tool calls (read-only).
        results: list[dict] = []
        for tc in payload["tool_calls"]:
            tool_name = tc.get("tool", "")
            tool_args = tc.get("arguments", {}) or {}
            try:
                result = registry.call(tool_name, **tool_args)
            except Exception as exc:
                result = {"error": str(exc)}
            results.append({"tool": tool_name, "result": result})

        raw_reply = agent10.call(
            "Lookup results:\n"
            + json.dumps(results, indent=2, ensure_ascii=False)
            + "\n\nNow output your final JSON verdict (no markdown fences)."
        )

    # -----------------------------------------------------------------------
    # Parse Agent10's JSON verdict with retries.
    # -----------------------------------------------------------------------
    verdict_obj: dict | None = None
    for attempt in range(max_parse_retries):
        text = raw_reply.strip()
        # Strip accidental markdown fences.
        if text.startswith("```"):
            lines = text.splitlines()
            text = "\n".join(
                ln for ln in lines if not ln.strip().startswith("```")
            ).strip()

        try:
            obj = json.loads(text)
            if _validate_verdict(obj):
                verdict_obj = obj
                break
            feedback = (
                "Your JSON was parsed but failed schema validation. "
                "Required keys: verdict (PASS|PATCHED|NEEDS_HUMAN), "
                "issues (list), patches (list). "
                "Output ONLY the corrected JSON — no prose, no fences."
            )
        except (json.JSONDecodeError, ValueError):
            feedback = (
                "Your response is not valid JSON. "
                "Output ONLY a single JSON verdict object — no prose, no fences."
            )

        if attempt < max_parse_retries - 1:
            console.print(
                f"  [Agent10] Parse attempt {attempt + 1}/{max_parse_retries} failed — retrying."
            )
            raw_reply = agent10.call(feedback)

    if verdict_obj is None:
        console.print(
            "[yellow][Agent10] All parse attempts failed — "
            "scaffold verification inconclusive. Continuing with current state."
        )
        # Non-fatal: if scaffold already compiled, pass through.
        return scaffold_succeeded

    verdict = verdict_obj.get("verdict", "NEEDS_HUMAN")
    issues = verdict_obj.get("issues", [])
    patches = verdict_obj.get("patches", [])

    issue_count = len([i for i in issues if i.get("severity") == "ERROR"])
    console.print(
        f"  [Agent10] Verdict: {verdict} | "
        f"issues={len(issues)} (errors={issue_count}) | "
        f"patches={len(patches)}"
    )

    for issue in issues:
        sev = issue.get("severity", "?")
        phase = issue.get("phase", "?")
        loc = issue.get("location", "?")
        desc = issue.get("description", "")[:120]
        console.print(f"    [{sev}] {phase} @ {loc}: {desc}")

    # -----------------------------------------------------------------------
    # PASS: scaffold is already verified — nothing to do.
    # -----------------------------------------------------------------------
    if verdict == "PASS":
        console.print("  [Agent10] Scaffold verified — no issues found.")
        return True

    # -----------------------------------------------------------------------
    # NEEDS_HUMAN: Agent10 found issues but cannot safely patch.
    # -----------------------------------------------------------------------
    if verdict == "NEEDS_HUMAN":
        console.print(
            "[yellow][Agent10] Issues found but no safe patches — "
            "human intervention recommended. Aborting scaffold phase."
        )
        return False

    # -----------------------------------------------------------------------
    # PATCHED: apply the patches, then re-verify.
    # Allow up to _MAX_PATCH_ROUNDS cycles in case the first patch batch
    # reveals secondary issues.
    # -----------------------------------------------------------------------
    current_patches = patches
    for patch_round in range(1, _MAX_PATCH_ROUNDS + 1):
        if not current_patches:
            console.print(
                f"  [Agent10] Patch round {patch_round}: no patches to apply — stopping."
            )
            break

        console.print(
            f"  [Agent10] Patch round {patch_round}/{_MAX_PATCH_ROUNDS}: "
            f"applying {len(current_patches)} patch(es)..."
        )
        patch_errors = _apply_patches(registry, current_patches)
        if patch_errors:
            for pe in patch_errors:
                console.print(f"    [yellow][Agent10] Patch error: {pe}")

        # Verify after patching.
        try:
            verify_result = registry.call("run_lean_verify", target_file)
        except Exception as exc:
            console.print(f"  [Agent10] Verify call failed: {exc}")
            break

        exit_code = int(verify_result.get("exit_code", 1))
        sorry_count = int(verify_result.get("sorry_count", 0))
        errors_text = str(verify_result.get("errors", ""))

        console.print(
            f"  [Agent10] After patch round {patch_round}: "
            f"exit={exit_code}, sorry={sorry_count}"
        )

        if exit_code == 0:
            console.print(
                f"[green]  [Agent10] Scaffold verified after {patch_round} "
                f"patch round(s): exit=0, sorry={sorry_count}."
            )
            return True

        # Still failing — ask Agent10 for another correction round.
        if patch_round < _MAX_PATCH_ROUNDS:
            console.print(
                f"  [Agent10] Errors remain — requesting follow-up correction "
                f"(round {patch_round + 1}/{_MAX_PATCH_ROUNDS})..."
            )
            followup_prompt = (
                f"[AGENT10 — FOLLOW-UP CORRECTION (round {patch_round + 1})]\n\n"
                "The previous patches were applied but the scaffold still does not compile.\n\n"
                f"## Remaining Build Errors\n```\n{errors_text[:2000]}\n```\n\n"
                "## Current Scaffold\n"
                f"```lean\n{load_file(target_file)}\n```\n\n"
                "Repeat the verification protocol for the remaining errors only.\n"
                "Issue lookup rounds if needed, then output your updated JSON verdict."
            )
            # Reset agent context to avoid pollution from previous round.
            agent10.reset()
            raw_reply = agent10.call(followup_prompt)

            # Lookup rounds for follow-up.
            for _ in range(_MAX_LOOKUP_ROUNDS):
                try:
                    payload = json.loads(raw_reply.strip())
                except (json.JSONDecodeError, ValueError):
                    break
                if not (
                    isinstance(payload, dict)
                    and payload.get("type") == "lookup"
                    and isinstance(payload.get("tool_calls"), list)
                ):
                    break
                results = []
                for tc in payload["tool_calls"]:
                    tool_name = tc.get("tool", "")
                    tool_args = tc.get("arguments", {}) or {}
                    try:
                        result = registry.call(tool_name, **tool_args)
                    except Exception as exc:
                        result = {"error": str(exc)}
                    results.append({"tool": tool_name, "result": result})
                raw_reply = agent10.call(
                    "Lookup results:\n"
                    + json.dumps(results, indent=2, ensure_ascii=False)
                    + "\n\nNow output your updated JSON verdict (no markdown fences)."
                )

            # Parse follow-up verdict.
            next_verdict: dict | None = None
            for attempt in range(max_parse_retries):
                text = raw_reply.strip()
                if text.startswith("```"):
                    lines = text.splitlines()
                    text = "\n".join(
                        ln for ln in lines if not ln.strip().startswith("```")
                    ).strip()
                try:
                    obj = json.loads(text)
                    if _validate_verdict(obj):
                        next_verdict = obj
                        break
                    feedback = (
                        "Schema invalid. Required: verdict, issues (list), patches (list). "
                        "Output ONLY the JSON."
                    )
                except (json.JSONDecodeError, ValueError):
                    feedback = "Not valid JSON. Output ONLY the JSON verdict object."
                if attempt < max_parse_retries - 1:
                    raw_reply = agent10.call(feedback)

            if next_verdict is None:
                console.print(
                    f"  [Agent10] Follow-up parse failed at round {patch_round + 1} — stopping."
                )
                break

            current_patches = next_verdict.get("patches", [])
            if next_verdict.get("verdict") in ("PASS", "NEEDS_HUMAN"):
                if next_verdict["verdict"] == "PASS":
                    console.print("  [Agent10] Follow-up verdict: PASS — no more patches needed.")
                    return True
                console.print(
                    "[yellow]  [Agent10] Follow-up verdict: NEEDS_HUMAN — stopping."
                )
                return False

    # Exhausted patch rounds without achieving exit=0.
    console.print(
        f"[yellow][Agent10] Patch budget exhausted ({_MAX_PATCH_ROUNDS} round(s)) "
        "without achieving exit=0 — scaffold verification failed."
    )
    return False
