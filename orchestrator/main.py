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
from collections import Counter
import time
from datetime import datetime, timezone
import functools
import hashlib
import json
import re
import subprocess
import sys
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path

from rich.console import Console
from rich.panel import Panel
from rich.progress import BarColumn, Progress, SpinnerColumn, TextColumn

from orchestrator.agents import (
    Agent,
    ToolRegistry,
    auto_repair_loop,
    escalate,
)
from orchestrator.assumption_repair import (
    apply_assumption_patches,
    all_goals_are_assumptions,
    classify_goal,
    extract_unsolved_goals,
    goals_to_patch_list,
)
from orchestrator.config import (
    AGENT_CONFIGS,
    AUDIT_FLUSH_INTERVAL_SECONDS,
    ALGORITHM_REFERENCES,
    DISABLE_PHASE4_PERSISTENCE,
    DOC_ANCHORS,
    LIB_GLUE_ANCHORS,
    MAX_PHASE3_RETRIES,
    PROJECT_ROOT,
    REFERENCE_FILES_WITH_DESCRIPTIONS,
    RETRY_LIMITS,
    ROUTING_PARAMS,
    UNKNOWN_IDENTIFIER_RENAME_MAP,
    _get_default_references,
    set_runtime_overrides,
)
from orchestrator.file_io import (
    load_file,
    snapshot_file,
)
from orchestrator.tools import (
    _path_to_lean_module,
)
from orchestrator.metrics import (
    MetricsStore,
    capture_physical_metrics,
    count_glue_tricks_sections,
)
from orchestrator.prompts import (
    AGENT_FILES,
    build_algorithm_card,
    build_error_classification_prompt,
    load_meta_prompt_a,
    load_meta_prompt_b,
)
from orchestrator.audit_logger import AuditLogger
from orchestrator.verify import (
    check_glue_tricks_gate,
    check_leverage_gate,
    check_used_in_tags,
)
from orchestrator.providers import (
    call_llm,
    reset_api_token_meters,
    start_token_usage_heartbeat,
)
from orchestrator.error_classifier import (
    _LEAN_ERROR_LINE_RE,
    _LEAN_STRUCTURED_ERROR_RE,
    _LEAN_JSON_ERROR_RE,
    _UNKNOWN_SYMBOL_RE,
    _TYPECLASS_FAIL_RE,
    _TYPE_MISMATCH_RE,
    _FIELD_NOTATION_RE,
    _DUPLICATE_DECL_RE,
    _PROOF_BODY_LINE_THRESHOLD,
    _parse_lean_errors,
    _json_candidates,
    _classify_lean_error_structured,
    _get_decl_zone_end,
    _build_decl_zone_map,
    _is_in_declaration_zone,
    _is_target_file_error,
    _extract_first_error_line,
    _infer_failure_class,
    _llm_classify_error,
)
from orchestrator.git_utils import (
    GitRunSnapshot,
    _file_hash,
    _git_diff_files,
    _git_untracked_files,
    _capture_lean_baseline,
    _git_head_sha,
    _git_is_dirty,
    _capture_git_run_snapshot,
    _restore_snapshot_on_success,
    _rollback_to_snapshot,
    _get_modified_lean_files,
    _ensure_algorithm_in_lakefile,
    _remove_algorithm_from_lakefile,
)
from orchestrator.agent_callers import (
    _call_agent2_scaffold,
    _call_agent2_with_tools,
    _call_agent7_with_tools,
    _run_agent6_glue_loop,
)
from orchestrator.phase4_helpers import (
    Gate4Error,
    _parse_persister_json,
    _apply_lib_insert,
)
from orchestrator.agent3_executor import (
    ExecutionResult,
    _execute_single_tool_and_format,
    _format_done_rejection,
)
from orchestrator.phase2 import (
    phase1_generate_prompt,
    phase1_generate_prompt_from_spec,
    phase2_plan_and_approve,
    _SUBGRADIENT_CONTEXT,
    _SYMBOL_WHITELIST,
)
from orchestrator.phase4 import phase4_persist
from orchestrator.phase5 import phase5_finalize
from orchestrator.context_builders import (
    _CATALOG_LEMMA_HEADING_RE,
    _LIB_DECL_RE,
    _MIN_AGENT2_LOOKUP_ROUNDS,
    _PROJECT_IDENT_RE,
    _LEAN_KEYWORDS,
    _TOP_LEVEL_KEYWORDS,
    _DECL_START,
    _ESCALATION_CHAR_LIMIT,
    _extract_imported_algo_sigs,
    _format_agent3_tool_feedback,
    _check_patch_symbols,
    _prioritize_error_text,
    _get_reference_files_with_descriptions,
    _format_ref_and_classification_blocks,
    _format_failed_approaches,
    _extract_error_identifiers,
    _infer_definition_file_from_registry,
    _build_stale_error_hint,
    _prequery_dependency_signatures,
    _generate_attempt_diagnosis,
    _prequery_sorry_goals,
    _prequery_error_line_goal,
    _parse_sorry_classification,
    _retrieve_catalog_context,
    _extract_symbol_manifest,
    _collect_lib_declaration_names,
    _extract_catalog_lemma_names,
    _extract_new_identifiers_from_guidance,
    _extract_declaration_skeleton,
    _build_escalation_file_context,
)

console = Console()


def _resolve_workspace_path(path_str: str) -> Path:
    path = Path(path_str)
    return path if path.is_absolute() else PROJECT_ROOT / path


def _build_skip_to_agent9_guidance(
    algorithm: str,
    update_rule: str,
    proof_sketch: str,
    archetype: str,
    *,
    spec_file: str | None = None,
) -> str:
    if spec_file:
        spec_text = load_file(spec_file)
        try:
            spec = json.loads(spec_text)
        except json.JSONDecodeError as exc:
            raise ValueError(
                f"Cannot parse --spec-file '{spec_file}' as JSON: {exc}"
            ) from exc
        spec_algorithm = str(spec.get("algorithm", algorithm)).strip() or algorithm
        spec_archetype = str(spec.get("archetype", archetype)).upper()
        return (
            "[STRICT SKIP-TO-AGENT9 GUIDANCE]\n"
            "Operator requested a direct jump to Agent9. "
            "Phase 1, Phase 2, and Phase 3 scaffold work were intentionally skipped.\n"
            f"Algorithm: {spec_algorithm}\n"
            f"Archetype: {spec_archetype}\n"
            f"Spec file: {spec_file}\n"
            "Treat the structured JSON below as the approved mathematical plan.\n\n"
            f"```json\n{spec_text}\n```"
        )
    return (
        "[STRICT SKIP-TO-AGENT9 GUIDANCE]\n"
        "Operator requested a direct jump to Agent9. "
        "Phase 1, Phase 2, and Phase 3 scaffold work were intentionally skipped.\n"
        f"Algorithm: {algorithm}\n"
        f"Archetype: {archetype.upper()}\n"
        f"Update rule: {update_rule}\n"
        f"Proof sketch: {proof_sketch}\n"
        "Treat this operator-supplied summary as the approved mathematical plan."
    )

# Agent3 single-step interactive loop: maximum tool turns per attempt.
# Archetype B gets a 1.5× multiplier applied in phase3_prove.
from orchestrator.phase3_agent3 import (
    MAX_AGENT3_TOOL_TURNS,
    phase3_prove,
)

def phase3b_fix_tags(
    target_file: str,
    missing: list[str],
    max_retries: int = 3,
) -> None:
    """Patch missing Used-in docstring tags without disturbing proof logic.

    Agent3 is explicitly told that the proof is already correct; it must only
    add or extend /-- ... -/ docstrings.  After each round, Gate 4 is
    re-checked; if tags are still absent the loop retries up to *max_retries*
    times before raising Gate4Error.
    """
    registry = ToolRegistry()
    registry.register_default_tools()
    agent3 = Agent("sorry_closer")

    missing = list(dict.fromkeys(missing))
    missing_str = "\n".join(f"  - {m}" for m in missing)
    guidance = (
        "DOCSTRING-ONLY TASK — DO NOT MODIFY ANY PROOF LOGIC OR TACTIC LINES.\n"
        "Your proof already compiled (build=OK, sorry=0) and is 100% correct.\n"
        "The ONLY problem is that the following declarations are missing a "
        "'Used in:' line in their /-- ... -/ docstring:\n"
        f"{missing_str}\n\n"
        "For each declaration, use 'edit_file_patch' to find its existing "
        "docstring opening '/--' and replace it with a version that includes "
        "a line such as:\n"
        "  Used in: `<main_theorem>` (<file>, <step>)\n"
        "If the declaration has no docstring yet, add one immediately before "
        "the declaration keyword (def/lemma/theorem/structure).\n"
        "Do NOT touch any :=, tactic, or import lines.\n"
        "After all edits call 'run_lean_verify' once to confirm the file "
        "still compiles.\n"
        f"Target file: {target_file}"
    )

    for attempt in range(1, max_retries + 1):
        console.print(
            f"  [Gate 4b] tag-fixup attempt {attempt}/{max_retries} …"
        )
        raw_reply = agent3.call(
            "Use tools to add missing 'Used in:' docstring tags.\n"
            "Return ONLY valid JSON with keys: thought, tool_calls.\n"
            'Each tool call: {"tool": "<name>", "arguments": {...}}.\n'
            "Allowed tools: read_file, search_in_file, edit_file_patch, run_lean_verify.\n\n"
            f"Task:\n{guidance}"
        )

        try:
            payload = json.loads(raw_reply)
        except json.JSONDecodeError:
            guidance = (
                "DOCSTRING-ONLY TASK — DO NOT MODIFY PROOF LOGIC.\n"
                "Your previous reply was not valid JSON.  "
                "Return ONLY a JSON object with 'thought' and 'tool_calls'.\n"
                f"Still missing tags for:\n{missing_str}"
            )
            continue

        tool_calls = payload.get("tool_calls", []) if isinstance(payload, dict) else []
        for call in tool_calls:
            if not isinstance(call, dict):
                continue
            tool_name = call.get("tool")
            arguments = call.get("arguments", {})
            if not isinstance(tool_name, str) or not isinstance(arguments, dict):
                continue
            try:
                registry.call(tool_name, **arguments)
            except Exception as exc:  # noqa: BLE001
                console.print(f"  [Gate 4b] tool '{tool_name}' error: {exc}")

        missing_now = list(dict.fromkeys(check_used_in_tags([target_file])))
        if not missing_now:
            console.print("[green]\\[Gate 4b] All Used-in tags patched.")
            return

        missing_str = "\n".join(f"  - {m}" for m in missing_now)
        guidance = (
            "DOCSTRING-ONLY TASK — DO NOT MODIFY PROOF LOGIC.\n"
            f"Still missing 'Used in:' tags for:\n{missing_str}\n"
            "Apply edit_file_patch for the remaining declarations only.  "
            "Do NOT touch any proof logic or tactic lines."
        )

    raise Gate4Error(missing_now)

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
    max_tool_turns: int | None = None,
    force_low_leverage: bool = False,
    progress_detail: str = "normal",
    skip_to_agent9: bool = False,
    spec_file: str | None = None,
    agent_runtime: str = "hybrid",
    codex_skip_only: bool = True,
    lean_verify_backend: str = "auto",
    codex_transport: str = "sdk",
) -> None:
    """Execute the full 5-phase pipeline."""

    reset_api_token_meters()
    set_runtime_overrides(
        agent_runtime=agent_runtime,
        codex_skip_only=codex_skip_only,
        lean_verify_backend=lean_verify_backend,
        codex_transport=codex_transport,
        skip_to_agent9=skip_to_agent9,
    )

    from orchestrator import config as runtime_config
    _a9_codex = int(runtime_config.should_use_codex_backend("strategy_planner", skip_to_agent9=skip_to_agent9))
    _a3_codex = int(runtime_config.should_use_codex_backend("sorry_closer", skip_to_agent9=skip_to_agent9))
    console.print(
        "[cyan][Runtime][/cyan] "
        f"agent_runtime={runtime_config.AGENT_RUNTIME} "
        f"codex_skip_only={int(runtime_config.CODEX_SKIP_ONLY)} "
        f"codex_transport={runtime_config.CODEX_TRANSPORT} "
        f"skip_to_agent9={int(bool(skip_to_agent9))}"
    )
    console.print(
        "[cyan][Runtime][/cyan] "
        f"strategy_planner_codex={_a9_codex} sorry_closer_codex={_a3_codex}"
    )

    if target_file is None:
        target_file = f"Algorithms/{algorithm}.lean"
    skip_guidance: str | None = None
    if skip_to_agent9:
        target_path = _resolve_workspace_path(target_file)
        if not target_path.exists():
            raise FileNotFoundError(
                "--skip-to-agent9 requires an existing target file; "
                f"missing: {target_file}"
            )
        target_text = target_path.read_text(encoding="utf-8")
        if not target_text.strip():
            raise ValueError(
                "--skip-to-agent9 requires a non-empty target file containing theorem/lemma declarations; "
                f"file is empty: {target_file}"
            )
        if not re.search(r"^\s*(theorem|lemma)\s+\S+", target_text, re.MULTILINE):
            raise ValueError(
                "--skip-to-agent9 requires theorem/lemma headers in the target file; "
                f"none found in: {target_file}"
            )
        skip_guidance = _build_skip_to_agent9_guidance(
            algorithm,
            update_rule,
            proof_sketch,
            archetype,
            spec_file=spec_file,
        )

    baseline_tracked, baseline_untracked = _capture_lean_baseline()
    audit = AuditLogger.get()
    run_id = audit.start_run(algorithm)
    success = False
    _lakefile_added_by_us = False
    files_modified: list[str] = []
    git_snapshot: GitRunSnapshot | None = None
    rollback_applied = False
    rollback_reason: str | None = None
    success_restore_ok = True
    success_restore_error: str | None = None
    git_snapshot = _capture_git_run_snapshot(run_id)
    merged_phase3_audit = {
        "execution_history": [],
        "attempt_failures": [],
        "agent7_invocations": [],
        "agent7_step_execution_log": [],
        "agent7_plan_revisions": [],
        "agent7_blocked_actions": [],
        "agent7_forced_trigger_count": 0,
        "agent7_force_gate_entries": [],
        "agent7_force_gate_rejections": [],
        "agent7_force_gate_reason_samples": [],
        "git_run_start_sha": git_snapshot.start_sha,
        "git_pre_run_dirty": git_snapshot.pre_run_dirty,
        "git_stash_used": git_snapshot.stash_used,
        "git_rollback_applied": False,
        "git_rollback_reason": None,
        "git_success_restore_ok": True,
        "git_success_restore_error": None,
        "estimated_token_consumption": 0,
        "retry_count": 0,
    }

    stop_token_hb: Callable[[], None] | None = None
    try:
        _hb_interval = float(__import__("os").getenv("ORCHESTRATOR_TOKEN_HEARTBEAT_SECONDS", "600"))
        stop_token_hb = start_token_usage_heartbeat(_hb_interval)
        with Progress(
            SpinnerColumn(),
            TextColumn("{task.description}"),
            BarColumn(),
            transient=True,
        ) as progress:
            task = progress.add_task("Orchestrating...", total=7)

            # Phase 1
            audit.set_phase(1)
            if skip_to_agent9:
                prover_prompt = skip_guidance or proof_sketch
                progress.update(
                    task,
                    description="Phase 1/7: Prover prompt generation skipped  [--skip-to-agent9]...",
                )
            elif spec_file:
                progress.update(task, description="Phase 1/7: Generating prover prompt  [Agent1B / spec]...")
                prover_prompt, algorithm, archetype = phase1_generate_prompt_from_spec(spec_file)
            else:
                progress.update(task, description="Phase 1/7: Generating prover prompt  [Agent1]...")
                prover_prompt = phase1_generate_prompt(
                    algorithm, update_rule, proof_sketch, archetype
                )
            progress.advance(task)

            # Register the algorithm module in lakefile.lean before Phase 3 so
            # that `lake build Algorithms.<name>` succeeds.  Tracked so we can
            # roll back on failure.
            _lakefile_added_by_us = _ensure_algorithm_in_lakefile(
                Path(target_file).stem
            )

            # Phase 2 (may loop on re-plan)
            success = False
            total_attempts = 0
            while not success:
                audit.set_phase(2)
                if skip_to_agent9:
                    plan = skip_guidance or proof_sketch
                    agent2 = None
                    progress.update(
                        task,
                        description="Phase 2/7: Agent2 planning skipped  [--skip-to-agent9]...",
                    )
                    progress.advance(task)
                else:
                    progress.update(task, description="Phase 2/7: Planning & approval  [Agent1 ↔ Agent2]...")
                    plan, agent1, agent2 = phase2_plan_and_approve(
                        prover_prompt, force_low_leverage, archetype=archetype
                    )
                    progress.advance(task)

                # Phases 3-5 (scaffold → strategy → proof fill) all run inside
                # phase3_prove; it advances the progress bar for 3/7 and 4/7 itself.
                audit.set_phase(3)
                if skip_to_agent9:
                    progress.update(
                        task,
                        description="Phase 3/7: Direct jump to Agent9  [--skip-to-agent9]...",
                    )
                else:
                    progress.update(task, description="Phase 3/7: Scaffold writing  [Agent2]...")
                success, attempts, _, phase3_audit = phase3_prove(
                    agent2, target_file, plan,
                    max_retries=max_retries,
                    archetype=archetype,
                    max_tool_turns=max_tool_turns,
                    progress_detail=progress_detail,
                    skip_to_agent9=skip_to_agent9,
                    _rich_progress=progress,
                    _rich_task=task,
                )
                total_attempts += attempts
                merged_phase3_audit["execution_history"].extend(
                    phase3_audit.get("execution_history", [])
                )
                merged_phase3_audit["attempt_failures"].extend(
                    phase3_audit.get("attempt_failures", [])
                )
                merged_phase3_audit["agent7_invocations"].extend(
                    phase3_audit.get("agent7_invocations", [])
                )
                merged_phase3_audit["agent7_step_execution_log"].extend(
                    phase3_audit.get("agent7_step_execution_log", [])
                )
                merged_phase3_audit["agent7_plan_revisions"].extend(
                    phase3_audit.get("agent7_plan_revisions", [])
                )
                merged_phase3_audit["agent7_blocked_actions"].extend(
                    phase3_audit.get("agent7_blocked_actions", [])
                )
                merged_phase3_audit["agent7_forced_trigger_count"] += int(
                    phase3_audit.get("agent7_forced_trigger_count", 0)
                )
                merged_phase3_audit["agent7_force_gate_entries"].extend(
                    phase3_audit.get("agent7_force_gate_entries", [])
                )
                merged_phase3_audit["agent7_force_gate_rejections"].extend(
                    phase3_audit.get("agent7_force_gate_rejections", [])
                )
                merged_phase3_audit["agent7_force_gate_reason_samples"].extend(
                    phase3_audit.get("agent7_force_gate_reason_samples", [])
                )
                merged_phase3_audit["estimated_token_consumption"] += int(
                    phase3_audit.get("estimated_token_consumption", 0)
                )
                merged_phase3_audit["retry_count"] += int(
                    phase3_audit.get("retry_count", 0)
                )
                if not success:
                    progress.reset(task)
                    progress.advance(task)  # re-enter at phase 2 (→1/7)

            # phase3_prove internally advances for phases 3/7 and 4/7;
            # this advance covers the proof-fill completion → 5/7.
            progress.advance(task)

            # Phase 6
            audit.set_phase(4)
            progress.update(task, description="Phase 6/7: Persisting docs  [Agent4]...")
            if DISABLE_PHASE4_PERSISTENCE:
                console.print(
                    "[yellow][Phase 4] Documentation persistence disabled by runtime policy.[/yellow]"
                )
                audit.log_event("phase4_skipped", reason="disabled_by_runtime_policy")
                new_tricks = 0
            else:
                try:
                    new_tricks = phase4_persist(
                        algorithm,
                        target_file,
                        plan,
                        baseline_tracked=baseline_tracked,
                        baseline_untracked=baseline_untracked,
                    )
                except Gate4Error as exc:
                    console.print(
                        f"[yellow]\\[Gate 4] Missing Used-in tags detected "
                        f"({len(exc.missing)} declaration(s)).  "
                        "Entering tag-fixup loop …"
                    )
                    phase3b_fix_tags(target_file, exc.missing)
                    # Retry Phase 4 now that all tags are present.
                    new_tricks = phase4_persist(
                        algorithm,
                        target_file,
                        plan,
                        baseline_tracked=baseline_tracked,
                        baseline_untracked=baseline_untracked,
                    )
            progress.advance(task)

            # Phase 7
            audit.set_phase(5)
            progress.update(task, description="Phase 7/7: Finalizing metrics...")
            phase5_finalize(
                algorithm,
                new_tricks=new_tricks,
                phase3_audit=merged_phase3_audit,
                total_attempts=total_attempts,
            )
            progress.advance(task)

            success = True
            all_modified = _get_modified_lean_files(
                baseline_tracked,
                baseline_untracked,
            )
            docs_in_diff = {f for f in _git_diff_files() if f.startswith("docs/")}
            files_modified = sorted(set(all_modified) | docs_in_diff)
    finally:
        if stop_token_hb is not None:
            stop_token_hb()
        if git_snapshot is not None:
            if success:
                try:
                    _restore_snapshot_on_success(git_snapshot)
                except Exception as exc:  # noqa: BLE001
                    success_restore_ok = False
                    success_restore_error = str(exc)
                    console.print(
                        "[yellow][Git] Run succeeded but failed to restore pre-run stash: "
                        f"{success_restore_error}"
                    )
            else:
                try:
                    _rollback_to_snapshot(git_snapshot)
                    rollback_applied = True
                    rollback_reason = "run_failed"
                except Exception as exc:  # noqa: BLE001
                    rollback_applied = False
                    rollback_reason = f"rollback_failed: {exc}"
                    console.print(
                        "[red][Git] Automatic rollback failed: "
                        f"{rollback_reason}"
                    )
        merged_phase3_audit["git_rollback_applied"] = rollback_applied
        merged_phase3_audit["git_rollback_reason"] = rollback_reason
        merged_phase3_audit["git_success_restore_ok"] = success_restore_ok
        merged_phase3_audit["git_success_restore_error"] = success_restore_error
        audit.add_phase3_data(
            merged_phase3_audit.get("execution_history", []),
            merged_phase3_audit.get("attempt_failures", []),
            extra=merged_phase3_audit,
        )
        extra_snapshot = [target_file] if not success else []
        audit.finish_run(success, files_modified, extra_files_to_snapshot=extra_snapshot)
        if files_modified:
            console.print(
                f"[dim][Audit] Files modified: {', '.join(files_modified)}[/dim]"
            )
        if not success and _lakefile_added_by_us and not rollback_applied:
            _remove_algorithm_from_lakefile(Path(target_file).stem)


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
    parser.add_argument("--max-tool-turns", type=int, default=None,
                        help=(
                            f"Max single-step tool turns per attempt "
                            f"(default: {MAX_AGENT3_TOOL_TURNS}, "
                            f"x1.5 for Archetype B). Override with this flag."
                        ))
    parser.add_argument("--force-low-leverage", action="store_true",
                        help="Override the ≥50%% leverage gate")
    parser.add_argument("--progress-detail",
                        choices=["compact", "normal", "debug"],
                        default="normal",
                        help=(
                            "Phase 3 log verbosity. "
                            "compact=milestones only; "
                            "normal=per-sorry lifecycle+summary (default); "
                            "debug=every tool call+full errors"
                        ))
    parser.add_argument("--interactive", action="store_true",
                        help="Prompt for algorithm card interactively")
    parser.add_argument("--skip-to-agent9", action="store_true",
                        help=(
                            "Skip Phase 1/2 (Agent2 planning) and Phase 3a (scaffold + Agent10). "
                            "Jump directly to Agent9 strategy planning. "
                            "Requires target file to already exist."
                        ))
    parser.add_argument("--agent-runtime", choices=["http", "codex", "hybrid"], default="hybrid",
                        help="Agent runtime backend policy (default: hybrid).")
    parser.add_argument("--codex-skip-only", dest="codex_skip_only", action="store_true", default=True,
                        help="Enable Codex runtime only for --skip-to-agent9 flow (default).")
    parser.add_argument("--no-codex-skip-only", dest="codex_skip_only", action="store_false",
                        help="Allow Codex runtime on non-skip flows too.")
    parser.add_argument("--lean-verify-backend", choices=["auto", "leanlsp", "lake"], default="auto",
                        help="Lean verify backend preference: auto=leanlsp first then lake fallback.")
    parser.add_argument("--codex-transport", choices=["sdk", "api"], default="sdk",
                        help="Codex backend transport: sdk (Responses API) or api (legacy call_llm).")
    parser.add_argument("--spec-file", type=str, default=None,
                        help=(
                            "Path to a structured JSON algorithm specification file "
                            "(e.g. book/FOML/StochasticMirrorDescent.json). "
                            "When provided, replaces --algorithm / --update-rule / "
                            "--proof-sketch / --archetype: all four fields are read "
                            "from the spec. Agent1B (orchestrator_spec) is used instead "
                            "of the standard Agent1, preserving all JSON content verbatim."
                        ))

    args = parser.parse_args()

    if args.interactive:
        fields = _interactive_input()
    elif args.spec_file:
        # spec-file mode: algorithm/update_rule/proof_sketch/archetype are read
        # from the JSON file by phase1_generate_prompt_from_spec(); supply
        # placeholder values here so run() can accept them (they are overwritten
        # inside run() when spec_file is set).
        import json as _json
        try:
            _spec = _json.loads(open(args.spec_file).read())
        except Exception as _e:
            parser.error(f"Cannot read --spec-file '{args.spec_file}': {_e}")
        fields = {
            "algorithm": _spec.get("algorithm", args.spec_file),
            "update_rule": _spec.get("sections", {}).get("2_algorithm", {}).get(
                "update_rule", {}).get("math", "see spec"),
            "proof_sketch": f"See structured spec: {args.spec_file}",
            "archetype": str(_spec.get("archetype", "B")).upper(),
        }
    else:
        if not all([args.algorithm, args.update_rule, args.proof_sketch, args.archetype]):
            parser.error(
                "Provide --algorithm, --update-rule, --proof-sketch, and "
                "--archetype, or use --interactive, or use --spec-file."
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
        max_tool_turns=args.max_tool_turns,
        force_low_leverage=args.force_low_leverage,
        progress_detail=args.progress_detail,
        skip_to_agent9=args.skip_to_agent9,
        spec_file=args.spec_file,
        agent_runtime=args.agent_runtime,
        codex_skip_only=args.codex_skip_only,
        lean_verify_backend=args.lean_verify_backend,
        codex_transport=args.codex_transport,
    )


if __name__ == "__main__":
    main()
