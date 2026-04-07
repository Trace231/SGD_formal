"""Agent3 Phase-3 orchestration extracted from main.py.

This module contains MAX_AGENT3_TOOL_TURNS, helper functions used by phase3_prove,
and the full phase3_prove implementation without behavior changes.
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
    AGENT6_AUTO_ROUTE_ENABLED,
    AGENT8_MIDCHECK_ENABLED,
    AGENT8_MIDCHECK_INTERVAL_TURNS,
    AGENT8_MIDCHECK_MIN_TURN,
    AGENT_CONFIGS,
    AUDIT_FLUSH_INTERVAL_SECONDS,
    ALGORITHM_REFERENCES,
    DOC_ANCHORS,
    LIB_GLUE_ANCHORS,
    MAX_PHASE3_RETRIES,
    PROJECT_ROOT,
    REFERENCE_FILES_WITH_DESCRIPTIONS,
    RETRY_LIMITS,
    ROUTING_PARAMS,
    UNKNOWN_IDENTIFIER_RENAME_MAP,
    _get_default_references,
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
from orchestrator.providers import call_llm
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
    _should_route_to_agent6_for_infra,
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
from orchestrator.phase3.escalation import _apply_agent2_route
from orchestrator.phase3.guards import _is_line_still_sorry, _scan_sorry_lines_in_file
from orchestrator.phase3.prompting import _build_preemptive_agent7_prompt
from orchestrator.phase3.state import Phase3Progress, Phase3Runtime, Phase3State

console = Console()

# Agent3 single-step interactive loop: maximum tool turns per attempt.
# Archetype B gets a 1.5× multiplier applied in phase3_prove.
MAX_AGENT3_TOOL_TURNS = 20


def phase3_prove(
    agent2: Agent,
    target_file: str,
    plan: str,
    *,
    max_retries: int = MAX_PHASE3_RETRIES,
    archetype: str = "A",
    max_tool_turns: int | None = None,
    progress_detail: str = "normal",
    skip_to_agent9: bool = False,
    _rich_progress=None,
    _rich_task=None,
) -> tuple[bool, int, str, dict]:
    """Phase 3: Agent2 ↔ Agent3 proving loop + Agent5 escalation.

    progress_detail controls log verbosity:
      compact — only attempt-level milestones
      normal  — per-sorry start/close/skip + round summaries (default)
      debug   — also prints every tool call and full error text

    _rich_progress / _rich_task: optional Rich Progress + task ID so that
    sub-phase advances (scaffold→3/7, agent9→4/7) can be reflected in the
    top-level spinner without the caller needing to know internal transitions.

    Returns (success, attempts, errors_or_empty, audit).
    """
    _progress = Phase3Progress(_rich_progress, _rich_task)

    def _prog_update(desc: str) -> None:
        _progress.update(desc)

    def _prog_advance() -> None:
        _progress.advance()
    # Compute per-attempt tool-turn budget.  Archetype B proofs are structurally
    # more complex and get a 1.5× multiplier.  Callers may override via max_tool_turns.
    if max_tool_turns is None:
        max_tool_turns = MAX_AGENT3_TOOL_TURNS
    if archetype.upper() == "B":
        max_tool_turns = int(max_tool_turns * 1.5)
    agent3 = Agent("sorry_closer", extra_files=[target_file])
    registry = ToolRegistry()
    registry.register_default_tools()
    _algo_name = Path(target_file).stem
    # Read-only registry for Agent2 lookup rounds (no write tools exposed).
    readonly_registry = ToolRegistry()
    readonly_registry.register_readonly_tools()
    # Agent2 escalation registry: read tools + edit access for mid-proof escalation.
    escalation_registry = ToolRegistry()
    escalation_registry.register_default_tools()
    # Agent6 (Glue Filler): full write access + goal/have tools for helper lemma proof.
    agent6 = Agent("glue_filler", extra_files=[target_file])
    agent6_registry = ToolRegistry()
    agent6_registry.register_default_tools()
    # Agent7 (Interface Auditor): read-only lookup + strict execution protocol output.
    agent7 = Agent("interface_auditor", extra_files=[target_file])
    agent7_registry = ToolRegistry()
    agent7_registry.register_readonly_tools()
    runtime = Phase3Runtime(
        agent2=agent2,
        agent3=agent3,
        agent6=agent6,
        agent7=agent7,
        registry=registry,
        readonly_registry=readonly_registry,
        escalation_registry=escalation_registry,
        agent6_registry=agent6_registry,
        agent7_registry=agent7_registry,
        progress=_progress,
    )
    _ = runtime  # runtime container for gradual state migration
    state = Phase3State()
    diag_log = state.diag_log

    # Pre-check: if the target file already has 0 sorry and builds clean,
    # skip the entire Agent3 loop.  This prevents destructive rewrites when
    # a previous run already completed the proof (e.g., after a Gate 4 crash).
    def _target_exists_overlay() -> bool:
        """True when target exists in workspace."""
        try:
            load_file(target_file)
            return True
        except FileNotFoundError:
            return False

    if _target_exists_overlay():
        pre_result = registry.call("run_lean_verify", target_file)
        if int(pre_result.get("exit_code", 1)) == 0 and int(pre_result.get("sorry_count", 0)) == 0:
            console.print(
                "[green][Phase 3] File already complete (build=OK, sorry=0). "
                "Skipping Agent3 — proceeding directly to Phase 4."
            )
            return True, 0, "", {
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
                "estimated_token_consumption": 0,
                "retry_count": 0,
            }

    _archetype_b_warning = (
        "\n\nARCHETYPE B WARNING: This is a novel proof structure with no Layer 1 "
        "meta-theorem to delegate to. No high-level abstractions are allowed in "
        "the theorem statement without verification in Lib/. Every symbol you "
        "reference MUST be traceable to a file in the shared context. "
        "Use read_file to verify lemma names before writing anything."
        if archetype.upper() == "B" else ""
    )
    _tgt = Path(target_file) if Path(target_file).is_absolute() else PROJECT_ROOT / target_file

    # Remove write_new_file from Agent3's registry: Phase 3a scaffold guarantees the
    # target file exists before Agent3 starts. Agent3 should only use edit_file_patch.
    registry._tools.pop("write_new_file", None)

    # --- Glue pollution guard (Fix B2) ---
    # Snapshot all existing Lib/Glue/*.lean files so we
    # can detect and revert any direct edits Agent3 makes to shared infrastructure.
    _glue_dir = PROJECT_ROOT / "Lib" / "Glue"
    _glue_snapshot: dict[Path, str] = {
        p: p.read_text(encoding="utf-8")
        for p in _glue_dir.glob("*.lean")
    }

    # --- Layer0 pollution guard ---
    # Snapshot all existing Lib/Layer0/*.lean files so Agent3 can never
    # permanently corrupt foundational library code (ConvexFOC, IndepExpect, etc.).
    _layer0_dir = PROJECT_ROOT / "Lib" / "Layer0"
    _layer0_snapshot: dict[Path, str] = {
        p: p.read_text(encoding="utf-8")
        for p in _layer0_dir.glob("*.lean")
    }

    initial_exists: bool = _target_exists_overlay()
    # Pre-compute imported API signatures once; reused for every Agent2 + Agent3 call.
    _imported_sigs = _extract_imported_algo_sigs(target_file)
    _imported_sigs_block = (
        f"\n\n{_imported_sigs}"
        if _imported_sigs else ""
    )
    guidance, _ = _call_agent2_with_tools(
        agent2,
        readonly_registry,
        "The verification target file is "
        + target_file
        + ". Provide initial proving guidance for Agent3.  Specify which sorry "
        "to tackle first and the recommended proof strategy (Mathlib lemma, "
        "glue pattern letter, etc.). "
        "When the plan requires both new glue AND a new algorithm file, your "
        "guidance MUST instruct Agent3 to complete BOTH in a single attempt, "
        "or verification will fail."
        + _archetype_b_warning
        + _imported_sigs_block,
    )
    console.print(Panel(
        guidance[:400] + "..." if len(guidance) > 400 else guidance,
        title="[cyan]Agent2 — Initial Guidance",
    ))

    last_errors = state.last_errors
    last_sorry_count = state.last_sorry_count
    attempts = state.attempts
    execution_history = state.execution_history
    attempt_failures = state.attempt_failures
    agent3_turns = state.agent3_turns
    _last_audit_flush_time = time.time()
    state.last_audit_flush_time = _last_audit_flush_time
    # Progress-panel dedup: suppress identical consecutive error text prints.
    _last_printed_err_sig = state.last_printed_err_sig
    agent7_invocations = state.agent7_invocations
    agent7_step_execution_log = state.agent7_step_execution_log
    agent7_plan_revisions = state.agent7_plan_revisions
    agent7_blocked_actions = state.agent7_blocked_actions
    agent7_forced_trigger_count = state.agent7_forced_trigger_count
    agent7_force_gate_entries = state.agent7_force_gate_entries
    agent7_force_gate_rejections = state.agent7_force_gate_rejections
    agent7_force_gate_reason_samples = state.agent7_force_gate_reason_samples
    token_char_budget = state.token_char_budget
    # Carry-over Agent7 plan from round-replan routing: set at end of attempt N,
    # consumed at the start of attempt N+1's per-sorry loop initialisation.
    _pending_agent7_plan = state.pending_agent7_plan

    # Circuit breaker: track consecutive repeat error signatures.
    # Key: normalized (file, line, message) hash of the primary error.
    # If the same signature appears in two consecutive attempts, force Surgeon Mode.
    _last_error_sig = state.last_error_sig
    _consecutive_repeat_count = state.consecutive_repeat_count

    # Loop guard: track which attempt numbers have already had assumption auto-patching
    # applied, to avoid re-patching the same theorem with the same hypothesis.
    _assumption_patch_tried = state.assumption_patch_tried

    # Loop guard: consecutive DEPENDENCY_COMPILE_ERROR streak (same dep error).
    _dep_error_streak = state.dep_error_streak
    _last_dep_error_sig = state.last_dep_error_sig

    # Failed approaches history: accumulates structured failure records across attempts.
    # Injected into Agent2 prompts so it avoids repeating strategies that already failed.
    _failed_approaches = state.failed_approaches

    # get_lean_goal cache: avoids re-running expensive LSP elaboration when the
    # file content and sorry line are identical across attempts.
    # Key: (target_file_relative, sorry_line, file_content_hash)
    _goal_cache = state.goal_cache

    # Snapshot target-file state before any Agent3 edits.
    # initial_hash: used for Phase-3 global success gate (file must change vs start of Phase 3).
    # attempt_start_hash: snapshotted at the start of each attempt for per-attempt no-op detection.
    initial_hash: str | None = _file_hash(target_file)
    file_changed: bool = False  # updated each attempt

    # Sorry-count checkpoint: tracks the best verified state seen during this
    # Phase 3 run.  Updated after every run_lean_verify that reduces sorry count.
    # Used in SIGNATURE_HALLUCINATION to restore partial progress instead of
    # nuking all work.  Only verified (compilable) states are checkpointed.
    _initial_sorry_for_ckpt = int(
        registry.call("run_lean_verify", target_file).get("sorry_count", 999)
        if _target_exists_overlay() else 999
    )
    best_checkpoint: dict = {
        "sorry_count": _initial_sorry_for_ckpt,
        "content": load_file(target_file) if _target_exists_overlay() else None,
    }

    # ------------------------------------------------------------------
    # ------------------------------------------------------------------
    # Phase 3/7 — Scaffold: Agent2 writes ALL theorem statements + sorry
    # placeholders, then Agent10 verifies/corrects the scaffold.
    # Only runs when the target file does not yet exist.
    # ------------------------------------------------------------------
    if skip_to_agent9:
        # Skip Phase 2 (already handled by caller) and Phase 3a (scaffold + Agent10).
        # Agent9 strategy planning runs in the unified Phase 4/7 block below.
        console.print("[dim][Phase 3/7] Skipped via --skip-to-agent9.")
        _prog_advance()  # Phase 3/7

    elif not _target_exists_overlay():
        console.rule("[bold cyan]Phase 3/7 — Scaffold  [Agent2 → Agent10]")
        _prog_update("Phase 3/7: Scaffold writing  [Agent2]...")
        _scaffold_registry = ToolRegistry()
        _scaffold_registry.register_scaffold_tools()
        _scaffold_ok = _call_agent2_scaffold(
            agent2,
            _scaffold_registry,
            target_file,
            guidance,  # Agent2's approved plan from Phase 2
            algo_name=_algo_name,
        )
        # Collect build errors so Agent10 can use them for Full-Correction mode.
        if not _scaffold_ok:
            _a2_verify = registry.call("run_lean_verify", target_file)
            _a2_build_errors: str = str(_a2_verify.get("errors", ""))
        else:
            _a2_build_errors = ""

        # Agent10 (Scaffold Verifier): systematic API-trace and typeclass
        # completeness check after Agent2's scaffold attempt.
        #   • scaffold_succeeded=True  → Semantic-Verify mode (Phase D + E)
        #   • scaffold_succeeded=False → Full-Correction mode (Phase A-E)
        _prog_update("Phase 3/7: Scaffold verification  [Agent10]...")
        from orchestrator.phase3a_agent10 import run_agent10_verify as _run_agent10_verify
        _a10_ok = _run_agent10_verify(
            target_file,
            guidance,
            _algo_name,
            scaffold_succeeded=_scaffold_ok,
            build_errors=_a2_build_errors,
        )

        if not _a10_ok:
            console.print(
                "[red bold][Phase 3/7] Scaffold FAILED — Agent2 and Agent10 "
                "could not produce a compiling scaffold.  Aborting."
            )
            return False, 0, "Phase 3a scaffold failed", {
                "attempts": 0,
                "execution_history": [],
                "attempt_failures": [],
                "agent3_turns": [],
                "agent7_invocations": [],
                "agent7_step_execution_log": [],
                "agent7_plan_revisions": [],
                "agent7_blocked_actions": [],
                "agent7_forced_trigger_count": 0,
                "agent7_force_gate_entries": [],
                "agent7_force_gate_rejections": [],
                "agent7_force_gate_reason_samples": [],
            }

        # Scaffold verified — advance progress bar to 3/7.
        _prog_advance()

        # Refresh checkpoint with verified scaffold content.
        _initial_sorry_for_ckpt = int(
            registry.call("run_lean_verify", target_file).get("sorry_count", 999)
        )
        best_checkpoint["sorry_count"] = _initial_sorry_for_ckpt
        best_checkpoint["content"] = load_file(target_file)
        initial_hash = _file_hash(target_file)
        initial_exists = True

        # Phase 3/7 scaffold verified — Phase 4/7 Agent9 runs in unified block below.
        pass

    else:
        # File already exists — skip Agent2 scaffold writing only.
        # Still run Agent10 (semantic verification) and Agent9 (strategy plan)
        # because the file may be hand-written or a failed prior run.
        console.print(
            "[dim][Phase 3/7] Scaffold writing skipped — file already exists "
            f"({target_file})"
        )
        _a2_build_errors = ""
        _prog_update("Phase 3/7: Scaffold verification  [Agent10]...")
        from orchestrator.phase3a_agent10 import run_agent10_verify as _run_agent10_verify
        _run_agent10_verify(
            target_file, guidance, _algo_name,
            scaffold_succeeded=True,
            build_errors="",
        )
        _prog_advance()

        # Phase 3/7 scaffold verified — Phase 4/7 Agent9 runs in unified block below.
        pass

    # ------------------------------------------------------------------
    # Phase 4/7 — Strategy Plan: Agent9 ALWAYS runs regardless of code path.
    # It converts the compiled scaffold into a structured JSON proof plan for
    # Agent8's Decision Hub.  Failure is non-fatal — Agent8 runs without plan.
    # ------------------------------------------------------------------
    console.rule("[bold cyan]Phase 4/7 — Strategy Plan  [Agent9]")
    _prog_update("Phase 4/7: Strategy planning  [Agent9]...")
    from orchestrator.phase3a_agent9 import run_agent9_plan as _run_agent9_plan
    # Capture current build state to give Agent9 full context (errors, sorry count).
    _pre_agent9_verify: dict = (
        registry.call("run_lean_verify", target_file)
        if _target_exists_overlay() else {}
    )
    _agent9_plan: dict = _run_agent9_plan(
        target_file,
        guidance,
        _algo_name,
        verify_state=_pre_agent9_verify if _pre_agent9_verify else None,
    )
    if _agent9_plan:
        # Agent9 plan ready — bypass Agent3 multi-retry loop and hand control
        # directly to Agent8 Decision Hub.  Set max_retries=0 so the Agent3
        # loop (range(1, max_retries+1)) is skipped entirely.
        max_retries = 0
        last_errors = str(_pre_agent9_verify.get("errors", ""))
        last_sorry_count = int(
            _pre_agent9_verify.get("sorry_count", _initial_sorry_for_ckpt)
        )
        # Promote Agent9's structured plan as the primary guidance for Agent8.
        guidance = json.dumps(_agent9_plan, indent=2, ensure_ascii=False)
        console.print(
            f"[cyan bold][Agent9] Plan ready — handing control to Agent8 "
            f"(sorry={last_sorry_count})"
        )
    else:
        console.print(
            "[yellow][Agent9] Strategy plan unavailable — "
            "Agent8 will operate without structured plan."
        )
    _prog_advance()  # Phase 4/7

    # ------------------------------------------------------------------
    # Phase 5/7 — Proof Fill: Agent3 / Agent8 close all sorry placeholders.
    # ------------------------------------------------------------------
    console.rule("[bold cyan]Phase 5/7 — Proof Fill  [Agent8]")
    _prog_update("Phase 5/7: Proof filling  [Agent8]...")

    for attempt in range(1, max_retries + 1):
        attempts = attempt
        attempt_start_hash: str | None = _file_hash(target_file)

        # ------------------------------------------------------------------
        # Context eviction: periodically clear Agent3 / Agent2 conversation
        # history to prevent cumulative context pollution from failed attempts.
        # Clearing self.messages causes the next agent.call() to re-prepend
        # _file_context automatically (see Agent.call first-turn logic).
        # ------------------------------------------------------------------
        if attempt > 1:
            _a3_evict_n = RETRY_LIMITS.get("AGENT3_CONTEXT_EVICT_EVERY_N", 3)
            if (attempt - 1) % _a3_evict_n == 0:
                agent3.messages.clear()
                _goal_cache.clear()  # avoid stale file-hash cache entries after eviction
                console.print(
                    f"  [ContextEvict] a{attempt} — Agent3 context cleared "
                    f"(every {_a3_evict_n} attempts)"
                )

            _a2_evict_n = RETRY_LIMITS.get("AGENT2_CONTEXT_EVICT_EVERY_N", 4)
            if (attempt - 1) % _a2_evict_n == 0 and agent2.messages:
                agent2.messages.clear()
                # Re-inject distilled context: math plan + best checkpoint + failed approaches
                # blacklist. This replaces the full accumulated conversation with a clean
                # summary so Agent2 retains mathematical knowledge without failure noise.
                _distilled_failures = "\n".join(
                    f"  a{f['attempt']} L{f.get('line', '?')}: {str(f.get('message', ''))[:80]}"
                    for f in attempt_failures[-8:]
                ) or "  (none recorded)"
                _distilled_ctx = (
                    f"[CONTEXT REFRESH — Attempt {attempt}]\n"
                    "Your conversation history has been cleared to remove context pollution "
                    "from failed attempts. Below is a distilled summary.\n\n"
                    f"## Current proof plan (preserve math structure, update tactics only)\n"
                    f"{guidance[:RETRY_LIMITS.get('AGENT2_DISTILLED_GUIDANCE_CHARS', 5000)]}\n\n"
                    f"## Best checkpoint (sorry={best_checkpoint['sorry_count']})\n"
                    f"```lean\n{(best_checkpoint['content'] or '')[:3000]}\n```\n\n"
                    f"## Failed approaches — do NOT repeat these\n{_distilled_failures}\n\n"
                    "Provide updated proof strategy for the next attempt."
                )
                guidance, _ = _call_agent2_with_tools(agent2, escalation_registry, _distilled_ctx)
                console.print(
                    f"  [ContextEvict] a{attempt} — Agent2 context refreshed "
                    f"(every {_a2_evict_n} attempts, distilled)"
                )

        # Keep previous verify context available before prequery (attempt>1 path).
        # These are re-initialized later for per-attempt tracking, but must exist
        # before first use in _prequery_sorry_goals.
        last_exit_code = 1
        last_verify_text = ""
        # Fix 3: when checkpoint has already improved, forbid overwriting the target file.
        _no_overwrite_rule = (
            f"- FORBIDDEN: write_new_file({target_file}) — the file already exists "
            f"with {best_checkpoint['sorry_count']} sorry(s), improved from the "
            f"initial {_initial_sorry_for_ckpt}. Overwriting would discard this "
            f"progress. Use ONLY edit_file_patch on {target_file}.\n"
            if (
                best_checkpoint["content"] is not None
                and best_checkpoint["sorry_count"] < _initial_sorry_for_ckpt
            )
            else ""
        )
        _attempt_awareness = (
            f"[Attempt {attempt} of {max_retries}. Current sorry_count: {last_sorry_count}.]\n\n"
            if attempt > 1
            else ""
        )

        # Parse sorry classifications from Agent2's guidance; build mandatory
        # instruction block for STRUCTURAL sorries so Agent3 escalates immediately.
        _sorry_classifications = _parse_sorry_classification(guidance)
        _structural_sorries = [c for c in _sorry_classifications if c["type"] == "STRUCTURAL"]
        # Split by subtype: STRUCTURAL_GLUE → Agent6, STRUCTURAL_INTERFACE → Agent7.
        _glue_sorries = [c for c in _structural_sorries if c.get("subtype") == "STRUCTURAL_GLUE"]
        _iface_sorries = [c for c in _structural_sorries if c.get("subtype") != "STRUCTURAL_GLUE"]
        _sorry_structural_block = ""
        _struct_blocks: list[str] = []
        if _iface_sorries:
            _iface_info = "\n".join(
                f"  - Line {c['line']}: {c['reason']}\n"
                f"    diagnosis: \"{c.get('diagnosis', '')}\"\n"
                f"    dependency_symbols: {c.get('dependency_symbols', [])}"
                for c in _iface_sorries
            )
            _struct_blocks.append(
                "## MANDATORY PRE-AUDIT (interface/signature issue — from Agent2)\n"
                "The following sorry(s) have an API/interface problem:\n"
                + _iface_info + "\n"
                "REQUIRED first action: call request_agent7_interface_audit with the "
                "diagnosis above.\n"
                "Do NOT write any tactic or edit_file_patch before completing this step.\n"
            )
        if _glue_sorries:
            _glue_info = "\n".join(
                f"  - Line {c['line']}: {c['reason']}\n"
                f"    diagnosis: \"{c.get('diagnosis', '')}\"\n"
                f"    dependency_symbols: {c.get('dependency_symbols', [])}"
                for c in _glue_sorries
            )
            _struct_blocks.append(
                "## MANDATORY GLUE ESCALATION (missing bridge lemma — from Agent2)\n"
                "The following sorry(s) require a new glue/bridge lemma:\n"
                + _glue_info + "\n"
                "REQUIRED first action: call request_agent6_glue with stuck_at_line and "
                "the diagnosis above.\n"
                "Do NOT attempt local tactics — this sorry cannot be closed without a "
                "new lemma. Agent7 will pre-screen to confirm before Agent6 runs.\n"
            )
        if _struct_blocks:
            _sorry_structural_block = "\n".join(_struct_blocks) + "\n\n"
        if _structural_sorries:
            console.print(
                f"  [SorryClassification] attempt {attempt} — "
                + (f"{len(_glue_sorries)} GLUE: "
                   + ", ".join(f"line {c['line']}" for c in _glue_sorries)
                   if _glue_sorries else "")
                + (" | " if _glue_sorries and _iface_sorries else "")
                + (f"{len(_iface_sorries)} INTERFACE: "
                   + ", ".join(f"line {c['line']}" for c in _iface_sorries)
                   if _iface_sorries else "")
            )

        # -----------------------------------------------------------------------
        # Per-sorry iteration: build static attempt-level prompt once, then loop
        # over each sorry line and give Agent3 a focused target per iteration.
        # -----------------------------------------------------------------------

        # Build static (per-attempt) prover prompt parts.
        _base_prover_prompt = (
            _attempt_awareness
            + _sorry_structural_block
            + "Use tools to close sorry placeholders.\n"
            "Return ONLY valid JSON with exactly three keys: thought, tool, arguments.\n"
            "Output ONE action per response. After each action you will receive its "
            "result before deciding the next action.\n"
            'Example: {"thought": "...", "tool": "read_file", "arguments": {"path": "..."}}\n'
            "To signal no further actions are needed: "
            '{"thought": "...", "tool": "done", "arguments": {}}\n'
            "write_new_file is NOT available — the scaffold file already exists. "
            "Use ONLY edit_file_patch to modify the target file.\n"
            "Allowed tools: read_file, read_file_readonly, search_in_file, search_in_file_readonly, "
            "search_codebase, edit_file_patch, get_lean_goal, "
            "check_lean_have, run_lean_verify, request_agent6_glue, request_agent2_help, "
            "request_agent7_interface_audit.\n"
            "SITUATIONAL BEHAVIOR:\n"
            "- If guidance contains PATCH blocks (<<<SEARCH>>>/<<<REPLACE>>>): "
            "execute them exactly — copy old_str and new_str verbatim.\n"
            "- When you receive a tool result: analyze it and decide your next action.\n"
            "- After any edit call run_lean_verify to confirm.\n\n"
            "FILE EDITING RULES (non-negotiable):\n"
            f"- You may edit: {target_file}\n"
            "- Lib/Glue/Probability.lean, Algebra.lean, Measurable.lean, Calculus.lean: READ-ONLY.\n"
            "- All Lib/Layer0/*.lean files (ConvexFOC.lean, IndepExpect.lean, GradientFTC.lean) "
            "are READ-ONLY. Use read_file_readonly to inspect them, never edit_file_patch.\n"
            "- NEW helper lemmas (Level 2 gaps) go DIRECTLY in the target file, before the main theorem.\n"
            "  A helper lemma may have `sorry` body; that is intentional and not penalized.\n"
            "- BEFORE adding any new 'import X' statement to any file, call "
            "read_file_readonly(\"Main.lean\") or read_file_readonly(\"lakefile.lean\") "
            "to verify that X does not already import the file you are editing "
            "(which would create a circular dependency).\n"
            + _no_overwrite_rule
            + "\n"
            f"Target file: {target_file}\n"
            + (_imported_sigs_block.lstrip("\n") + "\n" if _imported_sigs_block else "")
            + f"Guidance:\n{guidance}"
        )

        # Per-attempt state (persists across all sorry iterations).
        exec_results: list[ExecutionResult] = []
        edited_this_attempt = False
        patch_mismatch_in_attempt = False
        last_exit_code = 1
        last_sorry_in_attempt = 0
        last_verify_text = ""
        last_verify_result: dict | None = None
        _lookup_done_since_last_edit: bool = False
        _patch_without_lookup_count: int = 0
        _tools_used_this_attempt: set[str] = set()
        _inner_break_reason = ""

        # Scan sorry lines for per-sorry iteration.
        # If no sorries exist (errors only, sorry=0), use a single None sentinel
        # so Agent3 can still fix compilation errors in one iteration.
        _sorry_lines_attempt = _scan_sorry_lines_in_file(target_file)
        _sorry_iter: list[int | None] = _sorry_lines_attempt if _sorry_lines_attempt else [None]
        _sorry_status: dict[int | None, str] = {ln: "pending" for ln in _sorry_iter}
        _total_turns_this_attempt = 0
        _break_attempt = False
        _per_sorry_turns_budget = RETRY_LIMITS.get("PER_SORRY_TURNS", 20)
        # Attempt-level escalation accumulators (for summary panel).
        _attempt_esc_a2: int = 0
        _attempt_esc_a6: int = 0
        _attempt_esc_a7: int = 0
        # Reset per-attempt error dedup.
        _last_printed_err_sig = None
        # Current error signature (MD5 of primary error); updated each verify round.
        _err_sig: str = ""

        # -------------------------------------------------------------------
        # Baseline error snapshot: capture errors BEFORE Agent3 touches the file.
        # Used by Agent8 MidCheck to distinguish pre-existing API/structural errors
        # from errors Agent3 introduces during its attempts.
        # -------------------------------------------------------------------
        try:
            _baseline_verify = registry.call("run_lean_verify", target_file)
            _baseline_errors_text: str = "\n".join(
                _baseline_verify.get("errors", [])
            ) or _baseline_verify.get("errors", "")
            if isinstance(_baseline_errors_text, list):
                _baseline_errors_text = "\n".join(_baseline_errors_text)
        except Exception:
            _baseline_errors_text = ""

        # -------------------------------------------------------------------
        # Per-sorry loop: each iteration focuses Agent3 on one sorry line.
        # -------------------------------------------------------------------
        for _active_sorry_line in _sorry_iter:
            if _sorry_status[_active_sorry_line] != "pending":
                continue
            if _total_turns_this_attempt >= max_tool_turns or _break_attempt:
                _sorry_status[_active_sorry_line] = "skipped"
                continue

            # Build per-sorry active target header.
            _active_target_header = ""
            if _active_sorry_line is not None:
                _other_pending = [
                    ln for ln in _sorry_iter
                    if ln is not None and ln != _active_sorry_line
                    and _sorry_status.get(ln) == "pending"
                ]
                _active_target_header = (
                    f"## Active Sorry Target: Line {_active_sorry_line}\n"
                    "Focus exclusively on closing this sorry. "
                    "Do NOT modify other sorry lines in this iteration.\n"
                    + (
                        "Other pending sorries (leave untouched this iteration): "
                        + ", ".join(f"line {ln}" for ln in _other_pending)
                        + "\n"
                        if _other_pending else ""
                    )
                    + "\n"
                )

            prover_prompt = _active_target_header + _base_prover_prompt

            # Per-sorry goal injection: full detail for active, lightweight for others.
            _goal_block = _prequery_sorry_goals(
                registry,
                target_file,
                guidance,
                _goal_cache,
                errors_text=last_verify_text,
                target_line=_active_sorry_line,
            )
            if _goal_block:
                if progress_detail != "compact":
                    console.print(
                        f"  [GoalPreQuery] attempt {attempt} "
                        + (f"sorry line {_active_sorry_line}" if _active_sorry_line else "error-fix mode")
                        + " — injected goal state"
                    )
                prover_prompt = prover_prompt + "\n\n" + _goal_block

            raw_reply = agent3.call(prover_prompt)
            token_char_budget += len(prover_prompt) + len(raw_reply)

            # Per-sorry escalation state (reset for each sorry).
            _escalation_count = 0
            _agent6_escalation_count = 0
            _last_local_error_sig: str | None = None
            _agent6_first_goal_sig: str | None = None
            _agent6_first_progress_ok: bool = False
            _agent6_second_min_progress = RETRY_LIMITS.get("AGENT6_SECOND_ESCALATION_MIN_PROGRESS", 1)
            _agent6_second_require_same_goal = bool(
                RETRY_LIMITS.get("AGENT6_SECOND_ESCALATION_REQUIRE_SAME_GOAL", 1)
            )
            _agent7_invocations_this_attempt = 0
            _agent7_max_invocations = RETRY_LIMITS.get("MAX_AGENT7_INVOCATIONS_PER_ATTEMPT", 4)
            _agent7_no_progress_threshold = RETRY_LIMITS.get("AGENT7_STEP_NO_PROGRESS_THRESHOLD", 2)
            # Agent3 autonomy: Agent6 no longer requires Agent7 pre-approval.
            _agent7_approved_agent6 = True
            # Agent2 router budget — reset each attempt.
            _routing_budget: dict[str, int] = {"self_revisions": 0, "preemptive_agent7": 0}
            _route_repeat_tracker: dict[str, int] = {}
            # Carry over any Agent7 plan pre-computed during the previous attempt's
            # round-replan routing (stored in _pending_agent7_plan); clear the carrier.
            _active_agent7_plan: dict | None = _pending_agent7_plan
            _pending_agent7_plan = None
            _agent7_current_step_idx = 0
            _agent7_pending_verify = False
            _direct_applied_patches: list[dict] = []
            _agent7_last_step_id: str | None = None
            _agent7_prev_sorry = last_sorry_count
            _agent7_no_progress_count = 0
            _agent7_force_stale_threshold = RETRY_LIMITS.get("AGENT7_FORCE_STALE_LINE_THRESHOLD", 3)
            _agent7_force_no_progress_turns_threshold = RETRY_LIMITS.get("AGENT7_FORCE_NO_PROGRESS_TURNS", 3)
            _agent7_force_after_soft_warn = RETRY_LIMITS.get("AGENT7_FORCE_AFTER_SOFT_WARN", 1)
            _agent7_soft_warned = False
            _agent7_force_gate_active = False
            _agent7_force_warn_turn: int | None = None
            _agent7_no_progress_turns = 0
            _agent7_last_verified_sorry: int | None = None
            _stale_err_line: int | None = None
            _stale_err_count: int = 0
            _def_zone_err_count: int = 0
            _def_zone_force_threshold = RETRY_LIMITS.get("DEFINITION_ZONE_FORCE_AGENT7_AFTER_N", 2)
            # Conservative routing counters.
            # Tracks consecutive turns where the same interface-like error signature repeated.
            _conservative_iface_sig: str = ""
            _conservative_iface_repeat_count: int = 0
            _conservative_iface_repeat_threshold = RETRY_LIMITS.get(
                "CONSERVATIVE_INTERFACE_ERROR_REPEAT_THRESHOLD", 2
            )
            _conservative_blocked_escalate = bool(
                RETRY_LIMITS.get("CONSERVATIVE_BLOCKED_SORRY_INTERFACE_ESCALATE", 1)
            )
            # Tracks whether the active sorry line was closed during this iteration.
            _active_sorry_closed = False

            # Compute per-sorry remaining budget.
            _per_sorry_remaining = max(
                8, min(_per_sorry_turns_budget, max_tool_turns - _total_turns_this_attempt)
            )

            # Per-sorry start log.
            if progress_detail != "compact":
                _pending_total = sum(1 for s in _sorry_status.values() if s == "pending")
                if _active_sorry_line is not None:
                    console.print(
                        f"  [PerSorryStart] a{attempt} line={_active_sorry_line} "
                        f"budget={_per_sorry_remaining}t "
                        f"pending={_pending_total}/{len(_sorry_iter)}"
                    )
                else:
                    console.print(
                        f"  [PerSorryStart] a{attempt} error-fix mode "
                        f"budget={_per_sorry_remaining}t"
                    )

            # Per-sorry turn counter (used in PerSorrySkip summary).
            _turns_this_sorry: int = 0
            # JSON retry counter — retry up to 2 times before breaking attempt
            _json_retry_count: int = 0
            _MAX_JSON_RETRIES: int = 2
            # Mid-check gate counter: tracks turns since last Agent8 soft-gate evaluation.
            _midcheck_turns_since_gate: int = 0

            # -------------------------------------------------------------------
            # Single-step interactive tool loop (per sorry)
            # Each iteration: parse one action, execute it, return result.
            # -------------------------------------------------------------------
            for tool_turn in range(_per_sorry_remaining):
                _total_turns_this_attempt += 1
                _turns_this_sorry += 1
                _midcheck_turns_since_gate += 1

                # ---------------------------------------------------------------
                # Agent8 mid-check soft gate: every AGENT8_MIDCHECK_INTERVAL_TURNS
                # Agent3 tool turns, ask Agent8 for a single routing decision.
                # If Agent8 says agent3_tactical → continue; otherwise dispatch
                # the chosen agent immediately and then let Agent3 continue.
                # ---------------------------------------------------------------
                if (
                    AGENT8_MIDCHECK_ENABLED
                    and _total_turns_this_attempt >= AGENT8_MIDCHECK_MIN_TURN
                    and _midcheck_turns_since_gate >= AGENT8_MIDCHECK_INTERVAL_TURNS
                ):
                    _midcheck_turns_since_gate = 0  # reset counter regardless of outcome
                    _midcheck_errors = last_verify_text if last_verify_text else last_errors
                    if _midcheck_errors.strip():
                        from orchestrator.phase3_agent8 import run_agent8_midcheck
                        _mc_decision = run_agent8_midcheck(
                            target_file,
                            guidance,
                            _midcheck_errors,
                            agent2=agent2,
                            agent9_plan=locals().get("_agent9_plan"),
                            decision_history=None,  # fresh per mid-check; no shared history
                            turns_elapsed=_total_turns_this_attempt,
                            baseline_errors=_baseline_errors_text,
                        )
                        _mc_action = _mc_decision.get("action", "agent3_tactical")
                        _mc_prompt = _mc_decision.get("targeted_prompt", "")
                        console.print(
                            f"  [Agent8 MidCheck] a{attempt} turn={_total_turns_this_attempt} "
                            f"→ {_mc_action}"
                        )
                        if _mc_action != "agent3_tactical":
                            # Execute the escalation action, then resume Agent3.
                            from orchestrator.phase3_agent8 import (
                                _agent8_run_agent7,
                                _agent8_run_agent7_then_agent6,
                            )
                            from orchestrator.tools import run_lean_verify as _rlv_mc
                            try:
                                if _mc_action == "agent7_signature":
                                    _a7p = _mc_decision.get("agent7_targeted_prompt", _mc_prompt)
                                    _a7plan, _ = _agent8_run_agent7(
                                        target_file, _midcheck_errors, _a7p
                                    )
                                    if _a7plan:
                                        from orchestrator.agents import ToolRegistry as _TR
                                        _exec_reg = _TR()
                                        _exec_reg.register_default_tools()
                                        for _step in _a7plan.get("ordered_steps", []):
                                            if _step.get("direct_apply") and _step.get("tool") == "edit_file_patch":
                                                _req = _step.get("required_args", {})
                                                if _req.get("old_str") and _req.get("new_str"):
                                                    try:
                                                        _exec_reg.call(
                                                            "edit_file_patch",
                                                            path=_req.get("path", target_file),
                                                            old_str=_req["old_str"],
                                                            new_str=_req["new_str"],
                                                        )
                                                    except Exception:
                                                        pass
                                    _attempt_esc_a7 += 1

                                elif _mc_action == "agent7_then_agent6":
                                    _a7p = _mc_decision.get("agent7_targeted_prompt", _mc_prompt)
                                    _a6p = _mc_decision.get("agent6_targeted_prompt", _mc_prompt)
                                    _agent8_run_agent7_then_agent6(
                                        target_file, _midcheck_errors, _a7p, _a6p
                                    )
                                    _attempt_esc_a7 += 1
                                    _attempt_esc_a6 += 1

                                elif _mc_action == "agent9_replan":
                                    from orchestrator.phase3a_agent9 import run_agent9_replan as _run_a9_midcheck
                                    _new_plan = _run_a9_midcheck(
                                        target_file,
                                        _midcheck_errors,
                                        _agent9_plan or {},
                                        algo_name,
                                        guidance,
                                    )
                                    if _new_plan:
                                        _agent9_plan = _new_plan
                                        guidance = json.dumps(_new_plan, indent=2, ensure_ascii=False)
                                    _attempt_esc_a2 += 1

                                elif _mc_action == "human_missing_assumption":
                                    console.print(
                                        "[red bold][Agent8 MidCheck] human_missing_assumption "
                                        "— escalating to human gate."
                                    )
                                    # Treat same as turn-limit exhaustion; break out.
                                    _inner_break_reason = "midcheck_human_gate"
                                    _break_attempt = True
                                    break

                            except Exception as _mc_exc:
                                console.print(
                                    f"  [Agent8 MidCheck] Dispatch error: {_mc_exc} "
                                    "— continuing Agent3."
                                )

                            # After escalation: re-verify and refresh Agent3 with new state.
                            if not _break_attempt:
                                _mc_verify = _rlv_mc(target_file)
                                last_exit_code = int(_mc_verify.get("exit_code", 1))
                                last_sorry_in_attempt = int(_mc_verify.get("sorry_count", 0))
                                _mc_errors_raw = _mc_verify.get("errors", [])
                                last_verify_text = (
                                    "\n".join(_mc_errors_raw)
                                    if isinstance(_mc_errors_raw, list)
                                    else str(_mc_errors_raw)
                                )
                                last_errors = last_verify_text
                                # Re-prime Agent3 with the updated state so it doesn't
                                # act on stale context.
                                _mc_feedback = (
                                    f"[Agent8 mid-check: dispatched {_mc_action}]\n"
                                    f"Current build state: exit={last_exit_code}, "
                                    f"sorry={last_sorry_in_attempt}\n"
                                    f"Errors:\n```\n{last_verify_text[:1500]}\n```\n"
                                    "Continue from this updated state."
                                )
                                raw_reply = agent3.call(_mc_feedback)
                                continue  # skip remainder of this turn; start fresh next turn
                try:
                    payload = json.loads(raw_reply)
                except json.JSONDecodeError as exc:
                    err_msg = (
                        f"Invalid JSON (line {exc.lineno}, col {exc.colno}): {exc.msg}. "
                        "Return valid JSON with keys: thought, tool, arguments."
                    )
                    diag_log.append(f"attempt={attempt} turn={tool_turn} {err_msg}")
                    if _json_retry_count < _MAX_JSON_RETRIES:
                        _json_retry_count += 1
                        raw_reply = agent3.call(
                            f"{err_msg}\n\n"
                            "Your response must be a single JSON object — no markdown fences, "
                            "no extra text. Example format:\n"
                            '{"thought": "...", "tool": "edit_file_patch", "arguments": {...}}'
                        )
                        _turns_this_sorry += 1
                        _total_turns_this_attempt += 1
                        continue
                    exec_results.append(ExecutionResult(
                        status_code="ERROR", message=err_msg, attempt=attempt,
                    ))
                    last_errors = err_msg
                    _inner_break_reason = "json_error"
                    _break_attempt = True
                    break

                _json_retry_count = 0  # reset on successful parse

                if not isinstance(payload, dict):
                    err_msg = "Agent3 JSON must be an object with keys: thought, tool, arguments."
                    diag_log.append(f"attempt={attempt} turn={tool_turn} {err_msg}")
                    if _json_retry_count < _MAX_JSON_RETRIES:
                        _json_retry_count += 1
                        raw_reply = agent3.call(
                            f"{err_msg}\n\n"
                            "Return ONLY a JSON object: "
                            '{"thought": "...", "tool": "...", "arguments": {...}}'
                        )
                        _turns_this_sorry += 1
                        _total_turns_this_attempt += 1
                        continue
                    exec_results.append(ExecutionResult(
                        status_code="ERROR", message=err_msg, attempt=attempt,
                    ))
                    last_errors = err_msg
                    _inner_break_reason = "json_error"
                    _break_attempt = True
                    break

                tool_name = str(payload.get("tool", ""))
                arguments = payload.get("arguments", {})
                if not isinstance(arguments, dict):
                    arguments = {}
                if tool_name:
                    _tools_used_this_attempt.add(tool_name)

                if progress_detail == "debug":
                    _line_tag = f"line={_active_sorry_line}" if _active_sorry_line else "err-fix"
                    console.print(
                        f"  [A3] a{attempt} t{tool_turn + 1}/{_per_sorry_remaining} "
                        f"{_line_tag} tool={tool_name}"
                    )

                _thought = str(payload.get("thought", "")).strip()
                _args_safe = {k: (v[:200] if isinstance(v, str) else v) for k, v in (arguments or {}).items() if k != "path"}
                if "path" in (arguments or {}):
                    _args_safe["path"] = str(arguments.get("path", ""))[:100]
                agent3_turns.append({
                    "attempt": attempt,
                    "turn": tool_turn + 1,
                    "thought": _thought[:8000] if _thought else "",
                    "tool": tool_name,
                    "arguments": _args_safe,
                    "ts": datetime.now(timezone.utc).isoformat(timespec="seconds"),
                })

                # ---------------------------------------------------------------
                # Forced Agent7 gate: when stuck too long, restrict next actions
                # ---------------------------------------------------------------
                if (
                    _agent7_force_gate_active
                    and _active_agent7_plan is None
                    and tool_name not in ("request_agent7_interface_audit", "run_lean_verify", "request_agent2_help")
                ):
                    agent7_force_gate_rejections.append({
                        "attempt": attempt,
                        "turn": tool_turn + 1,
                        "tool": tool_name,
                    })
                    exec_results.append(ExecutionResult(
                        status_code="BLOCKED",
                        message=f"AGENT7_FORCE_GATE_REJECT tool={tool_name}",
                        attempt=attempt,
                    ))
                    raw_reply = agent3.call(
                        "## FORCE_GATE_ACTIVE\n"
                        "You are stuck on repeated structural/type mismatch errors.\n"
                        "Allowed next tools: request_agent7_interface_audit, run_lean_verify, request_agent2_help.\n"
                        "Call request_agent7_interface_audit now."
                    )
                    token_char_budget += len(raw_reply)
                    continue

                # ---------------------------------------------------------------
                # Agent3 → Agent7 interface-audit escalation
                # ---------------------------------------------------------------
                if tool_name == "request_agent7_interface_audit":
                    if _agent7_invocations_this_attempt >= _agent7_max_invocations:
                        raw_reply = agent3.call(
                            "## request_agent7_interface_audit rejected — limit reached\n"
                            f"At most {_agent7_max_invocations} Agent7 invocations per attempt."
                        )
                        token_char_budget += len(raw_reply)
                        continue
                    _agent7_invocations_this_attempt += 1
                    _attempt_esc_a7 += 1
                    stuck_at_line = arguments.get("stuck_at_line") or arguments.get("sorry_line") or "unknown"
                    error_message = str(arguments.get("error_message", ""))[:1200]
                    diagnosis = str(arguments.get("diagnosis", ""))[:1600]
                    attempts_tried = int(arguments.get("attempts_tried", tool_turn + 1))
                    primary_error = arguments.get("primary_error")
                    dependency_symbols = arguments.get("dependency_symbols")
                    recent_failures = arguments.get("recent_failures")
                    _line_int = int(stuck_at_line) if str(stuck_at_line).isdigit() else _extract_first_error_line(last_verify_text) or 1
                    current_snippet = _build_escalation_file_context(target_file, _line_int)
                    dep_sigs = _prequery_dependency_signatures(last_verify_text, target_file)
                    if isinstance(primary_error, (dict, list)):
                        _primary_err_text = json.dumps(primary_error, ensure_ascii=False)[:1200]
                    else:
                        _primary_err_text = str(primary_error or "")[:1200]
                    if isinstance(dependency_symbols, list):
                        _dep_syms_text = ", ".join(str(s) for s in dependency_symbols[:20])
                    else:
                        _dep_syms_text = str(dependency_symbols or "")[:600]
                    if isinstance(recent_failures, list):
                        _recent_failures_text = json.dumps(recent_failures[-8:], ensure_ascii=False)[:3000]
                    else:
                        _recent_failures_text = str(recent_failures or "")[:2000]
                    if not _recent_failures_text:
                        _recent_failures_text = json.dumps(
                            [a for a in attempt_failures if a.get("attempt") == attempt][-8:],
                            ensure_ascii=False,
                        )[:3000]
                    agent7_prompt = (
                        "Produce a strict interface-audit protocol JSON for Agent3.\n"
                        f"Target file: {target_file}\n"
                        f"Stuck at line: {_line_int}\n"
                        f"Attempts tried: {attempts_tried}\n\n"
                        f"Primary error:\n```\n{_primary_err_text or error_message}\n```\n\n"
                        f"Diagnosis:\n{diagnosis}\n\n"
                        f"Dependency symbols hint:\n{_dep_syms_text}\n\n"
                        f"Recent failures:\n```\n{_recent_failures_text}\n```\n\n"
                        f"Current file (full when ≤500 lines):\n```lean\n{current_snippet[:20000]}\n```\n\n"
                        f"Dependency signatures:\n```lean\n{dep_sigs[:4000]}\n```\n\n"
                        "Return strict JSON only as specified in your system prompt."
                    )
                    plan_obj, raw_plan = _call_agent7_with_tools(
                        agent7,
                        agent7_registry,
                        agent7_prompt,
                    )
                    agent7_invocations.append({
                        "attempt": attempt,
                        "turn": tool_turn + 1,
                        "stuck_at_line": _line_int,
                        "error_message": error_message[:300],
                        "diagnosis": diagnosis[:300],
                        "success": plan_obj is not None,
                    })
                    if not plan_obj:
                        raw_reply = agent3.call(
                            "## Agent7 returned invalid protocol JSON\n"
                            "Continue with local fixes or escalate to Agent2/Agent6."
                        )
                        token_char_budget += len(raw_reply)
                        continue
                    _active_agent7_plan = plan_obj
                    _agent7_current_step_idx = 0
                    _agent7_pending_verify = False
                    _agent7_last_step_id = None
                    _agent7_prev_sorry = last_sorry_in_attempt
                    _agent7_no_progress_count = 0
                    # Agent7 gatekeeper: allow Agent6 only when Agent7 says infra is missing.
                    _ft = plan_obj.get("fallback_trigger") or {}
                    _agent7_approved_agent6 = (
                        str(_ft.get("route_to", "")).strip().lower() == "agent6"
                        or any(
                            str(s.get("tool", "")).strip() == "request_agent6_glue"
                            for s in (plan_obj.get("ordered_steps") or [])
                            if isinstance(s, dict)
                        )
                    )
                    if _agent7_force_gate_active:
                        _agent7_force_gate_active = False
                        exec_results.append(ExecutionResult(
                            status_code="SUCCESS",
                            message="AGENT7_FORCE_GATE_OFF",
                            attempt=attempt,
                        ))
                    agent7_plan_revisions.append({
                        "attempt": attempt,
                        "turn": tool_turn + 1,
                        "plan_size": len(plan_obj.get("ordered_steps", [])),
                        "root_cause": str(plan_obj.get("root_cause", ""))[:400],
                        "raw_excerpt": raw_plan[:800],
                    })
                    _steps = plan_obj.get("ordered_steps", [])
                    _first_step_id = str(_steps[0].get("step_id", "S1")) if isinstance(_steps, list) and _steps else "S1"
                    exec_results.append(ExecutionResult(
                        status_code="SUCCESS",
                        message=f"AGENT7_PLAN_APPLIED step={_first_step_id}",
                        attempt=attempt,
                    ))
                    raw_reply = agent3.call(
                        "## Agent7 protocol applied\n"
                        f"Root cause: {plan_obj.get('root_cause', '')}\n"
                        f"Next required step: {_first_step_id}\n"
                        "Execute exactly one step and include `executed_step_id` in your arguments.\n"
                        "After that step, call run_lean_verify before any other edit.\n"
                    )
                    token_char_budget += len(raw_reply)
                    continue

                # ---------------------------------------------------------------
                # Agent7 execution gate
                # ---------------------------------------------------------------
                if _active_agent7_plan is not None:
                    _steps = _active_agent7_plan.get("ordered_steps", [])
                    _has_steps = isinstance(_steps, list) and len(_steps) > 0
                    if _has_steps:
                        _step_idx = min(_agent7_current_step_idx, len(_steps) - 1)
                        _cur_step = _steps[_step_idx]
                        _cur_step_id = str(_cur_step.get("step_id", f"S{_step_idx + 1}"))
                        _cur_tool = str(_cur_step.get("tool", "")).strip()
                    else:
                        _cur_step = {}
                        _cur_step_id = "S1"
                        _cur_tool = ""

                    if _agent7_pending_verify and tool_name != "run_lean_verify":
                        agent7_blocked_actions.append({
                            "attempt": attempt,
                            "turn": tool_turn + 1,
                            "reason": "verify_required",
                            "requested_tool": tool_name,
                            "expected_step_id": _agent7_last_step_id,
                        })
                        raw_reply = agent3.call(
                            "## AGENT7_STEP_REJECTED\n"
                            f"You must call run_lean_verify now to validate step {_agent7_last_step_id} "
                            "before any further action."
                        )
                        token_char_budget += len(raw_reply)
                        continue

                    if not _agent7_pending_verify and _has_steps:
                        # -----------------------------------------------------------
                        # DirectApply: orchestrator executes mechanical edit_file_patch
                        # steps directly, bypassing Agent3, when direct_apply=true.
                        # -----------------------------------------------------------
                        if (
                            _cur_step.get("direct_apply")
                            and _cur_tool == "edit_file_patch"
                        ):
                            _req = _cur_step.get("required_args", {})
                            _da_old = _req.get("old_str", "")
                            _da_new = _req.get("new_str", "")
                            _da_path = _req.get("path", target_file)
                            if _da_old and _da_new:
                                try:
                                    registry.call(
                                        "edit_file_patch",
                                        path=_da_path,
                                        old_str=_da_old,
                                        new_str=_da_new,
                                    )
                                    _direct_applied_patches.append(
                                        {"path": _da_path, "new_str": _da_new, "step_id": _cur_step_id}
                                    )
                                    _agent7_current_step_idx = min(
                                        _agent7_current_step_idx + 1, len(_steps) - 1
                                    )
                                    console.print(
                                        f"  [Agent7 DirectApply] step {_cur_step_id} applied by orchestrator"
                                    )
                                    _da_verify = registry.call("run_lean_verify", target_file)
                                    last_exit_code = int(_da_verify.get("exit_code", 1))
                                    last_sorry_in_attempt = int(_da_verify.get("sorry_count", 0))
                                    last_verify_text = str(_da_verify.get("errors", ""))
                                    _next_step_hint = ""
                                    if _agent7_current_step_idx < len(_steps):
                                        _ns = _steps[_agent7_current_step_idx]
                                        _next_step_hint = (
                                            f"\nNext step: {_ns.get('step_id')} — "
                                            f"tool={_ns.get('tool')}, purpose={_ns.get('purpose')}"
                                        )
                                    raw_reply = agent3.call(
                                        f"## Agent7 step {_cur_step_id} applied directly by orchestrator\n"
                                        f"exit={last_exit_code}, sorry={last_sorry_in_attempt}\n"
                                        f"Protected content (do NOT remove):\n```lean\n{_da_new}\n```"
                                        + _next_step_hint
                                    )
                                    token_char_budget += len(raw_reply)
                                    continue
                                except (ValueError, FileNotFoundError) as _da_exc:
                                    # old_str not found or file missing — fall through to Agent3
                                    console.print(
                                        f"  [Agent7 DirectApply] step {_cur_step_id} failed "
                                        f"({_da_exc!r}) — delegating to Agent3"
                                    )
                                    # Fall through to normal gate flow below

                        if _cur_tool and tool_name != _cur_tool:
                            agent7_blocked_actions.append({
                                "attempt": attempt,
                                "turn": tool_turn + 1,
                                "reason": "wrong_step_tool",
                                "requested_tool": tool_name,
                                "expected_tool": _cur_tool,
                                "expected_step_id": _cur_step_id,
                            })
                            raw_reply = agent3.call(
                                "## AGENT7_STEP_REJECTED\n"
                                f"Current protocol step is {_cur_step_id} and requires tool `{_cur_tool}`. "
                                "Execute that step first."
                            )
                            token_char_budget += len(raw_reply)
                            continue
                        _executed_step_id = str(arguments.get("executed_step_id", "")).strip()
                        if _executed_step_id != _cur_step_id:
                            agent7_blocked_actions.append({
                                "attempt": attempt,
                                "turn": tool_turn + 1,
                                "reason": "step_id_mismatch",
                                "requested_tool": tool_name,
                                "executed_step_id": _executed_step_id,
                                "expected_step_id": _cur_step_id,
                            })
                            raw_reply = agent3.call(
                                "## AGENT7_STEP_REJECTED\n"
                                f"Include `executed_step_id: \"{_cur_step_id}\"` in arguments and retry."
                            )
                            token_char_budget += len(raw_reply)
                            continue
                        arguments = dict(arguments)
                        arguments.pop("executed_step_id", None)

                # "done" signal: force verify, NEVER trust Agent3's self-report
                if tool_name == "done":
                    forced_verify = registry.call("run_lean_verify", target_file)
                    forced_exit = int(forced_verify.get("exit_code", 1))
                    forced_sorry = int(forced_verify.get("sorry_count", 0))
                    current_hash = _file_hash(target_file)
                    file_changed = (snapshot_file(target_file) != "") and (
                        (not initial_exists) or (current_hash != initial_hash)
                    )
                    if forced_exit == 0 and forced_sorry == 0 and file_changed:
                        # Full-library gate
                        full_build = registry.call("run_repo_verify")
                        if int(full_build.get("exit_code", 1)) == 0:
                            execution_history.extend(exec_results)
                            console.print(
                                f"  [Agent3] attempt {attempt}/{max_retries} — "
                                f"build=OK, sorry=0 (done at turn {tool_turn + 1})"
                            )
                            # Success: restore any shared Glue/Layer0 files Agent3 may have edited.
                            for _gp, _goriginal in _glue_snapshot.items():
                                _gp_rel = str(_gp.relative_to(PROJECT_ROOT))
                                if snapshot_file(_gp_rel) != _goriginal:
                                    registry.call("overwrite_file", path=_gp_rel, content=_goriginal)
                                    console.print(f"  [Glue] Restored {_gp.name} (was modified)")
                            for _lp, _loriginal in _layer0_snapshot.items():
                                _lp_rel = str(_lp.relative_to(PROJECT_ROOT))
                                if snapshot_file(_lp_rel) != _loriginal:
                                    registry.call("overwrite_file", path=_lp_rel, content=_loriginal)
                                    console.print(f"  [Layer0] Restored {_lp.name} (was modified by Agent3)")
                            # Re-verify target file AFTER Glue/Layer0 restoration.
                            # If the proof relied on Agent3's Glue edits, restoration
                            # will break it here rather than silently declaring false success.
                            _post_restore = registry.call("run_lean_verify", target_file)
                            if not (
                                int(_post_restore.get("exit_code", 1)) == 0
                                and int(_post_restore.get("sorry_count", -1)) == 0
                            ):
                                console.print(
                                    "[yellow][Gate1] Target re-verify FAILED after Glue restoration "
                                    "— proof depended on modified Glue files. Continuing attempt."
                                )
                                last_errors = str(_post_restore.get("errors", ""))
                                break  # exit tool loop, retry attempt
                            return True, attempts, "", {
                                "execution_history": [r.__dict__ for r in execution_history],
                                "attempt_failures": attempt_failures,
                                "agent7_invocations": agent7_invocations,
                                "agent7_step_execution_log": agent7_step_execution_log,
                                "agent7_plan_revisions": agent7_plan_revisions,
                                "agent7_blocked_actions": agent7_blocked_actions,
                                "agent7_forced_trigger_count": agent7_forced_trigger_count,
                                "agent7_force_gate_entries": agent7_force_gate_entries,
                                "agent7_force_gate_rejections": agent7_force_gate_rejections,
                                "agent7_force_gate_reason_samples": agent7_force_gate_reason_samples,
                                "estimated_token_consumption": max(1, token_char_budget // 4),
                                "retry_count": sum(
                                    1 for r in execution_history
                                    if r.status_code in {"ERROR", "BLOCKED"}
                                ),
                            }
                        else:
                            full_errors = "\n".join(full_build.get("errors", [])) or "SGDAlgorithms full build failed"
                            last_errors = full_errors
                            exec_results.append(ExecutionResult(
                                status_code="ERROR",
                                message=f"[Full-Build Gate] SGDAlgorithms failed:\n{full_errors[:800]}",
                                attempt=attempt,
                            ))
                            raw_reply = agent3.call(
                                f"## done rejected — full library build failed\n"
                                f"```\n{full_errors[:2000]}\n```\n"
                                "Fix the cascade failure, then signal done again."
                            )
                            token_char_budget += len(raw_reply)
                            continue
                    else:
                        # Not actually done — tell Agent3 the real state
                        rejection = _format_done_rejection(forced_verify, target_file)
                        raw_reply = agent3.call(rejection)
                        token_char_budget += len(raw_reply)
                    continue

                # ---------------------------------------------------------------
                # Agent3 → Agent6 glue escalation: infrastructure gap handoff
                # Agent3 autonomy branch: Agent3 calls Agent6 directly when it
                # diagnoses a missing glue lemma — no Agent7 pre-screen required.
                # ---------------------------------------------------------------
                if tool_name == "request_agent6_glue":

                    max_agent6 = RETRY_LIMITS.get("MAX_AGENT6_ESCALATIONS_PER_ATTEMPT", 1)
                    stuck_at_line = arguments.get("stuck_at_line") or arguments.get("sorry_line") or "unknown"
                    error_message = str(arguments.get("error_message", ""))[:600]
                    diagnosis = str(arguments.get("diagnosis", ""))[:800]
                    extra_context = str(arguments.get("extra_context", ""))[:600]
                    try:
                        _line_int = int(stuck_at_line) if str(stuck_at_line).isdigit() else 1
                        g = registry.call("get_lean_goal", file_path=target_file, sorry_line=_line_int)
                        goal = (g.get("goal") or g.get("raw") or "").strip()
                        hypotheses = g.get("hypotheses")
                        if not isinstance(hypotheses, list):
                            hypotheses = []
                    except Exception:
                        goal = ""
                        hypotheses = []
                    if not goal:
                        raw_reply = agent3.call(
                            "## request_agent6_glue rejected — could not obtain goal from LSP\n"
                            "Call get_lean_goal first, then retry request_agent6_glue."
                        )
                        token_char_budget += len(raw_reply)
                        continue
                    _candidate_escalation = _agent6_escalation_count + 1
                    if _candidate_escalation > max_agent6:
                        raw_reply = agent3.call(
                            "## request_agent6_glue rejected — limit reached\n"
                            f"At most {max_agent6} handoff(s) to Agent6 per attempt. "
                            "Use request_agent2_help instead."
                        )
                        token_char_budget += len(raw_reply)
                        continue
                    _current_goal_sig = hashlib.md5(goal[:1000].encode("utf-8")).hexdigest()
                    if _candidate_escalation == 2:
                        _same_goal_ok = (not _agent6_second_require_same_goal) or (
                            _agent6_first_goal_sig is not None and _current_goal_sig == _agent6_first_goal_sig
                        )
                        _progress_ok = _agent6_first_progress_ok
                        if not (_same_goal_ok and _progress_ok):
                            raw_reply = agent3.call(
                                "## request_agent6_glue rejected — second escalation gate\n"
                                "Second Agent6 escalation is allowed only when:\n"
                                f"1) first Agent6 call reduced sorry_count by at least {_agent6_second_min_progress}; and\n"
                                "2) current goal is the same structural goal.\n"
                                "Continue local/tactical repair or call request_agent2_help."
                            )
                            token_char_budget += len(raw_reply)
                            continue
                    _agent6_escalation_count = _candidate_escalation
                    _attempt_esc_a6 += 1
                    console.print(
                        f"  [Agent3→Agent6] Glue handoff #{_agent6_escalation_count} at turn "
                        f"{tool_turn + 1}: stuck at line {stuck_at_line}"
                    )
                    _pre_agent6_sorry = last_sorry_in_attempt
                    success, msg = _run_agent6_glue_loop(
                        agent6,
                        agent6_registry,
                        target_file,
                        goal,
                        error_message,
                        diagnosis,
                        _algo_name,
                        hypotheses=hypotheses,
                        extra_context=extra_context or None,
                        stuck_line=_line_int,
                    )
                    if success:
                        exec_results.append(ExecutionResult(
                            status_code="SUCCESS",
                            message=f"request_agent6_glue: succeeded (turn {tool_turn + 1})",
                            attempt=attempt,
                        ))
                        # Immediate target regression verify so Agent3 knows whether glue fixed target.
                        _target_verify_after_agent6 = registry.call("run_lean_verify", target_file)
                        _tv_exit = int(_target_verify_after_agent6.get("exit_code", 1))
                        _tv_sorry = int(_target_verify_after_agent6.get("sorry_count", 0))
                        _tv_errors = _target_verify_after_agent6.get("errors", [])
                        _tv_error_text = (
                            "\n".join(_tv_errors[:5]) if isinstance(_tv_errors, list) else str(_tv_errors)
                        )
                        _progress_delta = max(0, _pre_agent6_sorry - _tv_sorry)
                        if _candidate_escalation == 1:
                            _agent6_first_goal_sig = _current_goal_sig
                            _agent6_first_progress_ok = _progress_delta >= _agent6_second_min_progress
                        raw_reply = agent3.call(
                            msg
                            + "\n\n## Target regression verify after Agent6\n"
                            + f"exit_code: {_tv_exit} | sorry_count: {_tv_sorry}\n"
                            + (
                                f"Top errors:\n```\n{_tv_error_text[:1200]}\n```\n"
                                if _tv_error_text else ""
                            )
                            + (
                                "Glue helped but target is still failing. Continue fixing target file.\n"
                                if not (_tv_exit == 0 and _tv_sorry == 0)
                                else "Target is now clean.\n"
                            )
                        )
                    else:
                        _stuck_line_int = int(stuck_at_line) if str(stuck_at_line).isdigit() else None
                        _current_snippet = _build_escalation_file_context(target_file, _stuck_line_int)
                        new_guidance, _ = _call_agent2_with_tools(
                            agent2,
                            escalation_registry,
                            f"[AGENT6 FALLBACK — Agent6 could not prove helper lemma]\n"
                            f"Agent3 escalated with infrastructure diagnosis. Agent6 failed.\n\n"
                            f"Error: {error_message}\nDiagnosis: {diagnosis}\n\n"
                            f"Target: {target_file} line {stuck_at_line}. Goal: {goal[:500]}...\n\n"
                            f"=== CURRENT FILE ({target_file}) ===\n```lean\n{_current_snippet}\n```\n\n"
                            f"Provide revised guidance. Agent3 continues in the SAME attempt.",
                        )
                        raw_reply = agent3.call(
                            f"## Agent6 could not fill glue — Agent2 guidance\n{new_guidance}\n\n"
                            "Apply this guidance now. Continue with tool calls."
                        )
                    token_char_budget += len(raw_reply)
                    continue

                # ---------------------------------------------------------------
                # Agent3 → Agent2 escalation: mid-attempt help request
                # ---------------------------------------------------------------
                if tool_name == "request_agent2_help":
                    _escalation_count += 1
                    _attempt_esc_a2 += 1
                    if _escalation_count > 5:
                        esc_msg = (
                            "## Escalation limit reached\n"
                            "You have already escalated 5 times this sorry. "
                            "Use your existing tools to make progress or call done."
                        )
                        raw_reply = agent3.call(esc_msg)
                        token_char_budget += len(esc_msg) + len(raw_reply)
                        continue
                    stuck_at_line = arguments.get("stuck_at_line", "unknown")
                    error_message = str(arguments.get("error_message", ""))[:600]
                    diagnosis = str(arguments.get("diagnosis", ""))[:800]
                    attempts_tried = int(arguments.get("attempts_tried", tool_turn + 1))
                    console.print(
                        f"  [Agent3→Agent2] Escalation #{_escalation_count} at turn "
                        f"{tool_turn + 1}: stuck at line {stuck_at_line}"
                    )
                    diag_log.append(
                        f"attempt={attempt} turn={tool_turn} "
                        f"Agent3 escalation: {diagnosis[:200]}"
                    )
                    _stuck_line_int = int(stuck_at_line) if str(stuck_at_line).isdigit() else None
                    current_file_snippet = _build_escalation_file_context(target_file, _stuck_line_int)
                    new_guidance, _a2_route_mid = _call_agent2_with_tools(
                        agent2,
                        escalation_registry,
                        f"[AGENT3 ESCALATION — MID-ATTEMPT HELP REQUEST]\n"
                        f"Agent3 is stuck on line {stuck_at_line} after "
                        f"{attempts_tried} turns.\n\n"
                        f"Agent3's error:\n```\n{error_message}\n```\n\n"
                        f"Agent3's diagnosis:\n{diagnosis}\n\n"
                        f"=== CURRENT FILE ({target_file}) ===\n"
                        f"```lean\n{current_file_snippet}\n```\n\n"
                        "Apply your Sorry-Fill Proof Path Protocol. "
                        "Classify the problem as structural (A) or tactical (B) "
                        "and provide revised, concrete guidance with exact Lean API "
                        "calls. Agent3 will continue in the SAME attempt.\n"
                        "If a Level-2 missing glue lemma is needed, add it directly "
                        f"in {target_file} before the main theorem.\n"
                        "ROUTING RULE: If this error is a structural INTERFACE problem — "
                        "invalid field notation, wrong function signature, mismatched "
                        "dot-access path — output exactly `ROUTE_TO: agent7` on its own "
                        "line BEFORE your analysis. The orchestrator will call Agent7 "
                        "automatically and deliver the audit protocol to Agent3.",
                    )
                    # Apply Agent2 router: "self" is forbidden mid-attempt.
                    _mid_route_budget = dict(_routing_budget)  # snapshot (no self mid-attempt)
                    _mid_route_budget["self_revisions"] = 9999  # disable self mid-attempt
                    _final_route_mid = _apply_agent2_route(
                        _a2_route_mid, _mid_route_budget, _err_sig, _route_repeat_tracker
                    )
                    # B: parse Agent2's routing signal — new JSON protocol + legacy ROUTE_TO fallback
                    _a2_wants_agent7 = _final_route_mid in ("agent7", "agent7_then_agent6")
                    _legacy_agent7 = bool(re.search(
                        r"^ROUTE_TO:\s*agent7\s*$", new_guidance,
                        re.IGNORECASE | re.MULTILINE,
                    ))
                    if (_a2_wants_agent7 or _legacy_agent7) and _agent7_invocations_this_attempt < _agent7_max_invocations:
                        _agent7_invocations_this_attempt += 1
                        _route_label = "JSON" if _a2_wants_agent7 else "legacy"
                        console.print(
                            f"  [Agent3→Agent2→Agent7] Agent2 routed to Agent7 "
                            f"(escalation #{_escalation_count}, "
                            f"invocation #{_agent7_invocations_this_attempt}, "
                            f"protocol={_route_label})"
                        )
                        _agent7_esc_snippet = _build_escalation_file_context(
                            target_file, _stuck_line_int
                        )
                        _a7_hint_mid = (_a2_route_mid or {}).get("agent7_hint", "") if _a2_route_mid else ""
                        _agent7_esc_prompt = (
                            "Produce a strict interface-audit protocol JSON for Agent3.\n"
                            f"Target file: {target_file}\n"
                            f"Stuck at line: {stuck_at_line}\n"
                            f"Escalated via Agent2 routing (structural interface problem).\n\n"
                            f"Primary error:\n```\n{error_message}\n```\n\n"
                            f"Diagnosis:\n{diagnosis}\n\n"
                            + (f"Agent2 routing hint:\n{_a7_hint_mid}\n\n" if _a7_hint_mid else "")
                            + f"Agent2 analysis:\n{new_guidance[:2000]}\n\n"
                            f"Current file (full when ≤500 lines):\n```lean\n{_agent7_esc_snippet[:20000]}\n```\n\n"
                            "Return strict JSON only as specified in your system prompt."
                        )
                        _plan_obj_esc, _raw_plan_esc = _call_agent7_with_tools(
                            agent7, agent7_registry,
                            _agent7_esc_prompt,
                        )
                        if _plan_obj_esc:
                            _active_agent7_plan = _plan_obj_esc
                            _agent7_current_step_idx = 0
                        if _final_route_mid == "agent7_then_agent6":
                            _ft_mid = (_plan_obj_esc or {}).get("fallback_trigger", {}) if _plan_obj_esc else {}
                            _agent7_approved_agent6 = str(_ft_mid.get("route_to", "")).lower() == "agent6"
                            console.print(f"  [A2Router→Agent7→Agent6] agent6_approved={_agent7_approved_agent6}")
                        esc_result_msg = (
                            f"## Agent7 Interface Audit "
                            f"(routed by Agent2 [{_route_label}], escalation #{_escalation_count})\n"
                            "Agent2 classified this as a structural interface problem "
                            "and escalated to Agent7.\n\n"
                            f"{_raw_plan_esc}\n\n"
                            "Execute Agent7's protocol: one step at a time, "
                            "run_lean_verify after each."
                        )
                    else:
                        esc_result_msg = (
                            f"## Agent2 Revised Guidance (escalation #{_escalation_count})\n"
                            f"{new_guidance}\n\n"
                            "Apply this guidance now. Continue with tool calls."
                        )
                    exec_results.append(ExecutionResult(
                        status_code="SUCCESS",
                        message=(
                            f"request_agent2_help: escalation #{_escalation_count} "
                            f"processed (turn {tool_turn + 1})"
                        ),
                        attempt=attempt,
                    ))
                    raw_reply = agent3.call(esc_result_msg)
                    token_char_budget += len(esc_result_msg) + len(raw_reply)
                    continue

                # Track lookup activity for runtime trajectory check.
                _is_lookup_tool = tool_name in (
                    "read_file", "read_file_readonly",
                    "search_in_file", "search_in_file_readonly", "search_codebase",
                )
                if _is_lookup_tool:
                    _lookup_done_since_last_edit = True

                # Patch symbol pre-check: warn Agent3 about unverified identifiers
                # before applying the patch (P1 - symbol existence gate).
                if tool_name == "edit_file_patch":
                    _patch_warning = _check_patch_symbols(arguments, registry)
                    # Hard gate: if a patch introduces unverifiable external symbols,
                    # Agent3 must perform lookup first even on the first patch turn.
                    if not _lookup_done_since_last_edit and _patch_warning:
                        console.print(
                            f"  [PatchSymbolGate] attempt {attempt} turn {tool_turn + 1} — "
                            "blocking patch until lookup evidence exists"
                        )
                        _gate_msg = (
                            "## BLOCKED — LOOKUP EVIDENCE REQUIRED BEFORE PATCH\n"
                            "Your patch introduces external identifiers that are not backed by "
                            "lookup evidence from this attempt.\n\n"
                            f"{_patch_warning}\n\n"
                            "Do NOT patch again yet. First call search_codebase, search_in_file, "
                            "read_file, or check_lean_expr to verify the exact current API, then "
                            "re-issue a minimal edit_file_patch."
                        )
                        raw_reply = agent3.call(_gate_msg)
                        token_char_budget += len(_gate_msg) + len(raw_reply)
                        continue

                    # Runtime trajectory check (kept for pure local/syntax patches):
                    # if no lookup occurred, remind Agent3 to verify before broader edits.
                    if not _lookup_done_since_last_edit and tool_turn > 0:
                        _patch_without_lookup_count += 1
                        if _patch_without_lookup_count <= 2:
                            _traj_warning = (
                                "## ⚠ TRAJECTORY VIOLATION — PATCH WITHOUT LOOKUP\n"
                                "You are patching without having called search_codebase, "
                                "search_in_file, or read_file since the last edit.\n\n"
                                "This is only acceptable for purely local syntax/binder fixes. "
                                "If the patch touches any external API, verify it first.\n"
                            )
                            raw_reply = agent3.call(_traj_warning)
                            token_char_budget += len(_traj_warning) + len(raw_reply)
                            continue
                    _lookup_done_since_last_edit = False  # reset after edit

                # Pre-edit snapshot: capture file content before Agent3's patch so
                # we can rollback if protected content (from DirectApply) is removed.
                _pre_edit_snapshot: str | None = None
                if tool_name == "edit_file_patch" and _direct_applied_patches:
                    try:
                        _pre_edit_snapshot = load_file(target_file)
                    except Exception:  # noqa: BLE001
                        _pre_edit_snapshot = None

                # Execute single tool and format result for Agent3
                result_msg, verify_result, edited = _execute_single_tool_and_format(
                    registry, tool_name, arguments, target_file
                )
                token_char_budget += len(result_msg)

                # Protection check: if Agent3's edit removed orchestrator-applied
                # content, roll back and warn.
                if (
                    tool_name == "edit_file_patch"
                    and edited
                    and _pre_edit_snapshot is not None
                    and _direct_applied_patches
                ):
                    try:
                        _current_content = load_file(target_file)
                    except Exception:  # noqa: BLE001
                        _current_content = ""
                    _violations = [
                        p for p in _direct_applied_patches
                        if p.get("path") in (target_file, str(Path(target_file).name))
                        and p["new_str"] not in _current_content
                    ]
                    if _violations:
                        registry.call(
                            "overwrite_file", path=target_file, content=_pre_edit_snapshot
                        )
                        _viol_desc = "\n".join(
                            f"  step {v['step_id']}: {v['new_str'][:120]!r}"
                            for v in _violations
                        )
                        console.print(
                            f"  [Agent7 DirectApply] attempt {attempt} turn {tool_turn + 1} — "
                            "protected content removed by Agent3 edit; rolling back"
                        )
                        raw_reply = agent3.call(
                            "## PROTECTED CONTENT VIOLATION — edit reverted\n"
                            "Your edit removed content applied directly by the orchestrator. "
                            "The edit has been rolled back.\n"
                            "The following content must remain in the file at all times:\n"
                            f"{_viol_desc}\n"
                            "Rewrite your patch to preserve these lines exactly."
                        )
                        token_char_budget += len(raw_reply)
                        edited_this_attempt = False
                        continue
                if (
                    _active_agent7_plan is not None
                    and not _agent7_pending_verify
                    and tool_name != "run_lean_verify"
                ):
                    _steps = _active_agent7_plan.get("ordered_steps", [])
                    if isinstance(_steps, list) and _steps:
                        _idx = min(_agent7_current_step_idx, len(_steps) - 1)
                        _agent7_last_step_id = str(_steps[_idx].get("step_id", f"S{_idx + 1}"))
                        _agent7_pending_verify = True
                        _agent7_prev_sorry = last_sorry_in_attempt

                if edited:
                    edited_this_attempt = True
                if "PATCH MISMATCH" in result_msg:
                    patch_mismatch_in_attempt = True

                exec_results.append(ExecutionResult(
                    status_code="SUCCESS" if not result_msg.startswith("## Tool error") else "ERROR",
                    message=f"{tool_name}: {result_msg[:120]}",
                    attempt=attempt,
                ))

                if time.time() - _last_audit_flush_time >= AUDIT_FLUSH_INTERVAL_SECONDS:
                    _last_audit_flush_time = time.time()
                    try:
                        _audit = AuditLogger.get()
                        _exec_full = [r.__dict__ for r in execution_history] + [r.__dict__ for r in exec_results]
                        _audit.flush_audit_incremental(
                            execution_history=_exec_full,
                            attempt_failures=attempt_failures,
                            agent3_turns=agent3_turns,
                            extra={
                                "agent7_invocations": agent7_invocations,
                                "agent7_step_execution_log": agent7_step_execution_log,
                                "agent7_plan_revisions": agent7_plan_revisions,
                                "agent7_blocked_actions": agent7_blocked_actions,
                                "agent7_forced_trigger_count": agent7_forced_trigger_count,
                                "agent7_force_gate_entries": agent7_force_gate_entries,
                                "agent7_force_gate_rejections": agent7_force_gate_rejections,
                                "agent7_force_gate_reason_samples": agent7_force_gate_reason_samples,
                            },
                        )
                    except Exception:
                        pass

                # Process run_lean_verify results inline
                if tool_name == "run_lean_verify" and verify_result is not None:
                    last_verify_result = verify_result
                    last_exit_code = int(verify_result.get("exit_code", 1))
                    last_sorry_in_attempt = int(verify_result.get("sorry_count", 0))
                    verify_errors = verify_result.get("errors", [])
                    last_verify_text = (
                        "\n".join(verify_errors)
                        if isinstance(verify_errors, list) else str(verify_errors)
                    )
                    last_sorry_count = last_sorry_in_attempt
                    last_errors = last_verify_text
                    if _agent7_last_verified_sorry is not None:
                        if last_sorry_in_attempt < _agent7_last_verified_sorry:
                            _agent7_no_progress_turns = 0
                        else:
                            _agent7_no_progress_turns += 1
                    _agent7_last_verified_sorry = last_sorry_in_attempt

                    # Agent7 execution gate: evaluate current step only on verify.
                    if _active_agent7_plan is not None and _agent7_pending_verify:
                        _current_line = _extract_first_error_line(last_verify_text)
                        _progress = (
                            last_sorry_in_attempt < _agent7_prev_sorry
                            or (last_exit_code == 0 and last_sorry_in_attempt == 0)
                        )
                        _regress = last_sorry_in_attempt > _agent7_prev_sorry
                        if _regress:
                            _agent7_no_progress_count += 1
                        elif _progress:
                            _agent7_no_progress_count = 0
                        else:
                            _agent7_no_progress_count += 1
                        agent7_step_execution_log.append({
                            "attempt": attempt,
                            "turn": tool_turn + 1,
                            "step_id": _agent7_last_step_id,
                            "exit_code": last_exit_code,
                            "sorry_before": _agent7_prev_sorry,
                            "sorry_after": last_sorry_in_attempt,
                            "error_line": _current_line,
                            "accepted": bool(_progress and not _regress),
                        })
                        if _progress and not _regress:
                            exec_results.append(ExecutionResult(
                                status_code="SUCCESS",
                                message=f"AGENT7_STEP_ACCEPTED {(_agent7_last_step_id or '')}",
                                attempt=attempt,
                            ))
                            _steps = _active_agent7_plan.get("ordered_steps", [])
                            if isinstance(_steps, list):
                                _agent7_current_step_idx = min(
                                    _agent7_current_step_idx + 1, max(0, len(_steps) - 1)
                                )
                            _agent7_pending_verify = False
                        elif _agent7_no_progress_count >= _agent7_no_progress_threshold:
                            exec_results.append(ExecutionResult(
                                status_code="BLOCKED",
                                message=(
                                    f"AGENT7_STEP_REJECTED {(_agent7_last_step_id or '')} "
                                    "no progress threshold reached"
                                ),
                                attempt=attempt,
                            ))
                            _agent7_pending_verify = False
                            _agent7_no_progress_count = 0
                            _agent7_invocations_this_attempt += 1
                            _line_int = _current_line or 1
                            current_snippet = _build_escalation_file_context(target_file, _line_int)
                            dep_sigs = _prequery_dependency_signatures(last_verify_text, target_file)
                            _recent_failures = json.dumps(
                                [a for a in attempt_failures if a.get("attempt") == attempt][-8:],
                                ensure_ascii=False,
                            )[:3000]
                            revised_prompt = (
                                "Revise prior interface-audit protocol due to no progress.\n"
                                f"Target file: {target_file}\n"
                                f"Line: {_line_int}\n"
                                f"Latest verify errors:\n```\n{last_verify_text[:2000]}\n```\n\n"
                                f"Recent failures:\n```\n{_recent_failures}\n```\n\n"
                                f"Current file (full when ≤500 lines):\n```lean\n{current_snippet[:20000]}\n```\n\n"
                                f"Dependency signatures:\n```lean\n{dep_sigs[:4000]}\n```\n\n"
                                "Return strict JSON protocol only."
                            )
                            _revised_plan, _raw = _call_agent7_with_tools(
                                agent7, agent7_registry, revised_prompt
                            )
                            if _revised_plan:
                                _active_agent7_plan = _revised_plan
                                _agent7_current_step_idx = 0
                                _agent7_last_step_id = None
                                _agent7_prev_sorry = last_sorry_in_attempt
                                agent7_plan_revisions.append({
                                    "attempt": attempt,
                                    "turn": tool_turn + 1,
                                    "reason": "no_progress",
                                    "plan_size": len(_revised_plan.get("ordered_steps", [])),
                                })
                                raw_reply = agent3.call(
                                    "## Agent7 protocol revised due to no progress\n"
                                    "Execute the new first step with executed_step_id and verify immediately."
                                )
                                token_char_budget += len(raw_reply)
                                continue
                        else:
                            exec_results.append(ExecutionResult(
                                status_code="BLOCKED",
                                message=f"AGENT7_STEP_REJECTED {(_agent7_last_step_id or '')}",
                                attempt=attempt,
                            ))
                            _agent7_pending_verify = False

                    # Checkpoint: save verified state whenever sorry count improves.
                    # Only verified (compilable) states are checkpointed.
                    if (
                        last_exit_code == 0
                        and
                        last_sorry_in_attempt < best_checkpoint["sorry_count"]
                        and snapshot_file(target_file) != ""
                    ):
                        best_checkpoint = {
                            "sorry_count": last_sorry_in_attempt,
                            "content": load_file(target_file),
                        }
                        console.print(
                            f"  [Checkpoint] Updated: sorry={last_sorry_in_attempt}"
                        )
                    elif (
                        last_exit_code == 0
                        and last_sorry_in_attempt > best_checkpoint["sorry_count"]
                        and best_checkpoint["content"] is not None
                        and snapshot_file(target_file) != ""
                    ):
                        registry.call("overwrite_file", path=target_file, content=best_checkpoint["content"])
                        result_msg = (
                            "## REGRESSION DETECTED\n"
                            f"Sorry count regressed from {best_checkpoint['sorry_count']} to {last_sorry_in_attempt}. "
                            f"Auto-restored checkpoint (sorry={best_checkpoint['sorry_count']}).\n"
                            "Do NOT repeat the previous patch. Try a different strategy.\n\n"
                        ) + result_msg
                        last_sorry_in_attempt = int(best_checkpoint["sorry_count"])
                        last_sorry_count = last_sorry_in_attempt
                        console.print(
                            f"  [Checkpoint] REGRESSION: sorry {verify_result.get('sorry_count', '?')} "
                            f"> {best_checkpoint['sorry_count']} — auto-restored"
                        )

                    # Per-sorry closure detection: check if the active sorry line is gone.
                    if (
                        _active_sorry_line is not None
                        and not _is_line_still_sorry(target_file, _active_sorry_line)
                    ):
                        _active_sorry_closed = True
                        console.print(
                            f"  [PerSorry] Line {_active_sorry_line} closed "
                            f"(attempt {attempt}, turn {tool_turn + 1})"
                        )

                    # Auto-done: verify already shows exit=0 sorry=0 mid-turn —
                    # lock the result immediately so Agent3 cannot over-edit.
                    if last_exit_code == 0 and last_sorry_in_attempt == 0:
                        _auto_hash = _file_hash(target_file)
                        _auto_changed = (snapshot_file(target_file) != "") and (
                            (not initial_exists) or (_auto_hash != initial_hash)
                        )
                        if _auto_changed:
                            console.print(
                                f"  [AutoDone] a{attempt} t{tool_turn + 1} — "
                                "verify=0/0; running full-library gate"
                            )
                            _auto_full = registry.call("run_repo_verify")
                            if int(_auto_full.get("exit_code", 1)) == 0:
                                execution_history.extend(exec_results)
                                console.print(
                                    f"  [Agent3] attempt {attempt}/{max_retries} — "
                                    f"build=OK, sorry=0 (auto-done at turn {tool_turn + 1})"
                                )
                                for _gp, _goriginal in _glue_snapshot.items():
                                    _gp_rel = str(_gp.relative_to(PROJECT_ROOT))
                                    if snapshot_file(_gp_rel) != _goriginal:
                                        registry.call("overwrite_file", path=_gp_rel, content=_goriginal)
                                        console.print(f"  [Glue] Restored {_gp.name} (was modified)")
                                for _lp, _loriginal in _layer0_snapshot.items():
                                    _lp_rel = str(_lp.relative_to(PROJECT_ROOT))
                                    if snapshot_file(_lp_rel) != _loriginal:
                                        registry.call("overwrite_file", path=_lp_rel, content=_loriginal)
                                        console.print(f"  [Layer0] Restored {_lp.name} (was modified by Agent3)")
                                # Re-verify target file AFTER Glue/Layer0 restoration.
                                _auto_post_restore = registry.call("run_lean_verify", target_file)
                                if not (
                                    int(_auto_post_restore.get("exit_code", 1)) == 0
                                    and int(_auto_post_restore.get("sorry_count", -1)) == 0
                                ):
                                    console.print(
                                        "[yellow][AutoDone] Target re-verify FAILED after Glue restoration "
                                        "— proof depended on modified Glue files. Continuing attempt."
                                    )
                                    last_errors = str(_auto_post_restore.get("errors", ""))
                                    break  # exit tool loop, retry attempt
                                return True, attempts, "", {
                                    "execution_history": [r.__dict__ for r in execution_history],
                                    "attempt_failures": attempt_failures,
                                    "agent7_invocations": agent7_invocations,
                                    "agent7_step_execution_log": agent7_step_execution_log,
                                    "agent7_plan_revisions": agent7_plan_revisions,
                                    "agent7_blocked_actions": agent7_blocked_actions,
                                    "agent7_forced_trigger_count": agent7_forced_trigger_count,
                                    "agent7_force_gate_entries": agent7_force_gate_entries,
                                    "agent7_force_gate_rejections": agent7_force_gate_rejections,
                                    "agent7_force_gate_reason_samples": agent7_force_gate_reason_samples,
                                    "estimated_token_consumption": max(1, token_char_budget // 4),
                                    "retry_count": sum(
                                        1 for r in execution_history
                                        if r.status_code in {"ERROR", "BLOCKED"}
                                    ),
                                }
                            else:
                                _auto_full_errors = (
                                    "\n".join(_auto_full.get("errors", []))
                                    or "SGDAlgorithms full build failed"
                                )
                                last_errors = _auto_full_errors
                                exec_results.append(ExecutionResult(
                                    status_code="ERROR",
                                    message=f"[AutoDone Full-Build Gate] SGDAlgorithms failed:\n{_auto_full_errors[:800]}",
                                    attempt=attempt,
                                ))
                                console.print(
                                    f"  [AutoDone] Full-library gate FAILED at turn {tool_turn + 1} "
                                    "— Agent3 must fix cascade"
                                )

                    if progress_detail in ("normal", "debug"):
                        _src_s  = last_sorry_in_attempt
                        _cln_s  = last_verify_result.get("sorry_declarations", _src_s) if last_verify_result else _src_s
                        _blk_s  = last_verify_result.get("blocked_sorry_count", 0)     if last_verify_result else 0
                        _sorry_display = (
                            f"sorry={_src_s} ({_cln_s} clean, {_blk_s} blocked)"
                            if _blk_s > 0 else f"sorry={_src_s}"
                        )
                        console.print(
                            f"  [A3] a{attempt}/{max_retries} "
                            f"t{tool_turn + 1}/{_per_sorry_remaining} — "
                            f"exit={last_exit_code} {_sorry_display}"
                            + (f" [L{_active_sorry_line} closed]" if _active_sorry_closed else "")
                        )
                    if last_exit_code != 0 and last_verify_text:
                        _err_sig = last_verify_text[:80]
                        if _err_sig != _last_printed_err_sig or progress_detail == "debug":
                            _last_printed_err_sig = _err_sig
                            _err_chars = 200 if progress_detail == "normal" else 400
                            console.print(f"[dim]  {last_verify_text[:_err_chars]}[/dim]")

                    # Parse structured errors for inner loop (used by prioritize + routing).
                    _structured_errors_inner = _parse_lean_errors(last_verify_text)
                    _inner_err_line = _extract_first_error_line(last_verify_text)

                    if last_exit_code != 0:
                        _primary_inner = _structured_errors_inner[0] if _structured_errors_inner else {}
                        attempt_failures.append({
                            "attempt": attempt,
                            "exit_code": last_exit_code,
                            "sorry_count": last_sorry_in_attempt,
                            "line": _primary_inner.get("line"),
                            "message": str(_primary_inner.get("message", "")),
                            "lean_errors": _prioritize_error_text(
                                _structured_errors_inner, last_verify_text,
                                _inner_err_line, target_file
                            ),
                            "target_file_content": (
                                load_file(target_file)[:50000] if _target_exists_overlay() else None
                            ),
                        })

                    # Classify error with structured parser, passing target_file for routing.
                    error_type, _structured_errors_inner = _classify_lean_error_structured(
                        last_verify_text, target_file
                    )
                    # A2: LLM fallback — upgrade PROOF_ERROR to DEFINITION_ZONE_ERROR when
                    # all regex missed but the error sits inside the declaration zone.
                    if error_type == "PROOF_ERROR" and _structured_errors_inner:
                        _primary_for_llm = _structured_errors_inner[0]
                        _pline_fb = _primary_for_llm.get("line", 9999)
                        try:
                            _tgt_lines_fb = (PROJECT_ROOT / target_file).read_text(encoding="utf-8").splitlines()
                            _dz_map_fb = _build_decl_zone_map(_tgt_lines_fb)
                        except OSError:
                            _dz_map_fb = []
                        if _is_in_declaration_zone(_pline_fb, _dz_map_fb):
                            _llm_fb = _llm_classify_error(
                                _primary_for_llm,
                                _build_escalation_file_context(target_file, _pline_fb),
                                target_file,
                            )
                            if _llm_fb.get("locus") == "declaration_zone":
                                error_type = "DEFINITION_ZONE_ERROR"
                    err_line_no = _extract_first_error_line(last_verify_text)
                    line_no_display = str(err_line_no) if err_line_no is not None else "unknown"
                    if last_exit_code != 0:
                        if err_line_no is not None and err_line_no == _stale_err_line:
                            _stale_err_count += 1
                        else:
                            _stale_err_line = err_line_no
                            _stale_err_count = 1
                    else:
                        _stale_err_line = None
                        _stale_err_count = 0

                    # ---- Conservative routing override gates ----
                    # These gates run BEFORE the main error-type dispatch.  They
                    # upgrade LOCAL_PROOF_ERROR / PROOF_ERROR to DEFINITION_ZONE_ERROR
                    # when evidence strongly suggests an interface/API mismatch.
                    #
                    # Gate A: blocked_sorry + interface-like primary error.
                    # When ALL source sorrys are blocked (none compile-clean) and the
                    # primary error message looks like an API/signature problem, skip
                    # the local self-fix loop and go straight to Agent7/Agent2 analysis.
                    _conservative_override_reason: str = ""
                    if (
                        _conservative_blocked_escalate
                        and error_type in ("LOCAL_PROOF_ERROR", "PROOF_ERROR")
                        and last_verify_result is not None
                        and int(last_verify_result.get("blocked_sorry_count", 0)) > 0
                        and _structured_errors_inner
                    ):
                        _primary_msg_A = str(_structured_errors_inner[0].get("message", ""))
                        _is_iface_A = bool(
                            _UNKNOWN_SYMBOL_RE.search(_primary_msg_A)
                            or _TYPE_MISMATCH_RE.search(_primary_msg_A)
                            or _FIELD_NOTATION_RE.search(_primary_msg_A)
                        )
                        if _is_iface_A:
                            error_type = "DEFINITION_ZONE_ERROR"
                            _conservative_override_reason = (
                                f"blocked_sorry={last_verify_result['blocked_sorry_count']} "
                                f"+ interface error: {_primary_msg_A[:80]}"
                            )

                    # Gate B: same interface-like error signature repeated too many times.
                    # Counts consecutive turns where the primary error is interface-like
                    # AND the (file:line:msg-prefix) signature hasn't changed.  Escalate
                    # after CONSERVATIVE_INTERFACE_ERROR_REPEAT_THRESHOLD turns.
                    if (
                        not _conservative_override_reason
                        and error_type in ("LOCAL_PROOF_ERROR", "PROOF_ERROR")
                        and _structured_errors_inner
                    ):
                        _primary_msg_B = str(_structured_errors_inner[0].get("message", ""))
                        _is_iface_B = bool(
                            _UNKNOWN_SYMBOL_RE.search(_primary_msg_B)
                            or _TYPE_MISMATCH_RE.search(_primary_msg_B)
                            or _FIELD_NOTATION_RE.search(_primary_msg_B)
                        )
                        if _is_iface_B:
                            _iface_sig_now = (
                                f"{_structured_errors_inner[0].get('file', '')}:"
                                f"{_structured_errors_inner[0].get('line', 0)}:"
                                f"{_primary_msg_B[:80]}"
                            )
                            if _iface_sig_now == _conservative_iface_sig:
                                _conservative_iface_repeat_count += 1
                            else:
                                _conservative_iface_sig = _iface_sig_now
                                _conservative_iface_repeat_count = 1
                            if _conservative_iface_repeat_count >= _conservative_iface_repeat_threshold:
                                error_type = "DEFINITION_ZONE_ERROR"
                                _conservative_override_reason = (
                                    f"interface error repeated {_conservative_iface_repeat_count}x: "
                                    f"{_primary_msg_B[:80]}"
                                )
                        else:
                            # Non-interface error: reset the interface repeat counter.
                            _conservative_iface_sig = ""
                            _conservative_iface_repeat_count = 0

                    # Log conservative override so operators can see why routing changed.
                    if _conservative_override_reason:
                        console.print(
                            f"  [ConservativeOverride] {error_type} ← "
                            f"{_conservative_override_reason}"
                        )
                    # ---- End conservative routing override gates ----

                    if error_type == "SIGNATURE_HALLUCINATION":
                        console.print(
                            f"  [Agent3] attempt {attempt}/{max_retries} — "
                            "[red]SIGNATURE_HALLUCINATION detected"
                        )
                        execution_history.extend(exec_results)
                        # Restore checkpoint if one exists; otherwise wipe.
                        # Note: do NOT gate on sorry_count < _initial_sorry_for_ckpt —
                        # that condition fails when the run started from a sorry=0 file,
                        # causing the checkpoint to be skipped and the file deleted.
                        if best_checkpoint["content"] is not None:
                            registry.call("overwrite_file", path=target_file, content=best_checkpoint["content"])
                            initial_hash = _file_hash(target_file)
                            initial_exists = True
                            file_changed = True
                            # Restore any Glue files Agent3 may have corrupted.
                            for _gp, _goriginal in _glue_snapshot.items():
                                _gp_rel = str(_gp.relative_to(PROJECT_ROOT))
                                if snapshot_file(_gp_rel) != _goriginal:
                                    registry.call("overwrite_file", path=_gp_rel, content=_goriginal)
                                    console.print(f"  [Glue] Restored {_gp.name} (SIGNATURE_HALLUCINATION rollback)")
                            # Restore any Layer0 files Agent3 may have corrupted.
                            for _lp, _loriginal in _layer0_snapshot.items():
                                _lp_rel = str(_lp.relative_to(PROJECT_ROOT))
                                if snapshot_file(_lp_rel) != _loriginal:
                                    registry.call("overwrite_file", path=_lp_rel, content=_loriginal)
                                    console.print(f"  [Layer0] Restored {_lp.name} (SIGNATURE_HALLUCINATION rollback)")
                            console.print(
                                f"  [Checkpoint] Restored (sorry={best_checkpoint['sorry_count']}) "
                                "instead of full wipe"
                            )
                        else:
                            # No checkpoint — delete the broken file and re-scaffold.
                            if _tgt.exists():
                                _tgt.unlink()
                            initial_exists = False
                            initial_hash = None
                            file_changed = False
                            # Re-run Phase 3a scaffold so Agent3 has a clean compilable base.
                            _halluc_scaffold_registry = ToolRegistry()
                            _halluc_scaffold_registry.register_scaffold_tools()
                            _halluc_err_ctx = (
                                f"[STATEMENT ERROR — SIGNATURE HALLUCINATION]\n"
                                f"Lean error excerpt:\n```\n"
                                f"{_prioritize_error_text(_structured_errors_inner, last_verify_text, _inner_err_line, target_file, max_chars=800)}"
                                f"\n```\n\n"
                                "The theorem STATEMENT itself is broken: it references a symbol "
                                "that does not exist in Lean or Lib/.\n"
                                "CONSTRAINT (non-negotiable — Principle A):\n"
                                "Use ONLY mathematical primitives in the new theorem signature.\n"
                                "Do NOT invent any new abstract type, set constructor, or class name —\n"
                                "including any name resembling the one that just failed.\n"
                                "Express every property as a direct inequality, ∀/∃ quantifier,\n"
                                "or inner-product expression (e.g. ∀ y, f y ≥ f x + ⟪g, y-x⟫_ℝ).\n\n"
                                "Rewrite the scaffold from scratch with all statements fixed.\n"
                            )
                            guidance, _ = _call_agent2_with_tools(
                                agent2,
                                escalation_registry,
                                _halluc_err_ctx + "Provide updated strategy for the re-scaffold.",
                            )
                            _scaffold_ok_h = _call_agent2_scaffold(
                                agent2,
                                _halluc_scaffold_registry,
                                target_file,
                                guidance,
                                algo_name=_algo_name,
                            )
                            if _scaffold_ok_h:
                                initial_exists = True
                                initial_hash = _file_hash(target_file)
                                best_checkpoint["content"] = load_file(target_file)
                                best_checkpoint["sorry_count"] = int(
                                    registry.call("run_lean_verify", target_file).get("sorry_count", 999)
                                )
                            else:
                                console.print(
                                    "[red][SIGNATURE_HALLUCINATION] Re-scaffold also failed — continuing."
                                )
                        _inner_break_reason = "hallucination"
                        _break_attempt = True
                        break  # start next attempt with fresh guidance

                    if error_type == "DEFINITION_ZONE_ERROR":
                        _def_zone_err_count += 1
                        result_msg = (
                            f"## DEFINITION ZONE ERROR [{_def_zone_err_count}/{_def_zone_force_threshold}]\n"
                            "Type mismatch occurs in declaration/definition zone (before proof tactics).\n"
                            "This usually means a called function is being applied with the wrong signature.\n"
                            f"After the FIRST failed local fix you MUST call request_agent7_interface_audit "
                            f"(forced at {_def_zone_force_threshold} consecutive definition-zone errors).\n\n"
                        ) + result_msg
                        error_type = "LOCAL_PROOF_ERROR"

                    if error_type == "LOCAL_PROOF_ERROR":
                        console.print(
                            f"  [Agent3] attempt {attempt}/{max_retries} — "
                            f"[yellow]LOCAL_PROOF_ERROR at line {line_no_display} "
                            f"(turn {tool_turn + 1}) — Agent3 continues self-fix"
                        )
                        # Build error signature for repeat detection (pass previous to detector)
                        _primary_local = _structured_errors_inner[0] if _structured_errors_inner else {}
                        _err_sig = (
                            f"{_primary_local.get('file', '')}:{_primary_local.get('line', 0)}:"
                            f"{str(_primary_local.get('message', ''))[:200]}"
                        )
                        # System-driven Agent6 auto-route: infra gap detected and need to solve now.
                        # When AGENT6_AUTO_ROUTE_ENABLED is False, Agent6 is invoked only when
                        # Agent7's protocol explicitly indicates a missing glue lemma.
                        should_route, infra_diag = _should_route_to_agent6_for_infra(
                            last_verify_text,
                            target_file,
                            _structured_errors_inner,
                            tool_turn,
                            _last_local_error_sig,
                        )
                        _last_local_error_sig = _err_sig
                        # Inject known identifier correction hint before escalation.
                        _unknown_ident_re = re.compile(
                            r"unknown (?:identifier|constant)[^`]*`([a-zA-Z][a-zA-Z0-9_.]*)`",
                            re.IGNORECASE,
                        )
                        for _um in _unknown_ident_re.finditer(last_verify_text):
                            _ident = _um.group(1)
                            if _ident in UNKNOWN_IDENTIFIER_RENAME_MAP:
                                _correct = UNKNOWN_IDENTIFIER_RENAME_MAP[_ident]
                                result_msg = (
                                    f"## Known identifier correction\n"
                                    f"Use `{_correct}` instead of `{_ident}`. Apply via edit_file_patch.\n\n"
                                ) + result_msg
                                break
                        max_agent6 = RETRY_LIMITS.get("MAX_AGENT6_ESCALATIONS_PER_ATTEMPT", 1)
                        if should_route and AGENT6_AUTO_ROUTE_ENABLED:
                            _line_int = int(err_line_no) if err_line_no is not None else 1
                            try:
                                g = registry.call("get_lean_goal", file_path=target_file, sorry_line=_line_int)
                                goal = (g.get("goal") or g.get("raw") or "").strip()
                                hypotheses = g.get("hypotheses")
                                if not isinstance(hypotheses, list):
                                    hypotheses = []
                            except Exception:
                                goal = ""
                                hypotheses = []
                            if goal:
                                _candidate_escalation = _agent6_escalation_count + 1
                                if _candidate_escalation > max_agent6:
                                    # exhausted Agent6 budget in this attempt
                                    goal = ""
                                _current_goal_sig = hashlib.md5(goal[:1000].encode("utf-8")).hexdigest()
                                if _candidate_escalation == 2:
                                    _same_goal_ok = (not _agent6_second_require_same_goal) or (
                                        _agent6_first_goal_sig is not None and _current_goal_sig == _agent6_first_goal_sig
                                    )
                                    _progress_ok = _agent6_first_progress_ok
                                    if not (_same_goal_ok and _progress_ok):
                                        goal = ""
                                if not goal:
                                    continue
                                _agent6_escalation_count = _candidate_escalation
                                console.print(
                                    f"  [System→Agent6] Auto-route #{_agent6_escalation_count} at turn "
                                    f"{tool_turn + 1}: infra gap detected — {infra_diag}"
                                )
                                _pre_agent6_sorry = last_sorry_in_attempt
                                success, agent6_msg = _run_agent6_glue_loop(
                                    agent6,
                                    agent6_registry,
                                    target_file,
                                    goal,
                                    str(_primary_local.get("message", ""))[:600],
                                    infra_diag,
                                    _algo_name,
                                    hypotheses=hypotheses,
                                    stuck_line=_line_int,
                                )
                                if success:
                                    exec_results.append(ExecutionResult(
                                        status_code="SUCCESS",
                                        message=f"Agent6 auto-route: succeeded (turn {tool_turn + 1})",
                                        attempt=attempt,
                                    ))
                                    _target_verify_after_agent6 = registry.call("run_lean_verify", target_file)
                                    _tv_exit = int(_target_verify_after_agent6.get("exit_code", 1))
                                    _tv_sorry = int(_target_verify_after_agent6.get("sorry_count", 0))
                                    _tv_errors = _target_verify_after_agent6.get("errors", [])
                                    _tv_error_text = (
                                        "\n".join(_tv_errors[:5]) if isinstance(_tv_errors, list) else str(_tv_errors)
                                    )
                                    _progress_delta = max(0, _pre_agent6_sorry - _tv_sorry)
                                    if _candidate_escalation == 1:
                                        _agent6_first_goal_sig = _current_goal_sig
                                        _agent6_first_progress_ok = _progress_delta >= _agent6_second_min_progress
                                    result_msg = (
                                        "## System routed to Agent6 (infra gap detected).\n"
                                        f"{agent6_msg}\n\n"
                                        "## Target regression verify after Agent6\n"
                                        f"exit_code: {_tv_exit} | sorry_count: {_tv_sorry}\n"
                                        + (
                                            f"Top errors:\n```\n{_tv_error_text[:1200]}\n```\n\n"
                                            if _tv_error_text else "\n"
                                        )
                                        + "Original verify result:\n" + result_msg
                                    )
                                else:
                                    _current_snippet = _build_escalation_file_context(target_file, _line_int)
                                    new_guidance, _ = _call_agent2_with_tools(
                                        agent2,
                                        escalation_registry,
                                        f"[AGENT6 AUTO-ROUTE FALLBACK — Agent6 could not prove helper lemma]\n"
                                        f"System detected infra gap: {infra_diag}\n\n"
                                        f"Error: {_primary_local.get('message', '')}\n\n"
                                        f"Target: {target_file} line {err_line_no}. Goal: {goal[:500]}...\n\n"
                                        f"=== CURRENT FILE ({target_file}) ===\n```lean\n{_current_snippet}\n```\n\n"
                                        f"Provide revised guidance. Agent3 continues in the SAME attempt.",
                                    )
                                    result_msg = (
                                        "## System routed to Agent6 — Agent6 could not fill glue. Agent2 guidance:\n"
                                        f"{new_guidance}\n\n"
                                        "Apply this guidance now. Original verify result:\n" + result_msg
                                    )
                        if _stale_err_count >= 3:
                            result_msg = result_msg + "\n\n" + _build_stale_error_hint(
                                registry,
                                target_file,
                                last_verify_text,
                                err_line_no,
                                _stale_err_count,
                            )
                        _stuck_now = (
                            (
                                _stale_err_count >= _agent7_force_stale_threshold
                                and _agent7_no_progress_turns >= _agent7_force_no_progress_turns_threshold
                            )
                            or _def_zone_err_count >= _def_zone_force_threshold
                        )
                        _reason = (
                            f"stale_line_count={_stale_err_count}, "
                            f"no_progress_turns={_agent7_no_progress_turns}, "
                            f"def_zone_err_count={_def_zone_err_count}, "
                            f"line={line_no_display}"
                        )
                        if _stuck_now and not _agent7_soft_warned:
                            _agent7_soft_warned = True
                            _agent7_force_warn_turn = tool_turn + 1
                            agent7_force_gate_reason_samples.append(_reason)
                            exec_results.append(ExecutionResult(
                                status_code="BLOCKED",
                                message=f"AGENT7_FORCE_WARNING {_reason}",
                                attempt=attempt,
                            ))
                            raw_reply = agent3.call(
                                "## AGENT7_FORCE_WARNING\n"
                                "Repeated structural/type mismatch with no progress detected.\n"
                                "Next action SHOULD be request_agent7_interface_audit.\n"
                                "If stuck persists, FORCE_GATE_ACTIVE will be enabled."
                            )
                            token_char_budget += len(raw_reply)
                            continue
                        if (
                            _stuck_now
                            and _agent7_soft_warned
                            and (not _agent7_force_gate_active)
                            and _agent7_force_warn_turn is not None
                            and (tool_turn + 1 - _agent7_force_warn_turn) >= _agent7_force_after_soft_warn
                        ):
                            _agent7_force_gate_active = True
                            _def_zone_err_count = 0
                            agent7_forced_trigger_count += 1
                            agent7_force_gate_entries.append({
                                "attempt": attempt,
                                "turn": tool_turn + 1,
                                "reason": _reason,
                            })
                            exec_results.append(ExecutionResult(
                                status_code="BLOCKED",
                                message=f"AGENT7_FORCE_GATE_ON {_reason}",
                                attempt=attempt,
                            ))
                            raw_reply = agent3.call(
                                "## FORCE_GATE_ACTIVE\n"
                                "You are stuck on repeated structural/type mismatch errors.\n"
                                "You must call request_agent7_interface_audit now (or request_agent2_help as fallback)."
                            )
                            token_char_budget += len(raw_reply)
                            continue

                    if error_type == "DEPENDENCY_COMPILE_ERROR":
                        # Errors originate from a dependency/import file, not target.
                        # Do NOT rewrite target — route to dependency fix via Agent2.
                        _dep_only = [
                            e for e in _structured_errors_inner
                            if not _is_target_file_error(e["file"], target_file)
                        ]
                        _dep_errors_text = (
                            _prioritize_error_text(_dep_only, last_verify_text, _inner_err_line, target_file, max_chars=1200)
                            if _dep_only else last_verify_text[:800]
                        )
                        console.print(
                            f"  [Agent3] attempt {attempt}/{max_retries} — "
                            "[cyan]DEPENDENCY_COMPILE_ERROR — routing to dep-fix via Agent2"
                        )
                        execution_history.extend(exec_results)
                        _attempt_failures_current = [
                            a for a in attempt_failures if a.get("attempt") == attempt
                        ]
                        _attempt_diag = _generate_attempt_diagnosis(
                            attempt,
                            _attempt_failures_current,
                            _tools_used_this_attempt,
                            registry,
                            target_file,
                        )
                        guidance, _ = _call_agent2_with_tools(
                            agent2,
                            escalation_registry,
                            _attempt_diag
                            +
                            f"[DEPENDENCY COMPILE ERROR — IMPORT FILE BROKEN]\n"
                            f"Errors are in a dependency file, NOT in {target_file}.\n\n"
                            f"Failing dependency errors:\n```\n{_dep_errors_text}\n```\n\n"
                            f"Target file ({target_file}) is NOT the source of errors — "
                            "do NOT rewrite or delete the target.\n\n"
                            "REQUIRED ACTION:\n"
                            "1. search_codebase to find the correct Lean 4 / Mathlib API names "
                            "for any unknown identifiers.\n"
                            "2. Use edit_file_patch to fix the dependency file directly.\n"
                            "3. Output a PATCH block (<<<SEARCH>>>/<<<REPLACE>>>) with the "
                            "exact fix. Reference verified API names only.",
                        )
                        _inner_break_reason = "dep_compile_error"
                        _break_attempt = True
                        break  # start next attempt with dep-fix guidance

                # Return tool result to Agent3 for next decision
                raw_reply = agent3.call(result_msg)
                token_char_budget += len(raw_reply)

            else:
                # for-loop completed without break: turn limit exhausted
                console.print(
                    f"  [Agent3] attempt {attempt}/{max_retries} — "
                    f"turn limit ({max_tool_turns}) reached without success"
                )
                _inner_break_reason = "turn_limit"
                # Force a final verify if no verify was done this attempt
                if last_verify_result is None:
                    final_verify = registry.call("run_lean_verify", target_file)
                    last_exit_code = int(final_verify.get("exit_code", 1))
                    last_sorry_in_attempt = int(final_verify.get("sorry_count", 0))
                    verify_errors = final_verify.get("errors", [])
                    last_verify_text = (
                        "\n".join(verify_errors)
                        if isinstance(verify_errors, list) else str(verify_errors)
                    )
                    last_sorry_count = last_sorry_in_attempt
                    last_errors = last_verify_text
                    if (
                        last_exit_code == 0
                        and
                        last_sorry_in_attempt < best_checkpoint["sorry_count"]
                        and _target_exists_overlay()
                    ):
                        best_checkpoint = {
                            "sorry_count": last_sorry_in_attempt,
                            "content": load_file(target_file),
                        }
                        console.print(
                            f"  [Checkpoint] Updated at turn limit: sorry={last_sorry_in_attempt}"
                        )


            # Per-sorry iteration outcome: mark sorry as closed or skipped.
            if _active_sorry_line is not None:
                _sorry_status[_active_sorry_line] = (
                    "closed" if _active_sorry_closed else "skipped"
                )
                # PerSorrySkip log: only emit when not closed.
                if not _active_sorry_closed and progress_detail != "compact":
                    _skip_reason = _inner_break_reason or "turn_limit"
                    console.print(
                        f"  [PerSorrySkip] a{attempt} line={_active_sorry_line} "
                        f"reason={_skip_reason} turns_used={_turns_this_sorry}"
                    )
            # Exit=1 invariant guard: if the file is broken at the end of this
            # sorry iteration, restore the best checkpoint immediately so the
            # next turn never starts from a non-compiling state.
            # Exception: if the active sorry was just closed this iteration,
            # the proof structure is complete but may have residual syntax/type
            # errors. Do NOT restore — let Agent3 fix those in the next
            # per-sorry iteration rather than discarding the nearly-done proof.
            if (
                last_exit_code == 1
                and best_checkpoint["content"] is not None
                and not _active_sorry_closed
            ):
                registry.call(
                    "overwrite_file", path=target_file,
                    content=best_checkpoint["content"],
                )
                last_sorry_in_attempt = int(best_checkpoint["sorry_count"])
                last_sorry_count = last_sorry_in_attempt
                _restore_result = registry.call("run_lean_verify", target_file)
                last_exit_code = 0 if _restore_result["success"] else 1
                last_errors = "\n".join(_restore_result.get("errors", []))
                console.print(
                    f"  [InvariantRestore] exit=1 at sorry boundary — "
                    f"restored checkpoint (sorry={best_checkpoint['sorry_count']})"
                    f" → re-verify exit={last_exit_code}"
                )

            if _break_attempt:
                _inner_break_reason = _inner_break_reason or "break_attempt"
                break  # exit the per-sorry loop early

        # ---------------------------------------------------------------
        # End of per-sorry loop — round-level Agent2 replan
        # If any sorries remain unresolved, ask Agent2 for updated strategy
        # before the next attempt begins.
        # ---------------------------------------------------------------
        _skipped_sorry_lines = [
            ln for ln, s in _sorry_status.items()
            if s != "closed" and ln is not None
        ]
        if (
            _skipped_sorry_lines
            and attempt < max_retries
            and _inner_break_reason not in ("dep_compile_error", "hallucination", "json_error")
        ):
            # Build a full error history summary (last 8 failures) so Agent2 sees the
            # complete picture of what has been tried, not just the last verify output.
            _replan_failure_summary = "\n".join(
                f"  a{f['attempt']} L{f.get('line', '?')}: {str(f.get('message', ''))[:100]}"
                for f in attempt_failures[-8:]
            ) or "  (none recorded)"
            _round_replan_prompt = (
                f"[ROUND REPLAN — Per-Sorry Pass {attempt} Complete]\n"
                f"Closed: {[ln for ln, s in _sorry_status.items() if s == 'closed']}\n"
                f"Skipped (unresolved): {_skipped_sorry_lines}\n\n"
                f"## Full error history (last 8 failures)\n{_replan_failure_summary}\n\n"
                f"## Latest verify errors\n```\n{last_verify_text[:1200]}\n```\n\n"
                f"=== CURRENT FILE ({target_file}) ===\n"
                f"```lean\n"
                + (load_file(target_file)[:8000] if _target_exists_overlay() else "(no file)")
                + "\n```\n\n"
                "Provide updated proof strategy for the unresolved sorry lines. "
                "Apply your Sorry-Fill Proof Path Protocol. "
                "If a Level-2 missing helper lemma is needed, add it directly in the target file before the main theorem.\n\n"
                "## ROUTING DECISION REQUIRED\n"
                "End your response with a ROUTE_DECISION JSON block indicating which agent "
                "should handle the next attempt:\n"
                "  ROUTE_DECISION: {\"route_to\": \"agent3\"|\"agent7\"|\"agent7_then_agent6\"|\"self\", "
                "\"confidence\": 0.0-1.0, \"reason\": \"...\", \"agent7_hint\": \"...\"}\n"
                "Choose agent7 when the error is an API/signature/typeclass mismatch. "
                "Choose agent7_then_agent6 when a new glue lemma is also needed. "
                "Choose self when the proof strategy needs fundamental revision. "
                "Choose agent3 for tactical tactic fixes.\n"
            )
            console.print(
                f"  [RoundReplan] attempt {attempt} — "
                f"{len(_skipped_sorry_lines)} unresolved: "
                + ", ".join(f"line {ln}" for ln in _skipped_sorry_lines)
            )
            guidance, _a2_route_replan = _call_agent2_with_tools(
                agent2, escalation_registry, _round_replan_prompt
            )

            # Execute Agent2's routing decision for the NEXT attempt.
            _final_route_replan = _apply_agent2_route(
                _a2_route_replan, _routing_budget, _err_sig, _route_repeat_tracker
            )
            if _final_route_replan in ("agent7", "agent7_then_agent6"):
                _routing_budget["preemptive_agent7"] = _routing_budget.get("preemptive_agent7", 0) + 1
                _a7_hint_replan = (_a2_route_replan or {}).get("agent7_hint", "")
                _a7_prompt_replan = _build_preemptive_agent7_prompt(
                    _a7_hint_replan, target_file, last_verify_text, agent7_registry
                )
                agent7.messages.clear()
                _a7_plan_replan, _ = _call_agent7_with_tools(agent7, agent7_registry, _a7_prompt_replan)
                if _a7_plan_replan:
                    _pending_agent7_plan = _a7_plan_replan
                    console.print(
                        f"  [A2Router→Agent7] Replan preemptive Agent7 triggered "
                        f"(confidence={(_a2_route_replan or {}).get('confidence', '?')})"
                    )
                if _final_route_replan == "agent7_then_agent6":
                    _ft_replan = (_a7_plan_replan or {}).get("fallback_trigger", {}) if _a7_plan_replan else {}
                    if str(_ft_replan.get("route_to", "")).lower() == "agent6":
                        console.print("  [A2Router→Agent7→Agent6] agent6_approved for next attempt")
            elif _final_route_replan == "self":
                _routing_budget["self_revisions"] = _routing_budget.get("self_revisions", 0) + 1
                _self_msg_replan = (
                    "[SELF_REVISION] Your current proof strategy has low confidence. "
                    "Revise the overall proof approach fundamentally. Do NOT reuse the same tactics.\n\n"
                    + guidance
                )
                guidance, _ = _call_agent2_with_tools(agent2, escalation_registry, _self_msg_replan)
                console.print("  [A2Router→Self] Agent2 self-revision triggered (replan)")

        # ---------------------------------------------------------------
        # Attempt summary panel (normal: one compact line; debug: Panel)
        # ---------------------------------------------------------------
        _closed_ln  = [ln for ln, s in _sorry_status.items() if s == "closed"  and ln is not None]
        _skipped_ln = [ln for ln, s in _sorry_status.items() if s == "skipped" and ln is not None]
        _pending_ln = [ln for ln, s in _sorry_status.items() if s == "pending" and ln is not None]
        _a7_this_attempt = sum(
            1 for inv in agent7_invocations if inv.get("attempt") == attempt
        )
        if progress_detail == "normal":
            _closed_str  = ",".join(str(l) for l in _closed_ln)  or "—"
            _skipped_str = ",".join(str(l) for l in _skipped_ln) or "—"
            _sum_src = last_sorry_in_attempt
            _sum_cln = last_verify_result.get("sorry_declarations", _sum_src) if last_verify_result else _sum_src
            _sum_blk = last_verify_result.get("blocked_sorry_count", 0)       if last_verify_result else 0
            _sum_sorry_display = (
                f"sorry={_sum_src} ({_sum_cln} clean, {_sum_blk} blocked)"
                if _sum_blk > 0 else f"sorry={_sum_src}"
            )
            console.print(
                f"  [AttemptSummary] a{attempt}/{max_retries} "
                f"turns={_total_turns_this_attempt} "
                f"exit={last_exit_code} {_sum_sorry_display} | "
                f"closed=[{_closed_str}] skipped=[{_skipped_str}] "
                f"esc=A2:{_attempt_esc_a2}/A6:{_attempt_esc_a6}/A7:{_attempt_esc_a7}"
            )
        elif progress_detail == "debug":
            _summary_lines = [
                f"attempt:   {attempt}/{max_retries}",
                f"turns:     {_total_turns_this_attempt}/{max_tool_turns}",
                f"exit/sorry:{last_exit_code}/{last_sorry_in_attempt}",
                f"closed:    {_closed_ln}",
                f"skipped:   {_skipped_ln}",
                f"pending:   {_pending_ln}",
                f"escalations: A2={_attempt_esc_a2}  A6={_attempt_esc_a6}  A7={_attempt_esc_a7}",
                f"break_reason: {_inner_break_reason or 'none'}",
            ]
            console.print(Panel("\n".join(_summary_lines), title=f"[yellow]Attempt {attempt} Summary"))

        execution_history.extend(exec_results)

        # If inner loop broke due to hallucination or dep error, continue outer loop
        # (guidance already set by the break handler above)
        if _inner_break_reason in ("hallucination", "dep_compile_error"):
            continue

        _attempt_failures_current = [
            a for a in attempt_failures if a.get("attempt") == attempt
        ]
        _attempt_diag = _generate_attempt_diagnosis(
            attempt,
            _attempt_failures_current,
            _tools_used_this_attempt,
            registry,
            target_file,
        )

        # Classify the final error state for this attempt
        error_type_final, _structured_errors_final = (
            _classify_lean_error_structured(last_verify_text, target_file)
            if last_verify_text else ("PROOF_ERROR", [])
        )
        err_line_no_final = _extract_first_error_line(last_verify_text)
        line_no_display_final = str(err_line_no_final) if err_line_no_final is not None else "unknown"
        # Precompute int version of final error line for _build_escalation_file_context
        _err_line_int = int(line_no_display_final) if line_no_display_final.isdigit() else None

        current_code = (
            load_file(target_file)
            if _target_exists_overlay()
            else "(Agent3 has not created the file yet.)"
        )

        current_hash_end = _file_hash(target_file)
        attempt_file_changed = _target_exists_overlay() and (current_hash_end != attempt_start_hash)

        # No-op trap: file unchanged regardless of build status.
        # NOTE: DEPENDENCY_COMPILE_ERROR is excluded — when a dependency is broken
        # Agent3 correctly leaves the target file untouched; falling through to
        # the dep-error handler below is the right behaviour.
        if not attempt_file_changed and _target_exists_overlay():
            if error_type_final == "DEPENDENCY_COMPILE_ERROR":
                pass  # dep handler below will deal with it
            elif last_exit_code == 0 and last_sorry_in_attempt == 0:
                # File was already clean at attempt start — break to success gate.
                console.print(
                    f"  [Agent3] attempt {attempt}/{max_retries} — "
                    "build=OK, sorry=0, file unchanged — target already met."
                )
                break
            else:
                _noop_ctx = (
                    f"Attempt {attempt} NOOP — Agent3 made NO changes to {target_file}.\n"
                    f"Build exit code: {last_exit_code} | Sorry count: {last_sorry_in_attempt}\n"
                    f"Last error: {last_verify_text[:300]}\n\n"
                    "SURGEON MODE: Agent3 must change the file. Output a PATCH block "
                    "(<<<SEARCH>>>/<<<REPLACE>>>) with the exact Lean code to apply. "
                    "Be specific — no natural language, no explanation without a patch."
                )
                guidance, _a2_route_noop = _call_agent2_with_tools(agent2, escalation_registry, _noop_ctx)
                console.print(
                    f"  [Agent3] attempt {attempt}/{max_retries} — "
                    f"build={last_exit_code} (file UNCHANGED — NOOP forced)"
                )
                # ---- Agent2 Router: execute routing decision for NOOP ----
                _final_route_noop = _apply_agent2_route(
                    _a2_route_noop, _routing_budget, _err_sig, _route_repeat_tracker
                )
                if _final_route_noop in ("agent7", "agent7_then_agent6"):
                    _routing_budget["preemptive_agent7"] = _routing_budget.get("preemptive_agent7", 0) + 1
                    _a7_hint_noop = (_a2_route_noop or {}).get("agent7_hint", "")
                    _a7_prompt_noop = _build_preemptive_agent7_prompt(
                        _a7_hint_noop, target_file, last_verify_text, agent7_registry
                    )
                    agent7.messages.clear()
                    _a7_plan_noop, _ = _call_agent7_with_tools(agent7, agent7_registry, _a7_prompt_noop)
                    if _a7_plan_noop:
                        _active_agent7_plan = _a7_plan_noop
                        _agent7_current_step_idx = 0
                        _agent7_invocations_this_attempt += 1
                        console.print(
                            f"  [A2Router\u2192Agent7] Preemptive Agent7 triggered by NOOP route "
                            f"(confidence={(_a2_route_noop or {}).get('confidence', '?')})"
                        )
                    if _final_route_noop == "agent7_then_agent6":
                        _ft_noop = (_a7_plan_noop or {}).get("fallback_trigger", {}) if _a7_plan_noop else {}
                        _agent7_approved_agent6 = str(_ft_noop.get("route_to", "")).lower() == "agent6"
                        console.print(f"  [A2Router\u2192Agent7\u2192Agent6] agent6_approved={_agent7_approved_agent6}")
                elif _final_route_noop == "self":
                    _routing_budget["self_revisions"] = _routing_budget.get("self_revisions", 0) + 1
                    _self_msg_noop = (
                        "[SELF_REVISION] Your current proof strategy has low confidence. "
                        "Revise the overall proof approach fundamentally. Do NOT reuse the same tactics.\n\n"
                        + guidance
                    )
                    guidance, _ = _call_agent2_with_tools(agent2, escalation_registry, _self_msg_noop)
                    console.print("  [A2Router\u2192Self] Agent2 self-revision triggered (NOOP)")
                continue

        # DEPENDENCY_COMPILE_ERROR: dep broken — fix dep file directly, never rewrite target
        if error_type_final == "DEPENDENCY_COMPILE_ERROR":
            _dep_only_final = [
                e for e in _structured_errors_final
                if not _is_target_file_error(e["file"], target_file)
            ]
            _dep_errors_final = (
                _prioritize_error_text(_dep_only_final, last_verify_text, _err_line_int, target_file, max_chars=1200)
                if _dep_only_final else last_verify_text[:800]
            )
            console.print(
                f"  [Agent3] attempt {attempt}/{max_retries} — "
                "[cyan]DEPENDENCY_COMPILE_ERROR (post-attempt) — routing to dep-fix"
            )
            # Track dep-error streak for loop-guard.
            _dep_sig_now = hashlib.md5(_dep_errors_final[:200].encode()).hexdigest()[:16]
            if _dep_sig_now == _last_dep_error_sig:
                _dep_error_streak += 1
            else:
                _dep_error_streak = 0
            _last_dep_error_sig = _dep_sig_now
            _ref_files_dep = _get_reference_files_with_descriptions(target_file)
            _ref_class_dep = _format_ref_and_classification_blocks(
                _ref_files_dep, None
            )
            guidance, _ = _call_agent2_with_tools(
                agent2,
                escalation_registry,
                _attempt_diag
                + _format_failed_approaches(_failed_approaches[-5:])
                + (
                    f"[DEP-ERROR STREAK: {_dep_error_streak} consecutive identical dep errors]\n"
                    "You MUST change your approach — previous fixes did not work.\n\n"
                    if _dep_error_streak >= 2 else ""
                )
                + f"[DEPENDENCY COMPILE ERROR — ATTEMPT {attempt} FAILED]\n"
                f"Errors are in a dependency file, NOT in {target_file}.\n\n"
                f"Dependency errors:\n```\n{_dep_errors_final}\n```\n\n"
                "Do NOT rewrite or delete the target file.\n\n"
                "REQUIRED:\n"
                "1. search_codebase to find the correct Lean 4 / Mathlib API for each "
                "unknown identifier shown above.\n"
                "2. Fix the dependency file directly using edit_file_patch.\n"
                "3. Output a PATCH block (<<<SEARCH>>>/<<<REPLACE>>>) with exact correct API.\n"
                "Use only API names you have verified via search_codebase."
                + _ref_class_dep,
            )
            continue

        # Pre-query sorry goals once per attempt-failure, reuse across all Agent2 paths.
        _pre_agent2_goals = _prequery_sorry_goals(
            registry,
            target_file,
            "",
            _goal_cache,
            errors_text=last_verify_text,
        )
        _classification_request = (
            "\n\n## SORRY CLASSIFICATION REQUIRED\n"
            "For each sorry listed in the goal states above, output a classification block:\n"
            "```\n"
            "## SORRY CLASSIFICATION\n"
            "- Line N: STRUCTURAL_GLUE — <reason: a new bridge/glue lemma must be proved>\n"
            "  dependency_symbols: [\"lemmaA\"]\n"
            "  diagnosis: \"<what lemma is missing and why it cannot be proved locally>\"\n"
            "- Line M: STRUCTURAL_INTERFACE — <reason: API/signature/interface mismatch>\n"
            "  dependency_symbols: [\"wrongName\"]\n"
            "  diagnosis: \"<what interface fix is needed>\"\n"
            "- Line K: TACTICAL — <specific tactic or have-step to try>\n"
            "```\n"
            "STRUCTURAL_GLUE: goal requires a NEW lemma (not present in any imported Lib/ file) "
            "to be proved — e.g. a bridge between two process definitions, a measurability "
            "result for a custom function, an expectation bound for a specific algorithm step. "
            "Use when Agent6 (glue filler) must be invoked to prove a new helper lemma.\n"
            "STRUCTURAL_INTERFACE: goal fails because of a wrong API call, missing typeclass "
            "instance, wrong dot-notation, or function signature mismatch that is fixable "
            "WITHOUT proving a new lemma — just correcting the call site. "
            "Use when Agent7 (interface auditor) should be invoked.\n"
            "TACTICAL: ring / linarith / simp / exact / gcongr with existing hypotheses "
            "suffices — no new lemma or interface fix required.\n"
            + (_pre_agent2_goals or "")
        )

        # LOCAL_PROOF_ERROR: try sorry-degrade to keep the file compilable
        if error_type_final == "LOCAL_PROOF_ERROR":
            console.print(
                f"  [Agent3] attempt {attempt}/{max_retries} — "
                f"[yellow]LOCAL_PROOF_ERROR at line {line_no_display_final} — "
                "requesting sorry-degrade from Agent2"
            )
            err_summary_match = re.search(
                r"error:(.+)", last_verify_text, re.IGNORECASE | re.DOTALL
            )
            err_summary = (
                err_summary_match.group(1).strip()[:120].replace("\n", " ")
                if err_summary_match
                else last_verify_text[:120].replace("\n", " ")
            )
            _escalation_file_ctx = _build_escalation_file_context(target_file, _err_line_int)
            _primary_local = _structured_errors_final[0] if _structured_errors_final else None
            _ref_files_local = _get_reference_files_with_descriptions(target_file)
            _llm_class_local = (
                _llm_classify_error(_primary_local, _escalation_file_ctx, target_file)
                if _primary_local else None
            )
            _ref_class_local = _format_ref_and_classification_blocks(
                _ref_files_local, _llm_class_local
            )
            # Fetch the actual Lean goal state at the error line so Agent2 can
            # generate PATCH blocks with correctly-typed terms (no coercion guessing).
            _error_line_goal = _prequery_error_line_goal(
                escalation_registry, target_file, _err_line_int, _goal_cache
            )
            guidance, _a2_route_local = _call_agent2_with_tools(
                agent2,
                escalation_registry,
                _attempt_diag
                + _format_failed_approaches(_failed_approaches[-5:])
                + _ref_class_local
                + f"[LOCAL PROOF ERROR — DIAGNOSIS REQUIRED]\n"
                f"Build exit code: {last_exit_code} | Sorry count: {last_sorry_in_attempt}\n"
                f"Error at line {line_no_display_final}:\n```\n"
                f"{_prioritize_error_text(_structured_errors_final, last_verify_text, _err_line_int, target_file)}"
                f"\n```\n\n"
                + _error_line_goal
                + f"\n=== AGENT3'S CURRENT FILE ({target_file}) ===\n"
                f"```lean\n{_escalation_file_ctx}\n```\n\n"
                f"Agent3 used all {max_tool_turns} turns on line {line_no_display_final} "
                f"and could not fix the error.\n\n"
                f"DIAGNOSE FIRST — apply your Sorry-Fill Proof Path Protocol:\n\n"
                f"(A) STRUCTURAL error (type incompatibility, missing glue lemma, wrong proof\n"
                f"    approach that cannot be fixed by patching the current code):\n"
                f"    → Do NOT sorry-degrade. Provide a NEW proof strategy for the next attempt.\n"
                f"    → If a Level-2 helper lemma is missing, add it DIRECTLY in the target file\n"
                f"      before the main theorem using edit_file_patch (with sorry body).\n"
                f"    → Explain why the current approach fails at the type level.\n\n"
                f"(B) TACTICAL error (wrong tactic name, wrong lemma identifier, minor\n"
                f"    type mismatch fixable with a one-line rewrite):\n"
                f"    → Sorry-degrade line {line_no_display_final} using:\n"
                f"        sorry -- LOCAL_ERROR: {err_summary}\n"
                f"    → Provide the corrected tactic in your next-attempt guidance.\n\n"
                f"STATE YOUR CLASSIFICATION (A or B) EXPLICITLY before any patch or strategy.\n"
                f"PREFER the suggested_strategy from ERROR CLASSIFICATION above over A/B when present.\n"
                f"For add_instance: do NOT sorry-degrade; produce a PATCH that adds haveI/letI.\n\n"
                f"STRICT RULES (both cases):\n"
                f"1. Do NOT use write_new_file — the file must NOT be deleted or overwritten.\n"
                f"2. Use edit_file_patch with <<<SEARCH>>>/<<<REPLACE>>> for any patch.\n"
                f"3. SEARCH must be copied verbatim from the current file shown above.\n"
                f"4. For case A with a missing helper lemma: add it inline in the target file\n"
                f"   before the main theorem, then reference it in your guidance for Agent3.\n\n"
                + _retrieve_catalog_context(
                    _extract_new_identifiers_from_guidance(last_verify_text + "\n" + err_summary)
                )
                + _classification_request,
            )
            # ---- Agent2 Router: execute routing decision for LOCAL_PROOF_ERROR ----
            _final_route_local = _apply_agent2_route(
                _a2_route_local, _routing_budget, _err_sig, _route_repeat_tracker
            )
            if _final_route_local in ("agent7", "agent7_then_agent6"):
                _routing_budget["preemptive_agent7"] = _routing_budget.get("preemptive_agent7", 0) + 1
                _a7_hint_local = (_a2_route_local or {}).get("agent7_hint", "")
                _a7_prompt_local = _build_preemptive_agent7_prompt(
                    _a7_hint_local, target_file, last_verify_text, agent7_registry
                )
                agent7.messages.clear()
                _a7_plan_local, _ = _call_agent7_with_tools(agent7, agent7_registry, _a7_prompt_local)
                if _a7_plan_local:
                    _active_agent7_plan = _a7_plan_local
                    _agent7_current_step_idx = 0
                    _agent7_invocations_this_attempt += 1
                    console.print(
                        f"  [A2Router→Agent7] Preemptive Agent7 triggered by LOCAL_PROOF_ERROR route "
                        f"(confidence={(_a2_route_local or {}).get('confidence', '?')})"
                    )
                if _final_route_local == "agent7_then_agent6":
                    _ft_local = (_a7_plan_local or {}).get("fallback_trigger", {}) if _a7_plan_local else {}
                    _agent7_approved_agent6 = str(_ft_local.get("route_to", "")).lower() == "agent6"
                    console.print(f"  [A2Router→Agent7→Agent6] agent6_approved={_agent7_approved_agent6}")
            elif _final_route_local == "self":
                _routing_budget["self_revisions"] = _routing_budget.get("self_revisions", 0) + 1
                _self_msg_local = (
                    "[SELF_REVISION] Your current proof strategy has low confidence. "
                    "Revise the overall proof approach fundamentally. Do NOT reuse the same tactics.\n\n"
                    + guidance
                )
                guidance, _ = _call_agent2_with_tools(agent2, escalation_registry, _self_msg_local)
                console.print("  [A2Router→Self] Agent2 self-revision triggered (LOCAL_PROOF_ERROR)")
            continue

        # ---- Assumption-type shortcut (routing table: Todo 2) ----
        # If ALL unsolved goals in the error are assumption-shaped (Integrable,
        # Measurable, etc.) try a deterministic hypothesis patch BEFORE calling
        # Agent2.  This avoids burning an Agent2 LLM call on a mechanical fix.
        _unsolved_goals_now = extract_unsolved_goals(last_verify_text)
        if _unsolved_goals_now and all_goals_are_assumptions(_unsolved_goals_now):
            # Build a stable key for this error signature to avoid re-patching.
            _assm_err_key = hashlib.md5(
                (last_verify_text[:300]).encode()
            ).hexdigest()[:16]
            if _assm_err_key not in _assumption_patch_tried:
                _assumption_patch_tried.add(_assm_err_key)
                _auto_patches = goals_to_patch_list(_unsolved_goals_now, _tgt)
                if _auto_patches:
                    _n_auto = apply_assumption_patches(target_file, _auto_patches)
                    if _n_auto > 0:
                        console.print(
                            f"  [AssumptionRoute] Auto-patched {_n_auto} "
                            "missing assumption(s) — re-verifying."
                        )
                        _re_verify_assm = registry.call("run_lean_verify", target_file)
                        last_exit_code = int(_re_verify_assm.get("exit_code", 1))
                        last_sorry_in_attempt = int(_re_verify_assm.get("sorry_count", -1))
                        last_verify_text = str(_re_verify_assm.get("errors", ""))
                        if last_exit_code == 0 and last_sorry_in_attempt == 0:
                            # Full success — break to outer success gate
                            last_verify_result = _re_verify_assm
                            break
                        if last_exit_code == 0:
                            # Build clean but sorries remain — send Agent3 back in
                            guidance = (
                                f"[Auto-repair] Patched {_n_auto} missing assumption(s). "
                                f"Build now clean with {last_sorry_in_attempt} sorry(s). "
                                "Focus Agent3 on closing the remaining sorry placeholders."
                            )
                            continue
                        # Patch applied but build still broken — use updated errors
                        # and fall through to Agent2 with improved context
                        console.print(
                            "  [AssumptionRoute] Build still broken after patch — "
                            "forwarding to Agent2 with assumption context."
                        )

        # General failure: give Agent2 full context for new guidance
        mismatch_prefix = ""
        if patch_mismatch_in_attempt:
            mismatch_prefix = (
                "PATCH MISMATCH: Your previous SEARCH block did not match the file on disk.\n"
                "You MUST copy the SEARCH string VERBATIM from the raw file shown below.\n"
                "Do NOT reconstruct or reformat from memory — any whitespace difference "
                "will cause edit_file_patch to fail again.\n\n"
            )

        if _inner_break_reason == "json_error":
            guidance, _ = _call_agent2_with_tools(
                agent2,
                escalation_registry,
                f"Attempt {attempt} failed.\n"
                "Agent3 returned invalid JSON. Last error: " + last_errors + "\n"
                "Adjust your guidance so Agent3 outputs strict single-action JSON."
                + _classification_request,
            )
            continue

        # Circuit breaker: detect repeat error signatures across consecutive attempts.
        # Normalise primary error as (file, line, first 80 chars of message).
        _primary_err = _structured_errors_final[0] if _structured_errors_final else None
        if _primary_err:
            _err_sig = hashlib.md5(
                f"{_primary_err['file']}:{_primary_err['line']}:"
                f"{_primary_err['message'][:80]}".encode()
            ).hexdigest()
        else:
            _err_sig = hashlib.md5(last_verify_text[:200].encode()).hexdigest() if last_verify_text else ""

        if _err_sig and _err_sig == _last_error_sig:
            _consecutive_repeat_count += 1
        else:
            _consecutive_repeat_count = 0
        _last_error_sig = _err_sig

        # Compute file context and LLM classification for general failure (for injection into Agent2).
        _gen_file_ctx = _build_escalation_file_context(target_file, _err_line_int)
        _ref_files_gen = _get_reference_files_with_descriptions(target_file)
        _llm_class = (
            _llm_classify_error(_primary_err, _gen_file_ctx, target_file)
            if _primary_err else None
        )

        # Append to failed approaches history.
        if last_verify_text and _primary_err:
            _entry = {
                "attempt": attempt,
                "error_type": error_type_final,
                "file": _primary_err["file"],
                "line": _primary_err["line"],
                "message_summary": _primary_err["message"][:100],
                "failure_class": _infer_failure_class(error_type_final, _primary_err["message"]),
            }
            if _llm_class:
                _entry["llm_classification"] = _llm_class
            _failed_approaches.append(_entry)

        _surgeon_mode_forced = _consecutive_repeat_count >= 2
        if _surgeon_mode_forced:
            console.print(
                f"  [CircuitBreaker] attempt {attempt}/{max_retries} — "
                "[red]same error signature for 3+ consecutive attempts — forcing Surgeon Mode"
            )
            _consecutive_repeat_count = 0  # reset after intervention

        _gen_file_ctx = _build_escalation_file_context(target_file, _err_line_int)
        _surgeon_prefix = (
            "[CIRCUIT BREAKER — SURGEON MODE FORCED]\n"
            "The same Lean error has occurred in 3 or more consecutive attempts.\n"
            "Your previous patch approach is NOT working. You MUST change strategy:\n"
            "1. Do NOT repeat the same patch.\n"
            "2. search_codebase to find an alternative Lean 4 API or proof approach.\n"
            "3. Output ONLY a single surgical <<<SEARCH>>>/<<<REPLACE>>> block.\n"
            "4. Each identifier in REPLACE must be verified via lookup first.\n"
            "5. Agent3 is forbidden from free exploration — patch only.\n\n"
            if _surgeon_mode_forced else ""
        )

        # Gate Agent2 for assumption-shaped errors: if the error has only
        # assumption-type goals, the problem is a missing hypothesis in the
        # theorem signature — NOT a proof strategy issue.  Tell Agent2 to add
        # the missing hypotheses rather than change the proof body.
        _assumption_goals_detected = bool(
            _unsolved_goals_now and all_goals_are_assumptions(_unsolved_goals_now)
        )
        _assumption_context_prefix = ""
        if _assumption_goals_detected:
            _missing_types = [
                g["goal"].lstrip("⊢ ").strip()
                for g in _unsolved_goals_now
                if classify_goal(g["goal"]) == "MISSING_ASSUMPTION"
            ]
            _missing_list = "\n".join(f"  • {t}" for t in _missing_types[:6])
            _assumption_context_prefix = (
                "[ROUTING: MISSING ASSUMPTIONS — NOT A PROOF OBLIGATION]\n"
                "All unsolved goals are missing hypothesis types that should be added "
                "to the theorem signature, not fixed in the proof body.\n"
                "Automatic patching was attempted but the build is still broken.\n"
                "Missing hypothesis types:\n"
                f"{_missing_list}\n\n"
                "ACTION REQUIRED: Add the above as explicit hypotheses to the relevant "
                "theorem signature (using `(h_foo : <type>)` parameters), then confirm "
                "Agent3 does NOT change proof tactics for these — just add the params.\n\n"
            )
        _history_prefix = _format_failed_approaches(_failed_approaches[-5:])
        guidance, _a2_route_gen = _call_agent2_with_tools(
            agent2,
            escalation_registry,
            _attempt_diag + _surgeon_prefix + _assumption_context_prefix + _history_prefix + mismatch_prefix
            + f"Attempt {attempt} failed.\n"
            f"Build exit code: {last_exit_code} | Sorry count: {last_sorry_in_attempt}\n"
            f"Error first occurs at line {line_no_display_final}.\n"
            f"=== FULL LEAN ERROR OUTPUT ===\n```\n"
            f"{_prioritize_error_text(_structured_errors_final, last_verify_text, _err_line_int, target_file)}"
            f"\n```\n"
            f"\n=== AGENT3'S CURRENT FILE ({target_file}) ===\n"
            f"```lean\n{_gen_file_ctx}\n```\n\n"
            f"SURGEON MODE: Diagnose the root cause of the Lean error above. "
            f"Focus on line {line_no_display_final} and its surrounding context. "
            "Then output one PATCH block per error in the <<<SEARCH>>>/<<<REPLACE>>> format. "
            "SEARCH must be copied verbatim from the current file (exact whitespace/indentation). "
            "Write the exact correct Mathlib 4 code in REPLACE — no vague suggestions. "
            "If a Level-2 helper lemma is missing, add it DIRECTLY in the target file "
            "before the main theorem using edit_file_patch (with sorry body). "
            "If REPLACE uses a Lib/ lemma, add a comment above the patch: "
            "# Source: Lib/Glue/<File>.lean or Lib/Layer0/<File>.lean — <lemma name>. "
            "Do NOT name a lemma you have not verified in the file context provided. "
            "Agent3 will apply your patches verbatim as edit_file_patch calls.\n\n"
            + _retrieve_catalog_context(
                _extract_new_identifiers_from_guidance(last_verify_text)
            )
            + _classification_request,
        )
        # ---- Agent2 Router: execute routing decision for general failure ----
        _final_route_gen = _apply_agent2_route(
            _a2_route_gen, _routing_budget, _err_sig, _route_repeat_tracker
        )
        if _final_route_gen in ("agent7", "agent7_then_agent6"):
            _routing_budget["preemptive_agent7"] = _routing_budget.get("preemptive_agent7", 0) + 1
            _a7_hint_gen = (_a2_route_gen or {}).get("agent7_hint", "")
            _a7_prompt_gen = _build_preemptive_agent7_prompt(
                _a7_hint_gen, target_file, last_verify_text, agent7_registry
            )
            agent7.messages.clear()
            _a7_plan_gen, _ = _call_agent7_with_tools(agent7, agent7_registry, _a7_prompt_gen)
            if _a7_plan_gen:
                _active_agent7_plan = _a7_plan_gen
                _agent7_current_step_idx = 0
                _agent7_invocations_this_attempt += 1
                console.print(
                    f"  [A2Router→Agent7] Preemptive Agent7 triggered by general-failure route "
                    f"(confidence={(_a2_route_gen or {}).get('confidence', '?')})"
                )
            if _final_route_gen == "agent7_then_agent6":
                _ft_gen = (_a7_plan_gen or {}).get("fallback_trigger", {}) if _a7_plan_gen else {}
                _agent7_approved_agent6 = str(_ft_gen.get("route_to", "")).lower() == "agent6"
                console.print(f"  [A2Router→Agent7→Agent6] agent6_approved={_agent7_approved_agent6}")
        elif _final_route_gen == "self":
            _routing_budget["self_revisions"] = _routing_budget.get("self_revisions", 0) + 1
            _self_msg_gen = (
                "[SELF_REVISION] Your current proof strategy has low confidence. "
                "Revise the overall proof approach fundamentally. Do NOT reuse the same tactics.\n\n"
                + guidance
            )
            guidance, _ = _call_agent2_with_tools(agent2, escalation_registry, _self_msg_gen)
            console.print("  [A2Router→Self] Agent2 self-revision triggered (general failure)")

    # Restore any shared Glue/Layer0 files Agent3 may have edited before exiting Phase 3.
    for _gp, _goriginal in _glue_snapshot.items():
        _gp_rel = str(_gp.relative_to(PROJECT_ROOT))
        if snapshot_file(_gp_rel) != _goriginal:
            registry.call("overwrite_file", path=_gp_rel, content=_goriginal)
            console.print(f"  [Glue] Restored {_gp.name} (was modified by Agent3)")
    for _lp, _loriginal in _layer0_snapshot.items():
        _lp_rel = str(_lp.relative_to(PROJECT_ROOT))
        if snapshot_file(_lp_rel) != _loriginal:
            registry.call("overwrite_file", path=_lp_rel, content=_loriginal)
            console.print(f"  [Layer0] Restored {_lp.name} (was modified by Agent3)")

    # ------------------------------------------------------------------
    # Agent8 Decision Hub: last-resort error-recovery before Agent5.
    # Each tick clears Agent8 context, builds minimal diagnostic info,
    # and dispatches a single targeted action.  On success → Phase 3 done.
    # On exhaustion → reset all agents and fall through to Agent5.
    # ------------------------------------------------------------------
    from orchestrator.phase3_agent8 import run_agent8_loop

    console.print(
        "[magenta bold]"
        + (
            "Agent9 plan ready — entering Agent8 Decision Hub as primary Phase 3 driver."
            if _agent9_plan
            else "Max retries exhausted — entering Agent8 Decision Hub."
        )
    )
    _agent8_success, _agent8_plan, _agent8_errors = run_agent8_loop(
        agent2,
        target_file,
        guidance,
        last_errors,
        best_checkpoint=best_checkpoint,
        agent9_plan=_agent9_plan,
    )
    if _agent8_success:
        # Restore Glue/Layer0 if Agent8 agents modified them
        for _gp2, _goriginal2 in _glue_snapshot.items():
            _gp2_rel = str(_gp2.relative_to(PROJECT_ROOT))
            if snapshot_file(_gp2_rel) != _goriginal2:
                registry.call("overwrite_file", path=_gp2_rel, content=_goriginal2)
        for _lp2, _loriginal2 in _layer0_snapshot.items():
            _lp2_rel = str(_lp2.relative_to(PROJECT_ROOT))
            if snapshot_file(_lp2_rel) != _loriginal2:
                registry.call("overwrite_file", path=_lp2_rel, content=_loriginal2)
        # Verify full-project build is clean, then re-verify the target file
        # specifically.  run_repo_verify builds the whole project (lake build) and
        # only checks exit_code; it does NOT verify that the target algorithm has
        # sorry=0 after Glue/Layer0 restoration.  We must confirm target is still
        # clean to avoid a false-success when restoration reintroduces a sorry.
        _repo_result = registry.call("run_repo_verify")
        _target_recheck = registry.call("run_lean_verify", target_file)
        if (
            int(_repo_result.get("exit_code", 1)) == 0
            and int(_target_recheck.get("exit_code", 1)) == 0
            and int(_target_recheck.get("sorry_count", -1)) == 0
        ):
            console.print("[green bold][Agent8] Decision Hub succeeded — Phase 5/7 complete.")
            return True, attempts, "", {
                "execution_history": [r.__dict__ for r in execution_history],
                "attempt_failures": attempt_failures,
                "agent7_invocations": agent7_invocations,
                "agent7_step_execution_log": agent7_step_execution_log,
                "agent7_plan_revisions": agent7_plan_revisions,
                "agent7_blocked_actions": agent7_blocked_actions,
                "agent7_forced_trigger_count": agent7_forced_trigger_count,
                "agent7_force_gate_entries": agent7_force_gate_entries,
                "agent7_force_gate_rejections": agent7_force_gate_rejections,
                "agent7_force_gate_reason_samples": agent7_force_gate_reason_samples,
                "estimated_token_consumption": max(1, token_char_budget // 4),
                "retry_count": sum(
                    1
                    for r in execution_history
                    if r.status_code in {"ERROR", "BLOCKED"}
                ),
            }
        console.print(
            "[yellow][Agent8] File-level verify passed but repo-verify failed. "
            "Falling through to Agent5."
        )
    else:
        # Update plan and errors from Agent8's attempts
        if _agent8_plan:
            guidance = _agent8_plan
        if _agent8_errors:
            last_errors = _agent8_errors

    # Reset all agent memories before Agent5 to prevent context pollution
    agent2.messages.clear()
    agent3.messages.clear()
    agent7.messages.clear()
    agent6.messages.clear()
    console.print(
        "  [Agent8→Agent5] All agent memories cleared before Agent5 escalation."
    )

    console.print("[red bold]Agent8 exhausted — escalating to Agent5.")
    if diag_log:
        console.print(Panel(
            "\n".join(diag_log[-12:]),
            title="[yellow]Phase 3 Retry Log",
        ))
    agent5 = Agent("diagnostician", extra_files=[target_file] if _target_exists_overlay() else [])
    sorry_context = (
        load_file(target_file)
        if _target_exists_overlay()
        else f"(File '{target_file}' does not exist — Prover Agent never created it.)"
    )
    action = auto_repair_loop(
        agent5,
        target_file,
        last_errors,
        guidance,
        sorry_context,
    )

    if action == "fixed":
        _strict_verify = registry.call("run_lean_verify", target_file)
        _strict_exit = int(_strict_verify.get("exit_code", 1))
        _strict_sorry = int(_strict_verify.get("sorry_count", -1))
        if _strict_exit == 0 and _strict_sorry == 0:
            console.print("[green bold][Agent5] Auto-repair fixed the build — Phase 5/7 complete.")
            return True, attempts, "", {
                "execution_history": [r.__dict__ for r in execution_history],
                "attempt_failures": attempt_failures,
                "agent7_invocations": agent7_invocations,
                "agent7_step_execution_log": agent7_step_execution_log,
                "agent7_plan_revisions": agent7_plan_revisions,
                "agent7_blocked_actions": agent7_blocked_actions,
                "agent7_forced_trigger_count": agent7_forced_trigger_count,
                "agent7_force_gate_entries": agent7_force_gate_entries,
                "agent7_force_gate_rejections": agent7_force_gate_rejections,
                "agent7_force_gate_reason_samples": agent7_force_gate_reason_samples,
                "estimated_token_consumption": max(1, token_char_budget // 4),
                "retry_count": sum(
                    1
                    for r in execution_history
                    if r.status_code in {"ERROR", "BLOCKED"}
                ),
            }
        last_errors = str(_strict_verify.get("errors", last_errors))
        console.print(
            "[yellow][Strict Success Gate] Blocked success: "
            f"exit={_strict_exit}, sorry={_strict_sorry}. "
            "Continuing as non-success."
        )
        action = "replan"
    elif action == "abort":
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
            "attempt_failures": attempt_failures,
            "agent7_invocations": agent7_invocations,
            "agent7_step_execution_log": agent7_step_execution_log,
            "agent7_plan_revisions": agent7_plan_revisions,
            "agent7_blocked_actions": agent7_blocked_actions,
            "agent7_forced_trigger_count": agent7_forced_trigger_count,
            "agent7_force_gate_entries": agent7_force_gate_entries,
            "agent7_force_gate_rejections": agent7_force_gate_rejections,
            "agent7_force_gate_reason_samples": agent7_force_gate_reason_samples,
            "estimated_token_consumption": max(1, token_char_budget // 4),
            "retry_count": sum(
                1
                for r in execution_history
                if r.status_code in {"ERROR", "BLOCKED"}
            ),
        }

    return False, attempts, last_errors, {
        "execution_history": [r.__dict__ for r in execution_history],
        "attempt_failures": attempt_failures,
        "agent7_invocations": agent7_invocations,
        "agent7_step_execution_log": agent7_step_execution_log,
        "agent7_plan_revisions": agent7_plan_revisions,
        "agent7_blocked_actions": agent7_blocked_actions,
        "agent7_forced_trigger_count": agent7_forced_trigger_count,
        "agent7_force_gate_entries": agent7_force_gate_entries,
        "agent7_force_gate_rejections": agent7_force_gate_rejections,
        "agent7_force_gate_reason_samples": agent7_force_gate_reason_samples,
        "estimated_token_consumption": max(1, token_char_budget // 4),
        "retry_count": sum(
            1
            for r in execution_history
            if r.status_code in {"ERROR", "BLOCKED"}
        ),
    }
