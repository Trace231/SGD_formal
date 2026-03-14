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
    apply_staging_rules,
    all_goals_are_assumptions,
    classify_goal,
    extract_unsolved_goals,
    goals_to_patch_list,
)
from orchestrator.config import (
    AGENT6_AUTO_ROUTE_ENABLED,
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
    write_staging_lemma,
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
    _DUPLICATE_DECL_RE,
    _PROOF_BODY_LINE_THRESHOLD,
    _parse_lean_errors,
    _json_candidates,
    _classify_lean_error_structured,
    _get_decl_zone_end,
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
    _STAGING_API_MISSPELLINGS,
    _PROJECT_IDENT_RE,
    _LEAN_KEYWORDS,
    _TOP_LEVEL_KEYWORDS,
    _DECL_START,
    _ESCALATION_CHAR_LIMIT,
    _extract_imported_algo_sigs,
    _extract_staging_sigs,
    _format_agent3_tool_feedback,
    _lint_staging_content,
    _format_staging_lint_feedback,
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
    _audit_staging_usage,
)

console = Console()

# Agent3 single-step interactive loop: maximum tool turns per attempt.
# Archetype B gets a 1.5× multiplier applied in phase3_prove.
MAX_AGENT3_TOOL_TURNS = 20


def _scan_sorry_lines_in_file(file_path: str) -> list[int]:
    """Return sorted line numbers that contain a non-commented sorry keyword."""
    tgt = PROJECT_ROOT / file_path
    if not tgt.exists():
        return []
    try:
        lines = tgt.read_text(encoding="utf-8").splitlines()
        return [
            i + 1
            for i, ln in enumerate(lines)
            if re.search(r"\bsorry\b", ln) and not ln.strip().startswith("--")
        ]
    except OSError:
        return []


def _is_line_still_sorry(file_path: str, line: int) -> bool:
    """Return True if ``line`` (1-indexed) still contains the sorry keyword."""
    tgt = PROJECT_ROOT / file_path
    if not tgt.exists():
        return False
    try:
        lines = tgt.read_text(encoding="utf-8").splitlines()
        if 1 <= line <= len(lines):
            return bool(re.search(r"\bsorry\b", lines[line - 1]))
        return False
    except OSError:
        return False


def _apply_agent2_route(
    route: dict | None,
    budget: dict,
    last_error_sig: str,
    route_repeat_tracker: dict,
) -> str:
    """Arbitrate Agent2's routing proposal; return the final route_to string.

    Applies the following guardrails in order:
    1. Invalid / missing route → "agent3"
    2. Confidence below threshold → "agent3"
    3. Anti-oscillation: same (error_sig, route_to) pair seen too many times → escalate
    4. "self" budget exceeded → "agent3"
    5. Preemptive Agent7 budget exceeded → "agent3"
    """
    if route is None:
        return "agent3"
    route_to = str(route.get("route_to", "agent3")).strip()
    confidence = float(route.get("confidence", 0.0))
    valid = {"agent3", "agent7", "agent7_then_agent6", "self"}
    if route_to not in valid:
        return "agent3"
    # Low-confidence guard: only route cross-agent when confident enough.
    min_conf = float(ROUTING_PARAMS.get("MIN_CONFIDENCE_FOR_CROSS_AGENT_ROUTE", 0.6))
    if route_to != "agent3" and confidence < min_conf:
        return "agent3"
    # Anti-oscillation: track how many times (error_sig, route_to) has been chosen.
    max_repeat = int(ROUTING_PARAMS.get("MAX_SAME_ROUTE_REPEAT", 2))
    sig_key = f"{last_error_sig[:40]}:{route_to}"
    route_repeat_tracker[sig_key] = route_repeat_tracker.get(sig_key, 0) + 1
    if route_repeat_tracker[sig_key] > max_repeat:
        # Escalate to next level to break oscillation.
        _escalation = {"agent3": "agent7", "agent7": "self", "self": "agent3"}
        return _escalation.get(route_to, "agent3")
    # "self" budget.
    max_self = int(ROUTING_PARAMS.get("MAX_SELF_REVISIONS_PER_ATTEMPT", 1))
    if route_to == "self" and budget.get("self_revisions", 0) >= max_self:
        return "agent3"
    # Preemptive Agent7 budget.
    max_a7 = int(ROUTING_PARAMS.get("AGENT7_PREEMPTIVE_MAX_PER_ATTEMPT", 1))
    if route_to in ("agent7", "agent7_then_agent6") and budget.get("preemptive_agent7", 0) >= max_a7:
        return "agent3"
    return route_to


def _build_preemptive_agent7_prompt(
    hint: str,
    target_file: str,
    last_verify_text: str,
    _agent7_registry: "ToolRegistry | None" = None,
) -> str:
    """Build the Agent7 prompt for a preemptive (Agent2-routed) invocation."""
    snippet = _build_escalation_file_context(target_file, _extract_first_error_line(last_verify_text))
    dep_sigs = _prequery_dependency_signatures(last_verify_text, target_file)
    return (
        "Produce a strict interface-audit protocol JSON for Agent3.\n"
        f"Target file: {target_file}\n"
        "[Preemptive invocation — triggered by Agent2 routing decision]\n\n"
        f"Agent2 diagnosis:\n{hint[:1200]}\n\n"
        f"Latest build errors:\n```\n{last_verify_text[:2000]}\n```\n\n"
        f"Current file snippet:\n```lean\n{snippet[:8000]}\n```\n\n"
        f"Dependency signatures:\n```lean\n{dep_sigs[:4000]}\n```\n\n"
        "Return strict JSON only as specified in your system prompt."
    )


def phase3_prove(
    agent2: Agent,
    target_file: str,
    plan: str,
    *,
    max_retries: int = MAX_PHASE3_RETRIES,
    archetype: str = "A",
    max_tool_turns: int | None = None,
    progress_detail: str = "normal",
) -> tuple[bool, int, str, dict]:
    """Phase 3: Agent2 ↔ Agent3 proving loop + Agent5 escalation.

    progress_detail controls log verbosity:
      compact — only attempt-level milestones
      normal  — per-sorry start/close/skip + round summaries (default)
      debug   — also prints every tool call and full error text

    Returns (success, attempts, errors_or_empty, audit).
    """
    # Compute per-attempt tool-turn budget.  Archetype B proofs are structurally
    # more complex and get a 1.5× multiplier.  Callers may override via max_tool_turns.
    if max_tool_turns is None:
        max_tool_turns = MAX_AGENT3_TOOL_TURNS
    if archetype.upper() == "B":
        max_tool_turns = int(max_tool_turns * 1.5)
    console.rule("[bold cyan]Phase 3/5 — Prove (fill sorry)")

    agent3 = Agent("sorry_closer", extra_files=[target_file])
    registry = ToolRegistry()
    registry.register_default_tools()
    _algo_name_for_staging = Path(target_file).stem  # e.g. "SVRGOuterLoop"
    _algo_name = _algo_name_for_staging  # alias used in Phase 3a scaffold block
    registry.register(
        "write_staging_lemma",
        functools.partial(write_staging_lemma, target_algo=_algo_name_for_staging),
    )
    # Read-only registry for Agent2 lookup rounds (no write tools exposed).
    readonly_registry = ToolRegistry()
    readonly_registry.register_readonly_tools()
    # Staging registry: read tools + write_staging_lemma for Agent2 mid-proof escalation.
    staging_registry = ToolRegistry()
    staging_registry.register_staging_tools(target_algo=_algo_name_for_staging)
    # Agent6 (Glue Filler): staging tools + get_lean_goal + check_lean_have for glue proof.
    agent6 = Agent("glue_filler", extra_files=[target_file])
    agent6_registry = ToolRegistry()
    agent6_registry.register_staging_tools(target_algo=_algo_name_for_staging)
    # Agent7 (Interface Auditor): read-only lookup + strict execution protocol output.
    agent7 = Agent("interface_auditor", extra_files=[target_file])
    agent7_registry = ToolRegistry()
    agent7_registry.register_readonly_tools()
    from orchestrator.tools import check_lean_have, get_lean_goal
    agent6_registry.register("get_lean_goal", get_lean_goal)
    agent6_registry.register("check_lean_have", check_lean_have)
    diag_log: list[str] = []

    # Pre-check: if the target file already has 0 sorry and builds clean,
    # skip the entire Agent3 loop.  This prevents destructive rewrites when
    # a previous run already completed the proof (e.g., after a Gate 4 crash).
    def _target_exists_overlay() -> bool:
        """True when target exists in workspace or staging overlay."""
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

    # --- Glue Staging setup (Fix B1) ---
    # Architecture: algorithm vs staging separation
    # - Algorithm file: target_file (e.g. Algorithms/<Algo>.lean) — main definitions, theorems.
    #   Created by Agent2 Phase 3a scaffold or pre-existing. Always lives in Algorithms/.
    # - Staging file: Lib/Glue/Staging/<Algo>.lean — glue/bridge lemmas only, added by
    #   Agent3/Agent6 via write_staging_lemma. Algorithm imports staging; never the reverse.
    # - run_lean_verify(target_file) builds the algorithm module (lake build Algorithms.<Algo>),
    #   which pulls in staging as a dependency. Build target is always the algorithm, never staging.
    #
    # Create a per-algorithm staging file under Lib/Glue/Staging/ so Agent3
    # never needs to touch the shared Lib/Glue/*.lean infrastructure.
    _algo_name = Path(target_file).stem  # e.g. "SVRGOuterLoop"
    _staging_path = PROJECT_ROOT / "Lib" / "Glue" / "Staging" / f"{_algo_name}.lean"
    _staging_rel = str(_staging_path.relative_to(PROJECT_ROOT))

    def _staging_exists_overlay() -> bool:
        try:
            load_file(_staging_rel)
            return True
        except FileNotFoundError:
            return False

    def _staging_read_overlay(default: str = "(staging file is empty)") -> str:
        try:
            return load_file(_staging_rel)
        except FileNotFoundError:
            return default

    def _staging_physical_path() -> Path:
        """Return concrete staging glue path in workspace."""
        return _staging_path

    if not snapshot_file(_staging_rel):
        registry.call(
            "write_new_file",
            path=_staging_rel,
            content=(
            f"-- Staging lemmas for {_algo_name} formalization.\n"
            "-- Add new helper lemmas here. Do NOT modify existing Lib/Glue files.\n"
            "import Lib.Glue.Probability\n"
            "import Lib.Glue.Algebra\n"
            "import Lib.Glue.Measurable\n"
            "import Lib.Glue.Calculus\n"
            ),
        )
        console.print(f"  [Staging] Created {_staging_rel}")

    # Remove write_new_file from Agent3's registry: Phase 3a scaffold guarantees the
    # target file exists before Agent3 starts. Agent3 should only use edit_file_patch.
    # Pop after staging creation so the orchestrator can create Lib/Glue/Staging/*.lean.
    registry._tools.pop("write_new_file", None)

    # Inject staging import into algorithm file if not already present.
    if snapshot_file(target_file):
        _tgt_content = load_file(target_file)
        _staging_import = f"import Lib.Glue.Staging.{_algo_name}"
        if _staging_import not in _tgt_content:
            _lines = _tgt_content.splitlines()
            last_import_idx = max(
                (i for i, l in enumerate(_lines) if l.startswith("import")), default=-1
            )
            _lines.insert(last_import_idx + 1, _staging_import)
            registry.call("overwrite_file", path=target_file, content="\n".join(_lines) + "\n")
            console.print(f"  [Staging] Injected import into {target_file}")

    # --- Glue pollution guard (Fix B2) ---
    # Snapshot all existing Lib/Glue/*.lean files (excluding Staging/) so we
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

    last_errors = ""
    last_sorry_count = 0
    attempts = 0
    execution_history: list[ExecutionResult] = []
    attempt_failures: list[dict] = []
    agent3_turns: list[dict] = []
    _last_audit_flush_time: float = time.time()
    # Progress-panel dedup: suppress identical consecutive error text prints.
    _last_printed_err_sig: str | None = None
    agent7_invocations: list[dict] = []
    agent7_step_execution_log: list[dict] = []
    agent7_plan_revisions: list[dict] = []
    agent7_blocked_actions: list[dict] = []
    agent7_forced_trigger_count = 0
    agent7_force_gate_entries: list[dict] = []
    agent7_force_gate_rejections: list[dict] = []
    agent7_force_gate_reason_samples: list[str] = []
    token_char_budget = 0
    # Carry-over Agent7 plan from round-replan routing: set at end of attempt N,
    # consumed at the start of attempt N+1's per-sorry loop initialisation.
    _pending_agent7_plan: dict | None = None

    # Circuit breaker: track consecutive repeat error signatures.
    # Key: normalized (file, line, message) hash of the primary error.
    # If the same signature appears in two consecutive attempts, force Surgeon Mode.
    _last_error_sig: str | None = None
    _consecutive_repeat_count: int = 0

    # Loop guard: track which attempt numbers have already had assumption auto-patching
    # applied, to avoid re-patching the same theorem with the same hypothesis.
    _assumption_patch_tried: set[str] = set()

    # Loop guard: consecutive DEPENDENCY_COMPILE_ERROR streak (same staging error).
    _dep_error_streak: int = 0
    _last_dep_error_sig: str | None = None

    # Failed approaches history: accumulates structured failure records across attempts.
    # Injected into Agent2 prompts so it avoids repeating strategies that already failed.
    _failed_approaches: list[dict] = []

    # get_lean_goal cache: avoids re-running expensive LSP elaboration when the
    # file content and sorry line are identical across attempts.
    # Key: (target_file_relative, sorry_line, file_content_hash)
    _goal_cache: dict[tuple[str, int, str], dict] = {}

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
        "staging_content": _staging_read_overlay(default="") or None,
    }

    # ------------------------------------------------------------------
    # Phase 3a — Scaffold: Agent2 writes ALL theorem statements + sorry
    # placeholders, and verifies exit_code=0 before Agent3 begins.
    # Only runs when the target file does not yet exist.
    # ------------------------------------------------------------------
    if not _target_exists_overlay():
        _scaffold_registry = ToolRegistry()
        _scaffold_registry.register_scaffold_tools(target_algo=_algo_name)
        _algo_name_for_staging = _algo_name
        _scaffold_ok = _call_agent2_scaffold(
            agent2,
            _scaffold_registry,
            target_file,
            guidance,  # Agent2's approved plan from Phase 2
            staging_rel=_staging_rel,
            algo_name=_algo_name_for_staging,
        )
        if not _scaffold_ok:
            console.print(
                "[red bold][Phase 3a] Scaffold failed — Agent2 could not produce "
                "a compiling scaffold. Aborting Phase 3."
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
        # Refresh checkpoint with fresh scaffold content
        _initial_sorry_for_ckpt = int(
            registry.call("run_lean_verify", target_file).get("sorry_count", 999)
        )
        best_checkpoint["sorry_count"] = _initial_sorry_for_ckpt
        best_checkpoint["content"] = load_file(target_file)
        best_checkpoint["staging_content"] = _staging_read_overlay(default="") or None
        initial_hash = _file_hash(target_file)
        initial_exists = True

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
                    f"{guidance[:2000]}\n\n"
                    f"## Best checkpoint (sorry={best_checkpoint['sorry_count']})\n"
                    f"```lean\n{(best_checkpoint['content'] or '')[:3000]}\n```\n\n"
                    f"## Failed approaches — do NOT repeat these\n{_distilled_failures}\n\n"
                    "Provide updated proof strategy for the next attempt."
                )
                guidance, _ = _call_agent2_with_tools(agent2, staging_registry, _distilled_ctx)
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
            "search_codebase, edit_file_patch, write_staging_lemma, get_lean_goal, "
            "check_lean_have, run_lean_verify, request_agent6_glue, request_agent2_help, "
            "request_agent7_interface_audit.\n"
            "SITUATIONAL BEHAVIOR:\n"
            "- If guidance contains PATCH blocks (<<<SEARCH>>>/<<<REPLACE>>>): "
            "execute them exactly — copy old_str and new_str verbatim.\n"
            "- When you receive a tool result: analyze it and decide your next action.\n"
            "- After any edit call run_lean_verify to confirm.\n\n"
            "GLUE STAGING RULE (non-negotiable):\n"
            f"- You may edit: {target_file}, {_staging_rel}\n"
            "- Lib/Glue/Probability.lean, Algebra.lean, Measurable.lean, Calculus.lean: READ-ONLY.\n"
            "- All Lib/Layer0/*.lean files (ConvexFOC.lean, IndepExpect.lean, GradientFTC.lean) "
            "are READ-ONLY. Use read_file_readonly to inspect them, never edit_file_patch.\n"
            f"- NEW glue lemmas (Level 2 gaps) go to {_staging_rel}.\n"
            f"  Agent2 may have already written them there — check the staging file section below.\n"
            "  A staging lemma may have `sorry` body; that is intentional and not penalized.\n"
            f"- {_staging_rel} already imports all main Lib/Glue files.\n"
            "- BEFORE adding any new 'import X' statement to any file, call "
            "read_file_readonly(\"Main.lean\") or read_file_readonly(\"lakefile.lean\") "
            "to verify that X does not already import the file you are editing "
            "(which would create a circular dependency).\n"
            f"- CRITICAL: {_staging_rel} does NOT import {target_file}. Any lemma you "
            f"add to {_staging_rel} CANNOT reference definitions that are first defined "
            f"in {target_file} (e.g., `outerProcess`, or any `def`/`theorem` introduced "
            f"there). Such references always fail with 'Invalid field' or 'unknown "
            f"identifier'. If a helper needs those definitions, place it INSIDE "
            f"{target_file} directly.\n"
            + _no_overwrite_rule
            + "\n"
            f"Target file: {target_file}\n"
            + (_imported_sigs_block.lstrip("\n") + "\n" if _imported_sigs_block else "")
            + (_extract_staging_sigs(_staging_path) if _staging_exists_overlay() else "")
            + (
                "\n## Staging file (writable — add new glue lemmas here)\n"
                f"File: {_staging_rel}\n"
                "```lean\n"
                + _staging_read_overlay(default="")
                + "\n```\n"
                "If a lemma is NOT in Lib/Glue/*.lean but IS in this staging file, use it directly.\n"
                f"To add a new lemma: use write_staging_lemma(staging_path=\"{_staging_rel}\", "
                f"lean_code=\"...\") to append, or edit_file_patch to modify existing content.\n\n"
            )
            + f"Guidance:\n{guidance}"
        )

        # Staging errors flag (affects goal prequery elaboration).
        _staging_has_errors = (
            last_exit_code != 0
            and last_verify_text
            and any("Staging" in e.get("file", "") for e in _parse_lean_errors(last_verify_text))
        ) if attempt > 1 else False

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

        # Staging file lint check once per attempt before sorry loop.
        if _staging_exists_overlay():
            _staging_lint_violations = _lint_staging_content(
                _staging_read_overlay(default="")
            )
            if _staging_lint_violations:
                _lint_feedback = _format_staging_lint_feedback(
                    _staging_lint_violations, _staging_rel
                )
                console.print(
                    f"  [StagingLint] attempt {attempt} — "
                    f"{len(_staging_lint_violations)} lint violation(s) found in staging file"
                )
                # Use a temporary agent3 call; result feeds into first sorry's context.
                _lint_reply = agent3.call(_lint_feedback)
                token_char_budget += len(_lint_feedback) + len(_lint_reply)

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
                _staging_has_errors,
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

            # -------------------------------------------------------------------
            # Single-step interactive tool loop (per sorry)
            # Each iteration: parse one action, execute it, return result.
            # -------------------------------------------------------------------
            for tool_turn in range(_per_sorry_remaining):
                _total_turns_this_attempt += 1
                _turns_this_sorry += 1
                # Parse Agent3's single action
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
                        f"Current snippet:\n```lean\n{current_snippet[:8000]}\n```\n\n"
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
                                    console.print(f"  [Staging] Restored {_gp.name} (was modified)")
                            for _lp, _loriginal in _layer0_snapshot.items():
                                _lp_rel = str(_lp.relative_to(PROJECT_ROOT))
                                if snapshot_file(_lp_rel) != _loriginal:
                                    registry.call("overwrite_file", path=_lp_rel, content=_loriginal)
                                    console.print(f"  [Layer0] Restored {_lp.name} (was modified by Agent3)")
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
                        _staging_path,
                        _staging_rel,
                        goal,
                        error_message,
                        diagnosis,
                        _algo_name_for_staging,
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
                        _staging_snippet = _staging_read_overlay()
                        new_guidance, _ = _call_agent2_with_tools(
                            agent2,
                            staging_registry,
                            f"[AGENT6 FALLBACK — Agent6 could not prove glue]\n"
                            f"Agent3 escalated with infrastructure diagnosis. Agent6 failed.\n\n"
                            f"Error: {error_message}\nDiagnosis: {diagnosis}\n\n"
                            f"Target: {target_file} line {stuck_at_line}. Goal: {goal[:500]}...\n\n"
                            f"=== CURRENT FILE ({target_file}) ===\n```lean\n{_current_snippet}\n```\n\n"
                            f"=== STAGING FILE ({_staging_rel}) ===\n```lean\n{_staging_snippet}\n```\n\n"
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
                    _staging_snippet = _staging_read_overlay()
                    new_guidance, _a2_route_mid = _call_agent2_with_tools(
                        agent2,
                        staging_registry,
                        f"[AGENT3 ESCALATION — MID-ATTEMPT HELP REQUEST]\n"
                        f"Agent3 is stuck on line {stuck_at_line} after "
                        f"{attempts_tried} turns.\n\n"
                        f"Agent3's error:\n```\n{error_message}\n```\n\n"
                        f"Agent3's diagnosis:\n{diagnosis}\n\n"
                        f"=== CURRENT FILE ({target_file}) ===\n"
                        f"```lean\n{current_file_snippet}\n```\n\n"
                        f"=== STAGING FILE ({_staging_rel}) ===\n"
                        f"```lean\n{_staging_snippet}\n```\n\n"
                        "Apply your Sorry-Fill Proof Path Protocol. "
                        "Classify the problem as structural (A) or tactical (B) "
                        "and provide revised, concrete guidance with exact Lean API "
                        "calls. Agent3 will continue in the SAME attempt.\n"
                        "If a Level-2 missing glue lemma is needed, use write_staging_lemma "
                        f"to add it to {_staging_rel} NOW — do not just describe it.\n"
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
                            f"Current snippet:\n```lean\n{_agent7_esc_snippet[:6000]}\n```\n\n"
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
                    # Runtime trajectory check (P2): warn if Agent3 patches without
                    # any preceding lookup in this attempt.
                    if not _lookup_done_since_last_edit and tool_turn > 0:
                        _patch_without_lookup_count += 1
                        if _patch_without_lookup_count <= 2:
                            _traj_warning = (
                                "## ⚠ TRAJECTORY VIOLATION — PATCH WITHOUT LOOKUP\n"
                                "You are about to apply a patch without having called "
                                "search_codebase, search_in_file, or read_file since the "
                                "last edit in this attempt.\n\n"
                                "We STRONGLY RECOMMEND verifying identifiers before patching.\n\n"
                                "Call search_codebase or search_in_file for the identifiers in "
                                "your REPLACE block NOW, then re-issue your edit_file_patch.\n\n"
                                "Exception: if these are Lean built-in tactics (simp, ring, etc.) "
                                "or local binders, you may ignore this warning."
                            )
                            raw_reply = agent3.call(_traj_warning)
                            token_char_budget += len(_traj_warning) + len(raw_reply)
                            continue  # let Agent3 do a lookup before patching
                    _lookup_done_since_last_edit = False  # reset after edit

                    _patch_warning = _check_patch_symbols(arguments, registry)
                    if _patch_warning:
                        console.print(
                            f"  [PatchSymbolCheck] attempt {attempt} turn {tool_turn + 1} — "
                            "unverified identifiers detected, feeding back to Agent3"
                        )
                        raw_reply = agent3.call(_patch_warning)
                        token_char_budget += len(_patch_warning) + len(raw_reply)
                        continue  # let Agent3 self-correct before applying patch

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
                    # Post-edit staging lint: if the edited file is the staging file,
                    # run lint immediately and feed violations back to Agent3.
                    _edited_path_str = str(arguments.get("path", ""))
                    if (
                        _edited_path_str
                        and "Staging" in _edited_path_str
                        and _staging_exists_overlay()
                    ):
                        _post_lint = _lint_staging_content(
                            _staging_read_overlay(default="")
                        )
                        if _post_lint:
                            _post_lint_msg = _format_staging_lint_feedback(
                                _post_lint, _staging_rel
                            )
                            console.print(
                                f"  [StagingLint] post-edit — "
                                f"{len(_post_lint)} violation(s) remain in staging file"
                            )
                            result_msg = result_msg + "\n\n" + _post_lint_msg
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
                                f"Current snippet:\n```lean\n{current_snippet[:8000]}\n```\n\n"
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
                            "staging_content": (
                                snapshot_file(_staging_rel)
                                if snapshot_file(_staging_rel) else None
                            ),
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
                        if best_checkpoint.get("staging_content") is not None:
                            registry.call(
                                "overwrite_file",
                                path=_staging_rel,
                                content=best_checkpoint["staging_content"],
                            )
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
                                        console.print(f"  [Staging] Restored {_gp.name} (was modified)")
                                for _lp, _loriginal in _layer0_snapshot.items():
                                    _lp_rel = str(_lp.relative_to(PROJECT_ROOT))
                                    if snapshot_file(_lp_rel) != _loriginal:
                                        registry.call("overwrite_file", path=_lp_rel, content=_loriginal)
                                        console.print(f"  [Layer0] Restored {_lp.name} (was modified by Agent3)")
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
                        console.print(
                            f"  [A3] a{attempt}/{max_retries} "
                            f"t{tool_turn + 1}/{_per_sorry_remaining} — "
                            f"exit={last_exit_code} sorry={last_sorry_in_attempt}"
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
                        _dze_fb = _get_decl_zone_end(PROJECT_ROOT / target_file)
                        if _pline_fb <= _dze_fb:
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
                            # Also restore staging file to its checkpointed state.
                            if best_checkpoint.get("staging_content") is not None:
                                registry.call(
                                    "overwrite_file",
                                    path=_staging_rel,
                                    content=best_checkpoint["staging_content"],
                                )
                            # Restore any Glue files Agent3 may have corrupted.
                            for _gp, _goriginal in _glue_snapshot.items():
                                _gp_rel = str(_gp.relative_to(PROJECT_ROOT))
                                if snapshot_file(_gp_rel) != _goriginal:
                                    registry.call("overwrite_file", path=_gp_rel, content=_goriginal)
                                    console.print(f"  [Staging] Restored {_gp.name} (SIGNATURE_HALLUCINATION rollback)")
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
                            _halluc_scaffold_registry.register_scaffold_tools(
                                target_algo=_algo_name_for_staging
                            )
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
                                staging_registry,
                                _halluc_err_ctx + "Provide updated strategy for the re-scaffold.",
                            )
                            _scaffold_ok_h = _call_agent2_scaffold(
                                agent2,
                                _halluc_scaffold_registry,
                                target_file,
                                guidance,
                                staging_rel=_staging_rel,
                                algo_name=_algo_name_for_staging,
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
                                    _staging_path,
                                    _staging_rel,
                                    goal,
                                    str(_primary_local.get("message", ""))[:600],
                                    infra_diag,
                                    _algo_name_for_staging,
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
                                    _staging_snippet = _staging_read_overlay()
                                    new_guidance, _ = _call_agent2_with_tools(
                                        agent2,
                                        staging_registry,
                                        f"[AGENT6 AUTO-ROUTE FALLBACK — Agent6 could not prove glue]\n"
                                        f"System detected infra gap: {infra_diag}\n\n"
                                        f"Error: {_primary_local.get('message', '')}\n\n"
                                        f"Target: {target_file} line {err_line_no}. Goal: {goal[:500]}...\n\n"
                                        f"=== CURRENT FILE ({target_file}) ===\n```lean\n{_current_snippet}\n```\n\n"
                                        f"=== STAGING FILE ({_staging_rel}) ===\n```lean\n{_staging_snippet}\n```\n\n"
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
                        # Errors originate from a staging/dependency file, not target.
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
                            "[cyan]DEPENDENCY_COMPILE_ERROR — routing to dep-fix (staging fix)"
                        )
                        # Try deterministic rule-based staging fix first (no LLM call).
                        _staging_rule_fixes = apply_staging_rules(_staging_physical_path(), last_verify_text)
                        if _staging_rule_fixes > 0:
                            console.print(
                                f"  [Auto-fix] Applied {_staging_rule_fixes} rule-based "
                                f"fix(es) to {_staging_path.name} — skipping Agent2 call."
                            )
                            _inner_break_reason = "dep_compile_error"
                            _break_attempt = True
                            break
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
                            staging_registry,
                            _attempt_diag
                            +
                            f"[DEPENDENCY COMPILE ERROR — STAGING/IMPORT FILE BROKEN]\n"
                            f"Errors are in a dependency or staging file, NOT in {target_file}.\n\n"
                            f"Failing dependency errors:\n```\n{_dep_errors_text}\n```\n\n"
                            f"Target file ({target_file}) is NOT the source of errors — "
                            "do NOT rewrite or delete the target.\n\n"
                            "REQUIRED ACTION:\n"
                            "1. search_codebase to find the correct Lean 4 / Mathlib API names "
                            "for any unknown identifiers.\n"
                            "2. Use write_staging_lemma or edit_file_patch to fix the staging "
                            f"file ({_staging_rel}) only.\n"
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
                            "staging_content": (
                                _staging_read_overlay(default="") or None
                            ),
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
                "If a Level-2 missing glue lemma is needed, write it to staging NOW.\n\n"
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
                agent2, staging_registry, _round_replan_prompt
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
                guidance, _ = _call_agent2_with_tools(agent2, staging_registry, _self_msg_replan)
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
            console.print(
                f"  [AttemptSummary] a{attempt}/{max_retries} "
                f"turns={_total_turns_this_attempt} "
                f"exit={last_exit_code} sorry={last_sorry_in_attempt} | "
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
        # NOTE: DEPENDENCY_COMPILE_ERROR is excluded — when staging is broken
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
                guidance, _a2_route_noop = _call_agent2_with_tools(agent2, staging_registry, _noop_ctx)
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
                    guidance, _ = _call_agent2_with_tools(agent2, staging_registry, _self_msg_noop)
                    console.print("  [A2Router\u2192Self] Agent2 self-revision triggered (NOOP)")
                continue

        # DEPENDENCY_COMPILE_ERROR: staging/dep broken — fix dep, never rewrite target
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
            # Try deterministic rule-based staging fix first (no LLM call).
            _staging_rule_fixes_post = apply_staging_rules(_staging_physical_path(), last_verify_text)
            if _staging_rule_fixes_post > 0:
                console.print(
                    f"  [Auto-fix] Applied {_staging_rule_fixes_post} rule-based "
                    f"fix(es) to {_staging_path.name} — retrying without Agent2 call."
                )
                _dep_error_streak = 0  # reset streak after a fix
                continue
            _dep_staging_ctx = _staging_read_overlay()
            _ref_files_dep = _get_reference_files_with_descriptions(target_file)
            _ref_class_dep = _format_ref_and_classification_blocks(
                _ref_files_dep, None
            )
            guidance, _ = _call_agent2_with_tools(
                agent2,
                staging_registry,
                _attempt_diag
                + _format_failed_approaches(_failed_approaches[-5:])
                + (
                    f"[DEP-ERROR STREAK: {_dep_error_streak} consecutive identical staging errors]\n"
                    "You MUST change your approach — previous fixes did not work.\n\n"
                    if _dep_error_streak >= 2 else ""
                )
                + f"[DEPENDENCY COMPILE ERROR — ATTEMPT {attempt} FAILED]\n"
                f"Errors are in a dependency/staging file, NOT in {target_file}.\n\n"
                f"Dependency errors:\n```\n{_dep_errors_final}\n```\n\n"
                f"=== STAGING FILE ({_staging_rel}) ===\n"
                f"```lean\n{_dep_staging_ctx}\n```\n\n"
                "Do NOT rewrite or delete the target file.\n\n"
                "REQUIRED:\n"
                "1. search_codebase to find the correct Lean 4 / Mathlib API for each "
                "unknown identifier shown above.\n"
                "2. Fix the staging file using write_staging_lemma or edit_file_patch.\n"
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
            staging_has_errors=False,
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
            "Use when Agent6 (glue filler) must be invoked to prove a new staging lemma.\n"
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
            _staging_content_ctx = _staging_read_overlay()
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
                staging_registry, target_file, _err_line_int, _goal_cache
            )
            guidance, _a2_route_local = _call_agent2_with_tools(
                agent2,
                staging_registry,
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
                f"=== STAGING FILE ({_staging_rel}) ===\n"
                f"```lean\n{_staging_content_ctx}\n```\n\n"
                f"Agent3 used all {max_tool_turns} turns on line {line_no_display_final} "
                f"and could not fix the error.\n\n"
                f"DIAGNOSE FIRST — apply your Sorry-Fill Proof Path Protocol:\n\n"
                f"(A) STRUCTURAL error (type incompatibility, missing glue lemma, wrong proof\n"
                f"    approach that cannot be fixed by patching the current code):\n"
                f"    → Do NOT sorry-degrade. Provide a NEW proof strategy for the next attempt.\n"
                f"    → If a Level-2 glue lemma is missing, use write_staging_lemma to add it\n"
                f"      to {_staging_rel} NOW (with sorry body). Do not just describe it.\n"
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
                f"4. For case A with a missing glue lemma: use write_staging_lemma first,\n"
                f"   then reference it in your guidance for Agent3.\n\n"
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
                guidance, _ = _call_agent2_with_tools(agent2, staging_registry, _self_msg_local)
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
                staging_registry,
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
        _gen_staging_ctx = _staging_read_overlay()
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
            staging_registry,
            _attempt_diag + _surgeon_prefix + _assumption_context_prefix + _history_prefix + mismatch_prefix
            + f"Attempt {attempt} failed.\n"
            f"Build exit code: {last_exit_code} | Sorry count: {last_sorry_in_attempt}\n"
            f"Error first occurs at line {line_no_display_final}.\n"
            f"=== FULL LEAN ERROR OUTPUT ===\n```\n"
            f"{_prioritize_error_text(_structured_errors_final, last_verify_text, _err_line_int, target_file)}"
            f"\n```\n"
            f"\n=== AGENT3'S CURRENT FILE ({target_file}) ===\n"
            f"```lean\n{_gen_file_ctx}\n```\n\n"
            f"=== STAGING FILE ({_staging_rel}) ===\n"
            f"```lean\n{_gen_staging_ctx}\n```\n\n"
            f"SURGEON MODE: Diagnose the root cause of the Lean error above. "
            f"Focus on line {line_no_display_final} and its surrounding context. "
            "Then output one PATCH block per error in the <<<SEARCH>>>/<<<REPLACE>>> format. "
            "SEARCH must be copied verbatim from the current file (exact whitespace/indentation). "
            "Write the exact correct Mathlib 4 code in REPLACE — no vague suggestions. "
            "If a Level-2 glue lemma is missing, use write_staging_lemma to add it to "
            f"{_staging_rel} (with sorry body) before writing guidance for Agent3. "
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
            guidance, _ = _call_agent2_with_tools(agent2, staging_registry, _self_msg_gen)
            console.print("  [A2Router→Self] Agent2 self-revision triggered (general failure)")

    # Staging lemma usage audit (6c): report which staging lemmas were referenced.
    if snapshot_file(_staging_rel) and snapshot_file(target_file):
        console.rule("[dim]Staging usage audit")
        _audit_staging_usage(target_file, _staging_path, console.print)

    # Restore any shared Glue/Layer0 files Agent3 may have edited before exiting Phase 3.
    for _gp, _goriginal in _glue_snapshot.items():
        _gp_rel = str(_gp.relative_to(PROJECT_ROOT))
        if snapshot_file(_gp_rel) != _goriginal:
            registry.call("overwrite_file", path=_gp_rel, content=_goriginal)
            console.print(f"  [Staging] Restored {_gp.name} (was modified by Agent3)")
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

    console.print("[magenta bold]Max retries exhausted — entering Agent8 Decision Hub.")
    _agent8_success, _agent8_plan, _agent8_errors = run_agent8_loop(
        agent2,
        target_file,
        _staging_rel,
        guidance,
        last_errors,
        best_checkpoint=best_checkpoint,
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
        # Verify with run_repo_verify for full-project clean build
        _repo_result = registry.call("run_repo_verify")
        if int(_repo_result.get("exit_code", 1)) == 0:
            console.print("[green bold][Agent8] Decision Hub succeeded — Phase 3 complete.")
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
    _staging_file_for_repair = (
        str(_staging_physical_path()) if _staging_exists_overlay() else None
    )
    action = auto_repair_loop(
        agent5,
        target_file,
        _staging_file_for_repair,
        last_errors,
        guidance,
        sorry_context,
    )

    if action == "fixed":
        _strict_verify = registry.call("run_lean_verify", target_file)
        _strict_exit = int(_strict_verify.get("exit_code", 1))
        _strict_sorry = int(_strict_verify.get("sorry_count", -1))
        if _strict_exit == 0 and _strict_sorry == 0:
            console.print("[green bold][Agent5] Auto-repair fixed the build — Phase 3 complete.")
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
        "the keyword (def/lemma/theorem).\n"
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

        missing_now = check_used_in_tags([target_file])
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
) -> None:
    """Execute the full 5-phase pipeline."""

    if target_file is None:
        target_file = f"Algorithms/{algorithm}.lean"

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

    try:
        with Progress(
            SpinnerColumn(),
            TextColumn("{task.description}"),
            BarColumn(),
            transient=True,
        ) as progress:
            task = progress.add_task("Orchestrating...", total=5)

            # Phase 1
            audit.set_phase(1)
            progress.update(task, description="Phase 1/5: Generating prover prompt...")
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
                progress.update(task, description="Phase 2/5: Planning & approval...")
                plan, agent1, agent2 = phase2_plan_and_approve(
                    prover_prompt, force_low_leverage
                )
                progress.advance(task)

                # Phase 3
                audit.set_phase(3)
                progress.update(task, description="Phase 3/5: Proving (fill sorry)...")
                success, attempts, _, phase3_audit = phase3_prove(
                    agent2, target_file, plan,
                    max_retries=max_retries,
                    archetype=archetype,
                    max_tool_turns=max_tool_turns,
                    progress_detail=progress_detail,
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
                    progress.advance(task)  # re-enter at phase 2

            progress.advance(task)

            # Phase 4
            audit.set_phase(4)
            progress.update(task, description="Phase 4/5: Persisting docs...")
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

            # Phase 5
            audit.set_phase(5)
            progress.update(task, description="Phase 5/5: Finalizing metrics...")
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

    args = parser.parse_args()

    if args.interactive:
        fields = _interactive_input()
    else:
        if not all([args.algorithm, args.update_rule, args.proof_sketch, args.archetype]):
            parser.error(
                "Provide --algorithm, --update-rule, --proof-sketch, and "
                "--archetype, or use --interactive."
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
    )


if __name__ == "__main__":
    main()
