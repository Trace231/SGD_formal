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
import concurrent.futures
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

console = Console()

_CATALOG_LEMMA_HEADING_RE = re.compile(r"^####\s+`([^`]+)`", re.MULTILINE)
_LIB_DECL_RE = re.compile(
    r"^(?:theorem|lemma|noncomputable\s+def|def)\s+([A-Za-z_]\w*)",
    re.MULTILINE,
)

# ---------------------------------------------------------------------------
# Error classification — four-way classifier with structured error parsing
# ---------------------------------------------------------------------------

# "Unknown symbol" family — triggers SIGNATURE_HALLUCINATION only when the
# error is in the declaration zone of the *target* file.
# NOTE: 'failed to synthesize instance' is intentionally excluded; it is
# always a proof-body problem (LOCAL_PROOF_ERROR).
_UNKNOWN_SYMBOL_RE = re.compile(
    r"unknown identifier|unknown constant|unknown tactic",
    re.IGNORECASE,
)

# Type-class synthesis failures — always LOCAL_PROOF_ERROR, never hallucination.
_TYPECLASS_FAIL_RE = re.compile(r"failed to synthesize instance", re.IGNORECASE)
_TYPE_MISMATCH_RE = re.compile(
    r"Application type mismatch|Type mismatch|Function expected",
    re.IGNORECASE,
)

# Duplicate declarations always corrupt the target — full rewrite required.
_DUPLICATE_DECL_RE = re.compile(r"has already been declared", re.IGNORECASE)

# Lean structured error format: file.lean:LINE:COL: error: message
_LEAN_STRUCTURED_ERROR_RE = re.compile(
    r"([\w./\\-]+\.lean):(\d+):(\d+):\s*error:\s*([^\n]+)",
    re.IGNORECASE,
)

# Lake JSON error format: error: file.lean:LINE:COL: message
_LEAN_JSON_ERROR_RE = re.compile(
    r"^error:\s+([\w./\\-]+\.lean):(\d+):(\d+):\s*([^\n]*)",
    re.IGNORECASE | re.MULTILINE,
)

# Legacy single-group line extractor — kept for callers that use it directly.
_LEAN_ERROR_LINE_RE = re.compile(
    r"(?:[\w./\\-]+\.lean:(\d+):\d+:\s*error:"   # standard: file:line:col: error:
    r"|error:\s+[\w./\\-]+\.lean:(\d+):\d+:)",    # Lake JSON: error: file:line:col:
    re.IGNORECASE,
)

# Fallback threshold used only when structured parsing yields no results.
_PROOF_BODY_LINE_THRESHOLD = 50

# Minimum Agent2 lookup rounds required before guidance is forwarded to Agent3.
# Set to 0 to revert to the old warning-only behaviour.
_MIN_AGENT2_LOOKUP_ROUNDS = 2

# Known Lean 4 API misspellings in staging files: wrong_pattern → correct_name_hint.
_STAGING_API_MISSPELLINGS: dict[str, str] = {
    r"\bMeasurable\.prod_mk\b": "Measurable.prodMk",
    r"\b\.prod_mk\b": ".prodMk",
    r"\bsgdProcess_zero\b": "SVRGSetup.process_zero (dot notation)",
    r"\bsgdProcess_succ\b": "SVRGSetup.process_succ (dot notation)",
    r"\bsgdProcess_measurable\b": "SVRGSetup.svrgProcess_measurable",
}

# Snake_case identifiers that look like project-specific lemma names.
_PROJECT_IDENT_RE = re.compile(r"\b([a-z][a-z0-9]*(?:_[a-z][a-z0-9]*){1,})\b")

# Lean 4 / Mathlib tactics and keywords excluded from symbol existence checks.
_LEAN_KEYWORDS: frozenset[str] = frozenset([
    "linarith", "ring", "simp", "exact", "apply", "intro", "have", "show",
    "refine", "constructor", "trivial", "decide", "norm_num", "positivity",
    "fun", "let", "by", "do", "if", "then", "else", "match", "with", "at",
    "mul_comm", "add_comm", "mul_one", "one_mul", "zero_mul", "mul_zero",
    "sub_self", "add_zero", "zero_add", "neg_neg", "neg_zero",
    "pow_succ", "pow_zero", "pow_one", "mul_pow", "add_pow",
    "integral_const", "integral_add", "integral_sub", "integral_smul",
    "measurable_const", "aemeasurable_const", "integral_mono",
    "norm_nonneg", "norm_sq_nonneg", "inner_comm", "real_inner_comm",
    "div_nonneg", "mul_nonneg", "add_nonneg", "pow_nonneg",
    "ge_iff_le", "le_refl", "lt_irrefl", "field_simp", "push_neg",
    "calc", "have", "suffices", "obtain", "rcases", "use", "rw", "rfl",
    "simp_rw", "norm_cast", "push_cast", "ring_nf", "congr", "ext",
])

# Agent3 single-step interactive loop: maximum tool turns per attempt.
# Archetype B gets a 1.5× multiplier applied in phase3_prove.
MAX_AGENT3_TOOL_TURNS = 20

# ---------------------------------------------------------------------------
# Imported algorithm API signature injection
# ---------------------------------------------------------------------------

_TOP_LEVEL_KEYWORDS = re.compile(
    r"^(?:noncomputable\s+)?(?:def|theorem|lemma|abbrev|structure|class|instance"
    r"|namespace|section|end|open|variable|attribute|@\[|--)",
    re.MULTILINE,
)

_DECL_START = re.compile(
    r"^(?:noncomputable\s+)?(?:def|theorem|lemma|abbrev)\s+\w",
)


def _parse_lean_errors(verify_text: str) -> list[dict]:
    """Parse Lean build output into structured error records.

    Returns a list of dicts with keys: file, line, col, message.
    Handles both standard format (file:line:col: error: msg) and
    Lake JSON format (error: file:line:col: msg).
    """
    errors: list[dict] = []
    seen: set[tuple] = set()

    for m in _LEAN_STRUCTURED_ERROR_RE.finditer(verify_text):
        key = (m.group(1), m.group(2), m.group(3))
        if key not in seen:
            seen.add(key)
            errors.append({
                "file": m.group(1),
                "line": int(m.group(2)),
                "col": int(m.group(3)),
                "message": m.group(4).strip(),
            })

    for m in _LEAN_JSON_ERROR_RE.finditer(verify_text):
        key = (m.group(1), m.group(2), m.group(3))
        if key not in seen:
            seen.add(key)
            errors.append({
                "file": m.group(1),
                "line": int(m.group(2)),
                "col": int(m.group(3)),
                "message": m.group(4).strip(),
            })

    return errors


def _json_candidates(text: str) -> list[str]:
    """Return candidate JSON strings to try parsing, in priority order.

    1. The full text (LLM followed instructions exactly).
    2. From the first ``{`` to the last ``}`` (LLM prepended prose).
    3. Content inside a ```json ... ``` or ``` ... ``` fenced block.
    """
    candidates = [text]
    first_brace = text.find("{")
    last_brace = text.rfind("}")
    if first_brace != -1 and last_brace > first_brace:
        candidates.append(text[first_brace : last_brace + 1])
    import re as _re
    for m in _re.finditer(r"```(?:json)?\s*(\{.*?\})\s*```", text, _re.DOTALL):
        candidates.append(m.group(1))
    return candidates


def _classify_lean_error_structured(
    verify_text: str,
    target_file: str,
) -> tuple[str, list[dict]]:
    """Classifier of Lean build errors using structured error parsing.

    Returns (classification, errors) where classification is one of:
      SIGNATURE_HALLUCINATION  — unknown symbol in the *declaration zone* of target_file
                                 (not proof body) → full rewrite allowed.
      DEFINITION_ZONE_ERROR    — type mismatch in declaration/definition zone
                                 (before proof body) → verify callee signature first.
      DEPENDENCY_COMPILE_ERROR — first/primary errors originate in a non-target file
                                 (e.g. staging/import dep) → fix dep, do NOT rewrite target.
      LOCAL_PROOF_ERROR        — errors are in target but in proof body, or typeclass
                                 synthesis failures → patch only.
      PROOF_ERROR              — all other errors (type mismatch, unsolved goals, etc.).
    """
    errors = _parse_lean_errors(verify_text)

    # Duplicate declaration in target always corrupts the file.
    if _DUPLICATE_DECL_RE.search(verify_text):
        return "SIGNATURE_HALLUCINATION", errors

    if not errors:
        # No structured errors found — fall back to legacy line-threshold logic.
        has_unknown = bool(_UNKNOWN_SYMBOL_RE.search(verify_text))
        if not has_unknown:
            return "PROOF_ERROR", errors
        line_no = _extract_first_error_line(verify_text)
        if line_no is not None and line_no <= _PROOF_BODY_LINE_THRESHOLD:
            return "SIGNATURE_HALLUCINATION", errors
        return "LOCAL_PROOF_ERROR", errors

    # Normalise target path for comparison.  We use the full path to handle the
    # case where staging file and target share the same basename
    # (e.g. Lib/Glue/Staging/SVRGOuterLoop.lean vs Algorithms/SVRGOuterLoop.lean).
    def _is_target_file(error_file: str) -> bool:
        """True iff the error file refers to the target algorithm file."""
        ep = Path(error_file)
        tp = Path(target_file)
        # Full path match (normalised).
        if ep == tp:
            return True
        # Same name AND same directory-segment (Algorithms/).
        if ep.name == tp.name and "Algorithms" in str(ep):
            return True
        # Relative comparison after anchoring to project root.
        try:
            ep_rel = ep.relative_to(PROJECT_ROOT) if ep.is_absolute() else ep
            tp_rel = tp.relative_to(PROJECT_ROOT) if tp.is_absolute() else tp
            return ep_rel == tp_rel
        except ValueError:
            return ep.name == tp.name and "Staging" not in str(ep)

    target_errors = [e for e in errors if _is_target_file(e["file"])]
    dep_errors = [e for e in errors if not _is_target_file(e["file"])]

    # Primary errors come from a dependency/staging file — route to dep-fix branch.
    if dep_errors and not target_errors:
        return "DEPENDENCY_COMPILE_ERROR", errors

    # Even if some target errors exist, if the primary (first) error is in a dep, treat
    # as dependency compile error to avoid misrouting staging mistakes.
    if dep_errors and errors[0]["file"] and not _is_target_file(errors[0]["file"]):
        return "DEPENDENCY_COMPILE_ERROR", errors

    # All errors are in target — classify by message content and location.
    for e in target_errors:
        msg = e["message"]
        line = e["line"]

        if _DUPLICATE_DECL_RE.search(msg):
            return "SIGNATURE_HALLUCINATION", errors

        # Typeclass failure — always a proof-body problem.
        if _TYPECLASS_FAIL_RE.search(msg):
            return "LOCAL_PROOF_ERROR", errors

        # Type mismatch in declaration/definition zone usually means callee
        # signature misuse, not a local tactic issue.
        if _TYPE_MISMATCH_RE.search(msg):
            tgt_path = PROJECT_ROOT / target_file
            decl_zone_end = _get_decl_zone_end(tgt_path)
            if line <= decl_zone_end:
                return "DEFINITION_ZONE_ERROR", errors

        if _UNKNOWN_SYMBOL_RE.search(msg):
            # Only SIGNATURE_HALLUCINATION when error is in the declaration zone:
            # use target file content to determine where declarations end.
            tgt_path = PROJECT_ROOT / target_file
            decl_zone_end = _get_decl_zone_end(tgt_path)
            if line <= decl_zone_end:
                return "SIGNATURE_HALLUCINATION", errors
            return "LOCAL_PROOF_ERROR", errors

    return "PROOF_ERROR", errors


def _get_decl_zone_end(tgt_path: Path) -> int:
    """Return the last line number of the declaration zone in a Lean file.

    The declaration zone is everything up to (and including) the line where
    the first proof body begins — i.e. the first ':= by' or ':= ' that starts
    a proof.  Falls back to _PROOF_BODY_LINE_THRESHOLD if file is unreadable.
    """
    if not tgt_path.exists():
        return _PROOF_BODY_LINE_THRESHOLD
    try:
        lines = tgt_path.read_text(encoding="utf-8").splitlines()
    except OSError:
        return _PROOF_BODY_LINE_THRESHOLD

    # Find the first theorem/lemma/def declaration, then track until the proof body.
    in_decl = False
    for i, line in enumerate(lines, start=1):
        stripped = line.strip()
        if re.match(r"^(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev)\s", stripped):
            in_decl = True
        if in_decl and re.search(r":=\s*by\b|:=\s*$", line):
            return i
    return _PROOF_BODY_LINE_THRESHOLD


def _is_target_file_error(error_file: str, target_file: str) -> bool:
    """Return True iff an error file path refers to the target algorithm file."""
    ep = Path(error_file)
    tp = Path(target_file)
    if ep == tp:
        return True
    if ep.name == tp.name and "Algorithms" in str(ep):
        return True
    try:
        ep_rel = ep.relative_to(PROJECT_ROOT) if ep.is_absolute() else ep
        tp_rel = tp.relative_to(PROJECT_ROOT) if tp.is_absolute() else tp
        return ep_rel == tp_rel
    except ValueError:
        return ep.name == tp.name and "Staging" not in str(ep)


def _classify_lean_error(verify_text: str, target_file: str = "") -> str:
    """Backwards-compatible wrapper around _classify_lean_error_structured."""
    classification, _ = _classify_lean_error_structured(verify_text, target_file)
    return classification


def _extract_imported_algo_sigs(target_file: str) -> str:
    """Return a compact API-signature block for every Algorithms/*.lean file
    imported by *target_file*.

    Strategy: for each top-level declaration (def/theorem/lemma/abbrev) collect
    lines until the first blank line **or** the start of a new top-level keyword.
    Proof bodies are stripped by stopping before any line that begins (after
    optional leading spaces) with ``| `` (pattern-match arm) or ``by`` at the
    same indentation as ``:=``.  This is robust to multi-line signatures and
    one-liner ``:= expr`` forms alike.
    """
    tgt_path = PROJECT_ROOT / target_file
    if not tgt_path.exists():
        return ""

    content = tgt_path.read_text(encoding="utf-8")
    imported_algos = re.findall(r"^import Algorithms\.(\w+)", content, re.MULTILINE)
    if not imported_algos:
        return ""

    sections: list[str] = []
    for algo in imported_algos:
        algo_path = PROJECT_ROOT / f"Algorithms/{algo}.lean"
        if not algo_path.exists():
            continue
        algo_lines = algo_path.read_text(encoding="utf-8").splitlines()
        sigs: list[str] = []
        i = 0
        while i < len(algo_lines):
            line = algo_lines[i]
            if not _DECL_START.match(line):
                i += 1
                continue
            # Start of a declaration — collect signature lines.
            sig: list[str] = [line]
            j = i + 1
            while j < len(algo_lines):
                next_line = algo_lines[j]
                # Stop at blank line or new top-level keyword.
                if next_line.strip() == "" or _TOP_LEVEL_KEYWORDS.match(next_line):
                    break
                # Stop before proof body lines (by / := by / pattern arms).
                stripped = next_line.lstrip()
                if stripped.startswith("| ") or re.match(r"^\s*by\b", next_line):
                    break
                sig.append(next_line)
                j += 1
            # Drop trailing `:= ...` one-liner body if present.
            sig_text = "\n".join(sig)
            # Keep only up to `:=` to drop trivial proof bodies.
            if ":=" in sig_text:
                sig_text = sig_text[: sig_text.index(":=")].rstrip()
            if sig_text.strip():
                sigs.append(sig_text)
            i = j

        if sigs:
            sections.append(
                f"-- Algorithms/{algo}.lean --\n" + "\n\n".join(sigs)
            )

    if not sections:
        return ""
    return (
        "## Auto-injected API signatures from imported algorithm files\n\n"
        + "\n\n".join(sections)
    )


def _extract_staging_sigs(staging_path: "Path") -> str:
    """Return a compact signature block for all theorem/lemma/def in a staging file.

    Reuses the same parsing logic as _extract_imported_algo_sigs: collect declaration
    lines until proof body, strip at `:=`. Generic — works for any staging file.
    """
    try:
        rel = (
            str(staging_path.relative_to(PROJECT_ROOT))
            if staging_path.is_absolute()
            else str(staging_path)
        )
        content = snapshot_file(rel)
    except Exception:  # noqa: BLE001
        return ""
    if not content:
        return ""
    algo_lines = content.splitlines()
    sigs: list[str] = []
    i = 0
    while i < len(algo_lines):
        line = algo_lines[i]
        if not _DECL_START.match(line):
            i += 1
            continue
        sig: list[str] = [line]
        j = i + 1
        while j < len(algo_lines):
            next_line = algo_lines[j]
            if next_line.strip() == "" or _TOP_LEVEL_KEYWORDS.match(next_line):
                break
            stripped = next_line.lstrip()
            if stripped.startswith("| ") or re.match(r"^\s*by\b", next_line):
                break
            sig.append(next_line)
            j += 1
        sig_text = "\n".join(sig)
        if ":=" in sig_text:
            sig_text = sig_text[: sig_text.index(":=")].rstrip()
        if sig_text.strip():
            sigs.append(sig_text)
        i = j
    if not sigs:
        return ""
    staging_rel = str(staging_path.relative_to(PROJECT_ROOT)) if PROJECT_ROOT in staging_path.parents else str(staging_path)
    return (
        f"## Staging lemma signatures (auto-extracted from {staging_rel})\n\n"
        + "\n\n".join(sigs)
        + "\n\n"
    )


def _extract_first_error_line(verify_text: str) -> int | None:
    """Return the line number of the first Lean compiler error, or None.

    Handles both standard format (file:line:col: error:) and
    Lake JSON format (error: file:line:col:) via two capture groups.
    """
    m = _LEAN_ERROR_LINE_RE.search(verify_text)
    if not m:
        return None
    # group(1): standard format, group(2): Lake JSON format
    raw = m.group(1) or m.group(2)
    return int(raw) if raw else None


def _format_agent3_tool_feedback(
    exec_results: list,
    verify_result: dict,
    target_file: str,
    current_code: str,
) -> str:
    """Format tool execution results for Agent3 to analyze and fix."""
    exit_code = int(verify_result.get("exit_code", 1))
    sorry_count = int(verify_result.get("sorry_count", 0))
    errors = verify_result.get("errors", [])
    err_text = "\n".join(errors) if isinstance(errors, list) else str(errors)
    warnings = verify_result.get("warnings", [])
    warn_text = "\n".join(warnings) if isinstance(warnings, list) else str(warnings)
    parts = [
        "## Tool execution results",
        "",
        f"run_lean_verify({target_file}) returned:",
        f"- exit_code: {exit_code}",
        f"- sorry_count: {sorry_count}",
        "",
        "### Build errors (compiler errors with file:line:col)",
        "```",
        err_text[:6000] if err_text else "(no errors)",
        "```",
    ]
    if warn_text:
        parts.extend([
            "",
            "### Warnings (for context only — do not fix unless directly related)",
            "```",
            warn_text[:1500],
            "```",
        ])
    parts.extend([
        "",
        "Analyze the errors above. Each error line shows file:line:col and the issue "
        "(e.g. unknown identifier, wrong API, type mismatch). "
        "Fix using edit_file_patch, then call run_lean_verify. "
        "Output tool_calls with your fix.",
    ])
    failed_tools = [r for r in exec_results if r.status_code not in ("SUCCESS",)]
    if failed_tools:
        parts.extend([
            "",
            "### Other tool results",
            *[f"- {r.message}" for r in failed_tools],
        ])
    parts.extend([
        "",
        f"### Current file ({target_file})",
        "```lean",
        current_code[:10000] if current_code else "(empty)",
        "```",
    ])
    return "\n".join(parts)


def _lint_staging_content(staging_text: str) -> list[tuple[str, str]]:
    """Run the staging API lint pass on staging file content.

    Returns a list of (wrong_pattern, correction_hint) pairs for each violation found.
    An empty list means the content passed all lint checks.
    """
    violations: list[tuple[str, str]] = []
    for pattern, hint in _STAGING_API_MISSPELLINGS.items():
        if re.search(pattern, staging_text):
            violations.append((pattern.strip(r"\b"), hint))
    return violations


def _format_staging_lint_feedback(
    violations: list[tuple[str, str]],
    staging_file: str,
) -> str:
    """Format staging lint violations into an actionable Agent3 feedback message."""
    lines = [
        "## ⚠ STAGING FILE API LINT VIOLATIONS",
        f"The following known API misspellings were detected in {staging_file}:",
        "",
    ]
    for wrong, hint in violations:
        lines.append(f"  - `{wrong}` → correct form: `{hint}`")
    lines += [
        "",
        "These misspellings WILL cause Lean compilation errors.",
        "Fix each occurrence in the staging file BEFORE calling run_lean_verify.",
        "Use edit_file_patch with <<<SEARCH>>>/<<<REPLACE>>> targeting the staging file.",
    ]
    return "\n".join(lines)


def _check_patch_symbols(
    arguments: dict,
    registry: "ToolRegistry",
) -> str | None:
    """Pre-flight check for identifiers in an edit_file_patch REPLACE block.

    Extracts identifiers from the REPLACE text that look like external Lean API
    names (dotted namespace.name or snake_case ≥2 segments).  For each name not
    found in a local-variable whitelist, runs a search_codebase query.

    Returns a warning string if any significant identifiers are unverifiable
    (search returns empty), or None if all checks pass / no suspicious names found.
    The return value is injected as a feedback message to Agent3 BEFORE the patch
    is applied so Agent3 can self-correct.
    """
    # The argument key for the replace text varies: 'new_str', 'replace', 'content'.
    replace_text = (
        arguments.get("new_str")
        or arguments.get("replace")
        or arguments.get("content")
        or ""
    )
    if not replace_text:
        return None

    # Collect identifiers from REPLACE blocks (<<<REPLACE>>> ... <<<END>>>).
    replace_blocks = re.findall(
        r"<<<REPLACE>>>(.*?)<<<END>>>", replace_text, re.DOTALL
    )
    search_text = "\n".join(replace_blocks) if replace_blocks else replace_text

    # Dotted namespace.name identifiers.
    dotted = re.findall(r"\b[\w]+(?:\.[\w]+)+\b", search_text)
    # Snake_case project lemma names.
    snake = [
        m for m in _PROJECT_IDENT_RE.findall(search_text)
        if m not in _LEAN_KEYWORDS
    ]
    candidates = list(dict.fromkeys(dotted + snake))  # deduplicate, preserve order

    # Whitelist: names that are obviously local or Lean builtins.
    _local_re = re.compile(r"^[a-z]$|^h\d*$|^ih\w*$|^x\w*$|^f\w*$|^n\w*$|^i\w*$")
    candidates = [c for c in candidates if not _local_re.match(c)]

    if not candidates:
        return None

    missing: list[str] = []
    for name in candidates[:8]:  # limit to first 8 to avoid excessive API calls
        try:
            result = registry.call("search_codebase", query=name)
            result_text = str(result)
            if not result_text or result_text.strip() in ("", "[]", "null", "{}"):
                missing.append(name)
        except Exception:  # noqa: BLE001
            pass  # search failure is not a blocker

    if not missing:
        return None

    return (
        "## ⚠ PATCH SYMBOL PRE-CHECK WARNING\n"
        "The following identifiers in your REPLACE block could NOT be found "
        f"in the codebase via search_codebase: {', '.join(missing)}\n\n"
        "BEFORE applying this patch:\n"
        "1. Call search_codebase for each name above to find the correct API.\n"
        "2. Replace unverified names with the verified alternatives.\n"
        "3. Then re-issue your edit_file_patch with the corrected REPLACE.\n\n"
        "If these are local binders or names defined in the current file, "
        "you may ignore this warning and proceed."
    )


def _prioritize_error_text(
    structured_errors: list[dict],
    raw_text: str,
    last_edit_line: int | None,
    target_file: str,
    max_chars: int = 4000,
) -> str:
    """Return a compact, priority-sorted error string.

    Replaces bare ``last_verify_text[:N]`` truncation with an ordered view:
    1. Errors near the last edited line (±10 lines) — highest signal
    2. Errors in the target file
    3. Errors in the staging file
    4. All other dependency errors

    When structured_errors is empty, falls back to raw_text[:max_chars].
    """
    if not structured_errors:
        return raw_text[:max_chars]

    target_basename = Path(target_file).name

    def _priority(e: dict) -> tuple[int, int]:
        efile = Path(e["file"]).name
        eline = e["line"]
        near_edit = (
            last_edit_line is not None
            and abs(eline - last_edit_line) <= 10
        )
        is_target = efile == target_basename and "Staging" not in e["file"]
        is_staging = "Staging" in e["file"]
        tier = 0 if near_edit else (1 if is_target else (2 if is_staging else 3))
        return (tier, eline)

    sorted_errors = sorted(structured_errors, key=_priority)

    lines: list[str] = []
    for e in sorted_errors:
        line = f"{e['file']}:{e['line']}:{e['col']}: error: {e['message']}"
        lines.append(line)

    combined = "\n".join(lines)
    if len(combined) <= max_chars:
        return combined

    # Truncate: keep as many full error lines as fit within max_chars.
    kept: list[str] = []
    chars = 0
    truncated = 0
    for ln in lines:
        if chars + len(ln) + 1 > max_chars - 40:
            truncated += 1
        else:
            kept.append(ln)
            chars += len(ln) + 1
    result = "\n".join(kept)
    if truncated:
        result += f"\n... ({truncated} lower-priority errors truncated)"
    return result


def _infer_failure_class(error_type: str, message: str) -> str:
    """Map an error type + message to a human-readable failure class for history."""
    if error_type == "DEPENDENCY_COMPILE_ERROR":
        return "SymbolMissing"
    if error_type == "DEFINITION_ZONE_ERROR":
        return "DefinitionMismatch"
    if error_type == "SIGNATURE_HALLUCINATION":
        return "Structural"
    msg = message.lower()
    if "type mismatch" in msg:
        return "TypeMismatch"
    if "unsolved goals" in msg:
        return "TacticFail"
    if "no goals" in msg:
        return "ExcessGoal"
    if "unknown identifier" in msg or "unknown constant" in msg:
        return "UnknownIdent"
    return "Tactical"


def _llm_classify_error(
    primary_error: dict,
    file_context: str,
    target_file: str,
) -> dict:
    """Call LLM to classify error into locus, nature, suggested_strategy.

    Returns {"locus": str, "nature": str, "suggested_strategy": str, "reasoning": str}.
    Falls back to legacy _infer_failure_class-style values if LLM fails or times out.
    """
    from concurrent.futures import ThreadPoolExecutor, TimeoutError as FuturesTimeoutError

    cfg = AGENT_CONFIGS.get("planner", AGENT_CONFIGS.get("diagnostician", {}))
    provider = cfg.get("provider", "qwen")
    model = cfg.get("model", "qwen3.5-plus")
    max_tokens = cfg.get("max_tokens", 2048)

    prompt = build_error_classification_prompt(primary_error, file_context, target_file)

    def _call() -> str:
        return call_llm(
            provider,
            model,
            "You are a Lean 4 error classifier. Reply with JSON only.",
            [{"role": "user", "content": prompt}],
            max_tokens=max_tokens,
        )

    try:
        with ThreadPoolExecutor(max_workers=1) as ex:
            fut = ex.submit(_call)
            raw = fut.result(timeout=15)
    except (FuturesTimeoutError, Exception) as exc:
        fallback = _infer_failure_class(
            "PROOF_ERROR", primary_error.get("message", "")
        )
        return {
            "locus": "proof_body",
            "nature": "other",
            "suggested_strategy": "other",
            "reasoning": f"LLM classification failed ({exc!r}); fallback to legacy.",
        }

    # Parse JSON from response
    raw = raw.strip()
    for candidate in _json_candidates(raw):
        try:
            obj = json.loads(candidate)
            if isinstance(obj, dict):
                return {
                    "locus": str(obj.get("locus", "proof_body")),
                    "nature": str(obj.get("nature", "other")),
                    "suggested_strategy": str(obj.get("suggested_strategy", "other")),
                    "reasoning": str(obj.get("reasoning", "")),
                }
        except json.JSONDecodeError:
            continue
    return {
        "locus": "proof_body",
        "nature": "other",
        "suggested_strategy": "other",
        "reasoning": "LLM returned invalid JSON; fallback.",
    }


def _should_route_to_agent6_for_infra(
    last_verify_text: str,
    target_file: str,
    structured_errors: list[dict],
    tool_turn: int,
    last_local_error_sig: str | None,
) -> tuple[bool, str]:
    """Decide if we should auto-route to Agent6 for an infra gap.

    Returns (should_route, diagnosis). Trigger when:
    1. Error looks like infra-only (add_lemma / add_glue_lemma or pattern match)
    2. We need to solve now (repeated error or turn >= min)

    Uses pattern detection first; LLM fallback when uncertain.
    """
    from orchestrator.config import RETRY_LIMITS

    repeat_threshold = RETRY_LIMITS.get("AGENT6_AUTO_ROUTE_REPEAT_THRESHOLD", 2)
    min_turn = RETRY_LIMITS.get("AGENT6_AUTO_ROUTE_MIN_TURN", 3)

    # Build error signature: (file, line, first 200 chars of msg)
    primary = structured_errors[0] if structured_errors else {}
    err_sig = (
        f"{primary.get('file', '')}:{primary.get('line', 0)}:"
        f"{str(primary.get('message', ''))[:200]}"
    )
    is_repeated = last_local_error_sig is not None and err_sig == last_local_error_sig
    turn_ok = tool_turn >= min_turn

    # Need to solve now: same error repeated OR we're past min turn
    need_now = is_repeated or turn_ok

    if not need_now:
        return False, ""

    # Infra detection: pattern-based first
    _EXPECTED_TYPE_GOT_RE = re.compile(r"expected\s+type\s+.*\s+but\s+got", re.IGNORECASE)
    _APP_MISMATCH_RE = re.compile(
        r"application\s*(?:type\s+)?mismatch|type\s+mismatch",
        re.IGNORECASE,
    )
    _OMEGA_E_TYPE_RE = re.compile(r"\b(?:Ω|omega)\s*(?:→|->)\s*E\b|E\s*(?:→|->)\s*(?:Ω|omega)", re.IGNORECASE)
    _BRIDGE_KEYWORDS_RE = re.compile(
        r"\b(integral|fubini|measur|aestronglymeasurable|aemeasurable|expectation|condexp|bochner)\b",
        re.IGNORECASE,
    )
    _UNKNOWN_ID_LEMMA_LIKE_RE = re.compile(
        r"unknown identifier[^`]*`([a-zA-Z][a-zA-Z0-9_]*(?:\.[a-zA-Z][a-zA-Z0-9_]*)*)`",
        re.IGNORECASE,
    )
    # Exclude hypothesis-like names (h_xxx, hη, hL) — those are tactical
    _HYPOTHESIS_LIKE_RE = re.compile(r"^h[a-zA-Z0-9_]*$")
    # Local/binder-like identifiers (often tactical typos), including unicode subscripts
    _LOCAL_OR_UNICODE_IDENT_RE = re.compile(
        r"^[a-zA-Z](?:[a-zA-Z0-9']{0,2}|[₀₁₂₃₄₅₆₇₈₉]+|[a-zA-Z0-9']*[₀₁₂₃₄₅₆₇₈₉]+)$"
    )
    # External theorem/API-like identifier pattern
    _API_LIKE_RE = re.compile(r"(?:\.)|(?:_[a-zA-Z0-9_]+)")

    verify_lower = last_verify_text.lower()
    has_type_mismatch = bool(
        _EXPECTED_TYPE_GOT_RE.search(verify_lower) or _APP_MISMATCH_RE.search(verify_lower)
    )
    has_omega_e_bridge = bool(_OMEGA_E_TYPE_RE.search(last_verify_text))
    has_bridge_keywords = bool(_BRIDGE_KEYWORDS_RE.search(verify_lower))
    unknown_matches = list(_UNKNOWN_ID_LEMMA_LIKE_RE.finditer(last_verify_text))

    pattern_infra = False
    # Route type-mismatch to Agent6 only when it looks structural (bridge-level),
    # not purely tactical.
    if has_type_mismatch and (has_omega_e_bridge or has_bridge_keywords):
        pattern_infra = True
    for m in unknown_matches:
        ident = m.group(1)
        leaf = ident.split(".")[-1]
        if _HYPOTHESIS_LIKE_RE.match(leaf):
            continue
        if _LOCAL_OR_UNICODE_IDENT_RE.match(leaf):
            continue
        if _API_LIKE_RE.search(ident):
            pattern_infra = True
            break

    if pattern_infra:
        diag = (
            "Pattern: structural bridge mismatch (Ω/E, integral/measurability/expectation) "
            "or unknown external API-like identifier requiring glue lemma."
        )
        return True, diag

    # Optional LLM fallback for add_lemma / add_glue_lemma
    err_line = primary.get("line")
    try:
        file_ctx = _build_escalation_file_context(target_file, int(err_line) if err_line else None)
    except Exception:
        file_ctx = ""
    llm_result = _llm_classify_error(primary, file_ctx[:1500], target_file)
    strategy = (llm_result.get("suggested_strategy") or "").lower()
    if strategy in ("add_lemma", "add_glue_lemma"):
        return True, f"LLM: suggested_strategy={strategy}"

    return False, ""


def _get_reference_files_with_descriptions(target_file: str) -> list[tuple[str, str]]:
    """Merge universal refs (Lib/Glue, Layer0, Layer1, GLUE_TRICKS) + algorithm refs.

    Returns list of (path, description). Algorithm refs get description '(similar algorithm)'.
    """
    result: list[tuple[str, str]] = list(REFERENCE_FILES_WITH_DESCRIPTIONS)
    algo_refs = ALGORITHM_REFERENCES.get(
        Path(target_file).stem, _get_default_references(target_file)
    )
    seen: set[str] = {p for p, _ in result}
    for path in algo_refs:
        if path not in seen:
            seen.add(path)
            result.append((path, "(similar algorithm)"))
    return result


def _format_ref_and_classification_blocks(
    reference_files: list[tuple[str, str]],
    llm_classification: dict | None,
) -> str:
    """Format REFERENCE FILES and ERROR CLASSIFICATION blocks for Agent2 context."""
    parts: list[str] = []
    if reference_files:
        table_lines = [
            "| File | Purpose |",
            "|------|---------|",
        ]
        for path, desc in reference_files:
            table_lines.append(f"| {path} | {desc} |")
        parts.append(
            "## REFERENCE FILES (compare with working examples)\n"
            "Use search_codebase or read_file to fetch relevant sections.\n\n"
            + "\n".join(table_lines)
            + "\n"
        )
    if llm_classification:
        parts.append(
            "## ERROR CLASSIFICATION (from diagnostician)\n"
            f"Locus: {llm_classification['locus']} | Nature: {llm_classification['nature']} | "
            f"Suggested strategy: {llm_classification['suggested_strategy']}\n"
            f"Reasoning: {llm_classification['reasoning']}\n"
            "Follow the Cross-File Comparison Protocol. Use the suggested_strategy to choose "
            "your approach. For add_instance: suggest adding haveI/letI before the failing line. "
            "For compare_with_reference: use the reference files above.\n"
        )
    if parts:
        return "\n" + "\n".join(parts) + "\n"
    return ""


def _format_failed_approaches(approaches: list[dict]) -> str:
    """Format failed_approaches list for injection into Agent2 prompts."""
    if not approaches:
        return ""
    lines = [
        "[FAILED APPROACHES HISTORY — do NOT repeat these strategies]\n"
        "The following error signatures have already been seen in this run:"
    ]
    for a in approaches:
        lines.append(
            f"  Attempt {a['attempt']}: {a['failure_class']} @ "
            f"{Path(a['file']).name}:{a['line']} — {a['message_summary']}"
        )
    lines.append(
        "Choose a DIFFERENT approach. If you previously used a specific lemma or tactic "
        "that produced one of the above errors, use search_codebase to find an alternative."
    )
    return "\n".join(lines) + "\n\n"


def _extract_error_identifiers(error_text: str, limit: int = 8) -> list[str]:
    """Extract likely function/lemma identifiers from Lean error text."""
    if not error_text:
        return []
    candidates: list[str] = []
    patterns = [
        r"Function `([A-Za-z_]\w*)`",
        r"`([A-Za-z_]\w*)`",
        r"unknown (?:identifier|constant|theorem) ['`]?([A-Za-z_]\w*)['`]?",
    ]
    for pat in patterns:
        candidates.extend(re.findall(pat, error_text))
    seen: set[str] = set()
    out: list[str] = []
    for name in candidates:
        lname = name.lower()
        if (
            name in seen
            or len(name) < 3
            or lname in {"error", "line", "type", "function", "argument"}
        ):
            continue
        seen.add(name)
        out.append(name)
        if len(out) >= limit:
            break
    return out


def _infer_definition_file_from_registry(
    registry: "ToolRegistry",
    identifier: str,
    target_file: str,
) -> str | None:
    """Infer likely definition file for an identifier via search_codebase."""
    try:
        result = registry.call("search_codebase", query=identifier)
    except Exception:  # noqa: BLE001
        return None
    text = str(result or "")
    if not text:
        return None
    paths = re.findall(r"([A-Za-z0-9_./-]+\.lean)", text)
    if not paths:
        return None
    for p in paths:
        if Path(p).name != Path(target_file).name:
            return p
    return paths[0]


def _build_stale_error_hint(
    registry: "ToolRegistry",
    target_file: str,
    error_text: str,
    err_line_no: int | None,
    stale_count: int,
) -> str:
    """Build forced-read guidance when the same failing line repeats."""
    identifiers = _extract_error_identifiers(error_text, limit=1)
    ident = identifiers[0] if identifiers else "the called function"
    inferred = (
        _infer_definition_file_from_registry(registry, ident, target_file)
        if identifiers
        else None
    )
    suggested_read = (
        f'{{"tool": "read_file", "arguments": {{"path": "{inferred}"}}}}'
        if inferred
        else '{"tool": "search_codebase", "arguments": {"query": "<failing function name>"}}'
    )
    line_display = str(err_line_no) if err_line_no is not None else "unknown"
    return (
        "## STALE ERROR GUARD\n"
        f"Line {line_display} has failed {stale_count} consecutive verify turns unchanged.\n"
        f"Before editing again, you MUST read the definition of `{ident}` to confirm its exact signature.\n"
        "Repeated patching without reading dependency definitions will not converge.\n"
        f"Suggested next action: {suggested_read}\n"
    )


def _prequery_dependency_signatures(
    errors_text: str,
    target_file: str,
    max_symbols: int = 3,
) -> str:
    """Attach key dependency signatures extracted from recent Lean errors."""
    identifiers = _extract_error_identifiers(errors_text, limit=max_symbols * 2)
    if not identifiers:
        return ""

    candidate_files = [target_file] + AGENT_FILES.get("sorry_closer", [])
    seen_files: set[str] = set()
    lean_files: list[Path] = []
    for rel in candidate_files:
        if not isinstance(rel, str) or not rel.endswith(".lean"):
            continue
        if rel in seen_files:
            continue
        seen_files.add(rel)
        p = PROJECT_ROOT / rel
        if p.exists():
            lean_files.append(p)

    snippets: list[str] = []
    seen_syms: set[str] = set()
    for ident in identifiers:
        if ident in seen_syms:
            continue
        pat = re.compile(
            rf"^\s*(?:noncomputable\s+)?(?:def|theorem|lemma|abbrev|structure|class|instance)\s+{re.escape(ident)}\b"
        )
        found = False
        for fp in lean_files:
            try:
                lines = fp.read_text(encoding="utf-8").splitlines()
            except OSError:
                continue
            for i, ln in enumerate(lines):
                if not pat.match(ln):
                    continue
                start = max(0, i - 5)
                end = min(len(lines), i + 6)
                snippet = "\n".join(lines[start:end])
                rel = str(fp.relative_to(PROJECT_ROOT))
                snippets.append(f"-- Source: {rel}:{i + 1}\n{snippet}")
                seen_syms.add(ident)
                found = True
                break
            if found:
                break
        if len(snippets) >= max_symbols:
            break

    if not snippets:
        return ""
    return (
        "## Dependency Signatures (auto-extracted from errors)\n"
        + "\n\n".join(snippets)
        + "\n\n"
    )


def _generate_attempt_diagnosis(
    attempt: int,
    attempt_failures_current: list[dict],
    tools_used: set[str],
    registry: "ToolRegistry",
    target_file: str,
) -> str:
    """Generate deterministic attempt-level diagnosis summary for Agent2."""
    if not attempt_failures_current:
        return ""
    line_counts = Counter(
        int(a.get("line", -1))
        for a in attempt_failures_current
        if isinstance(a.get("line"), int) and int(a.get("line", -1)) > 0
    )
    persistent_line = None
    persistent_count = 0
    if line_counts:
        persistent_line, persistent_count = line_counts.most_common(1)[0]

    initial_sorry = int(attempt_failures_current[0].get("sorry_count", 0))
    final_sorry = int(attempt_failures_current[-1].get("sorry_count", 0))
    delta = final_sorry - initial_sorry
    primary_msg = str(attempt_failures_current[-1].get("message", ""))[:120]
    identifiers = _extract_error_identifiers(primary_msg, limit=1)
    ident = identifiers[0] if identifiers else "unknown"
    inferred = (
        _infer_definition_file_from_registry(registry, ident, target_file)
        if identifiers
        else None
    )
    inferred_display = inferred or "(unresolved)"
    line_display = str(persistent_line) if persistent_line is not None else "unknown"
    tools_display = ", ".join(sorted(tools_used)) if tools_used else "(none recorded)"
    return (
        f"[ATTEMPT {attempt} DIAGNOSIS]\n"
        f"- Persistent error: line {line_display} appeared {persistent_count}/{len(attempt_failures_current)} failing verifies "
        f"(latest: {primary_msg or 'n/a'})\n"
        f"- Sorry trajectory: {initial_sorry} -> {final_sorry} (net change: {delta:+d})\n"
        f"- Approaches tried (tools): {tools_display}\n"
        f"- Recommended focus: read definition of `{ident}` in {inferred_display} before next patch.\n\n"
    )


def _prequery_sorry_goals(
    registry: "ToolRegistry",
    target_file: str,
    guidance: str,
    goal_cache: dict,
    staging_has_errors: bool,
    errors_text: str = "",
) -> str:
    """Query Lean LSP for proof goals at all sorry locations in the target file.

    Primary source: directly scan the target file for lines containing `sorry`
    (excluding commented-out lines).  This guarantees goal injection regardless
    of whether Agent2 mentioned specific line numbers in its guidance.

    Secondary source: extract line numbers from the guidance text and merge
    them (deduped) with the file-scan results.

    Degradation conditions (any one triggers a skip for that line):
    - staging_has_errors is True (staging file broken → elaboration will fail)
    - get_lean_goal returns error field non-None
    - elapsed_s > 90

    The cache key is (target_file, sorry_line, file_content_hash) so repeated
    calls on an unchanged file cost 0 extra elaboration time.
    """
    if staging_has_errors:
        return ""

    tgt_path = PROJECT_ROOT / target_file
    if not tgt_path.exists():
        return ""

    current_hash = _file_hash(target_file)

    # Primary source: scan the file directly for sorry lines.
    # Skip lines that are pure comments (start with --).
    try:
        file_lines = tgt_path.read_text(encoding="utf-8").splitlines()
        file_sorry_lines = [
            i + 1
            for i, ln in enumerate(file_lines)
            if re.search(r"\bsorry\b", ln) and not ln.strip().startswith("--")
        ]
    except OSError:
        file_sorry_lines = []

    # Secondary source: extract line numbers from guidance text.
    # "line 305", "Line 305:", "sorry at 305", "line numbers: 305, 307"
    raw_lines = re.findall(
        r"(?:line|sorry\s+at|sorry(?:\s+on)?)\s+(\d+)",
        guidance,
        re.IGNORECASE,
    )
    raw_lines += re.findall(r"\bsorry\b.*?(\d{2,4})\b", guidance, re.IGNORECASE)
    guidance_sorry_lines = [int(x) for x in raw_lines if 1 <= int(x) <= 9999]

    # Merge: file-scan first (deterministic ordering), guidance as supplement.
    sorry_lines = list(dict.fromkeys(file_sorry_lines + guidance_sorry_lines))

    dep_block = _prequery_dependency_signatures(errors_text, target_file)
    if not sorry_lines:
        return dep_block

    results: list[str] = []
    for line in sorry_lines[:6]:  # cap at 6 lines to limit total LSP time
        cache_key = (target_file, line, current_hash or "")
        if cache_key in goal_cache:
            cached = goal_cache[cache_key]
        else:
            try:
                result = registry.call("get_lean_goal", file_path=target_file, sorry_line=line)
            except Exception:  # noqa: BLE001
                continue
            goal_cache[cache_key] = result
            cached = result

        if cached.get("error") or not cached.get("goal"):
            continue
        if cached.get("elapsed_s", 0) > 90:
            continue

        goal_text = cached["goal"]
        hyps = cached.get("hypotheses", [])
        entry = f"Line {line}: {goal_text}"
        if hyps:
            hyp_str = "; ".join(hyps[:6])
            entry += f"\n  Hypotheses: {hyp_str}"
        results.append(entry)

    if not results:
        return dep_block

    header = "## Pre-queried Lean Goal States (from LSP — authoritative)\n"
    header += "Use these exact types when formulating `have` steps.\n"
    body = "\n".join(results)
    return header + body + "\n\n" + dep_block


def _retrieve_catalog_context(
    query_terms: list[str],
    catalog_path: Path | None = None,
    max_entries: int = 3,
    max_chars: int = 1200,
) -> str:
    """Retrieve the top-matching CATALOG.md lemma entries for query_terms.

    Splits CATALOG.md on ``####`` headings, scores each entry by the sum of
    term occurrence counts (case-insensitive), returns the top ``max_entries``
    formatted entries concatenated and truncated to ``max_chars``.

    Returns an empty string when CATALOG.md is missing, unreadable, or no
    terms match any entry.
    """
    if catalog_path is None:
        catalog_path = PROJECT_ROOT / "docs" / "CATALOG.md"
    try:
        content = catalog_path.read_text(encoding="utf-8")
    except OSError:
        return ""

    if not query_terms:
        return ""

    # Split into lemma entries by the `####` heading marker.
    raw_entries = re.split(r"(?=^####\s)", content, flags=re.MULTILINE)
    entries: list[tuple[int, str]] = []  # (score, text)
    for entry in raw_entries:
        if not entry.strip() or not entry.startswith("####"):
            continue
        score = sum(
            len(re.findall(re.escape(term), entry, re.IGNORECASE))
            for term in query_terms
        )
        if score > 0:
            entries.append((score, entry.strip()))

    if not entries:
        return ""

    entries.sort(key=lambda x: x[0], reverse=True)
    top = entries[:max_entries]

    block = "## Relevant CATALOG entries (auto-retrieved)\n"
    remaining = max_chars - len(block)
    for _, text in top:
        chunk = text[:remaining]
        block += chunk + "\n\n"
        remaining -= len(chunk) + 2
        if remaining <= 0:
            break

    return block.rstrip()


def _extract_symbol_manifest(plan: str) -> list[dict]:
    """Parse symbol_manifest from the JSON block embedded in Agent2's plan.

    Returns an empty list when the block is absent or unparseable.
    """
    match = re.search(r"```json\s*(\{.*?\})\s*```", plan, re.DOTALL)
    if not match:
        return []
    try:
        data = json.loads(match.group(1))
        return data.get("symbol_manifest", [])
    except json.JSONDecodeError:
        return []


@dataclass
class ExecutionResult:
    """Result envelope for each Agent3 tool execution."""

    status_code: str  # SUCCESS / ERROR / BLOCKED
    message: str
    attempt: int = 0


_SUBGRADIENT_CONTEXT = """

## Note: subdifferential symbols (Mathlib 4.28+)

`Mathlib.Analysis.Convex.Subdifferential` has been REMOVED in Mathlib 4.28.
Do NOT add `import Mathlib.Analysis.Convex.Subdifferential` — this module no longer exists.
Instead, define these symbols locally in your algorithm file, placed AFTER `end <SetupNamespace>`:

  def subdifferential (_ : Type*) (f : E → ℝ) (w : E) : Set E :=
    {g : E | ∀ y : E, f y ≥ f w + ⟪g, y - w⟫_ℝ}

  theorem mem_subdifferential_iff {f : E → ℝ} {w g : E} :
      g ∈ subdifferential ℝ f w ↔ ∀ y : E, f y ≥ f w + ⟪g, y - w⟫_ℝ := Iff.rfl

Mark these as LOCAL in symbol_manifest, NOT as VERIFIED from Mathlib.
"""

_SYMBOL_WHITELIST: frozenset[str] = frozenset()


class Gate4Error(RuntimeError):
    """Raised by phase4_persist when Used-in docstring tags are absent.

    Carries ``missing`` as a structured list so the catch site never needs
    to parse a string representation.
    """

    def __init__(self, missing: list[str]) -> None:
        self.missing = missing
        super().__init__(f"[Gate 4] Missing Used-in tags: {missing}")


def _collect_lib_declaration_names() -> set[str]:
    """Collect theorem/lemma/def names under Lib/ for alignment checks."""
    lib_root = PROJECT_ROOT / "Lib"
    names: set[str] = set()
    if not lib_root.exists():
        return names
    for lean_file in lib_root.rglob("*.lean"):
        try:
            content = lean_file.read_text(encoding="utf-8")
        except OSError:
            continue
        names.update(_LIB_DECL_RE.findall(content))
    return names


def _extract_catalog_lemma_names(content: str) -> list[str]:
    """Extract catalog lemma headings from a markdown patch fragment."""
    return _CATALOG_LEMMA_HEADING_RE.findall(content)


# ---------------------------------------------------------------------------
# Git baseline helpers
# ---------------------------------------------------------------------------

def _file_hash(path: str | Path) -> str | None:
    """Return MD5 hex-digest of *path*, or None if the file does not exist."""
    try:
        content = load_file(path)
    except FileNotFoundError:
        return None
    return hashlib.md5(content.encode("utf-8")).hexdigest()


def _git_diff_files() -> set[str]:
    """Return tracked files with unstaged/staged modifications."""
    result = subprocess.run(
        ["git", "diff", "--name-only"],
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
    )
    return set(result.stdout.splitlines())


def _git_untracked_files() -> set[str]:
    """Return untracked files in the repository."""
    result = subprocess.run(
        ["git", "ls-files", "--others", "--exclude-standard"],
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
    )
    return set(result.stdout.splitlines())


def _capture_lean_baseline() -> tuple[set[str], set[str]]:
    """Capture pre-run Lean file baseline without mutating git state."""
    tracked = {f for f in _git_diff_files() if f.endswith(".lean")}
    untracked = {f for f in _git_untracked_files() if f.endswith(".lean")}
    return tracked, untracked


@dataclass
class GitRunSnapshot:
    """Git snapshot captured at run start for safe rollback."""

    start_sha: str
    pre_run_dirty: bool
    stash_used: bool
    stash_ref: str | None


def _git_head_sha() -> str:
    """Return current HEAD commit SHA."""
    result = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    return result.stdout.strip()


def _git_is_dirty() -> bool:
    """Return True when tracked or untracked changes are present."""
    result = subprocess.run(
        ["git", "status", "--porcelain"],
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    return bool(result.stdout.strip())


def _capture_git_run_snapshot(run_id: str) -> GitRunSnapshot:
    """Capture HEAD and optionally stash local dirt for rollback safety."""
    start_sha = _git_head_sha()
    pre_run_dirty = _git_is_dirty()
    if not pre_run_dirty:
        return GitRunSnapshot(
            start_sha=start_sha,
            pre_run_dirty=False,
            stash_used=False,
            stash_ref=None,
        )

    # Save all local modifications (tracked + untracked) so run rollback can
    # safely reset and then restore user state.
    stash_msg = f"orchestrator-pre-run-{run_id}"
    subprocess.run(
        ["git", "stash", "push", "-u", "-m", stash_msg],
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    return GitRunSnapshot(
        start_sha=start_sha,
        pre_run_dirty=True,
        stash_used=True,
        stash_ref="stash@{0}",
    )


def _restore_snapshot_on_success(snapshot: GitRunSnapshot) -> None:
    """Restore pre-run user state after successful run."""
    if not snapshot.stash_used:
        return
    subprocess.run(
        ["git", "stash", "pop", "--index", snapshot.stash_ref or "stash@{0}"],
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )


def _rollback_to_snapshot(snapshot: GitRunSnapshot) -> None:
    """Rollback workspace to run-start commit and restore pre-run dirt."""
    subprocess.run(
        ["git", "reset", "--hard", snapshot.start_sha],
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    # Remove untracked files generated during this run.
    subprocess.run(
        ["git", "clean", "-fd"],
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    if snapshot.stash_used:
        subprocess.run(
            ["git", "stash", "pop", "--index", snapshot.stash_ref or "stash@{0}"],
            cwd=PROJECT_ROOT,
            capture_output=True,
            text=True,
            check=True,
        )


def _get_modified_lean_files(
    baseline_tracked: set[str],
    baseline_untracked: set[str],
) -> list[str]:
    """Return Lean files changed since run start, excluding pre-existing dirt."""
    tracked_now = {f for f in _git_diff_files() if f.endswith(".lean")}
    untracked_now = {f for f in _git_untracked_files() if f.endswith(".lean")}

    newly_tracked = tracked_now - baseline_tracked
    newly_untracked = untracked_now - baseline_untracked
    baseline_untracked_promoted = tracked_now & baseline_untracked

    return sorted(newly_tracked | newly_untracked | baseline_untracked_promoted)


def _ensure_algorithm_in_lakefile(algorithm: str) -> bool:
    """Ensure Algorithms.<algorithm> is listed in lakefile.lean's SGDAlgorithms roots.

    If the module is already present this is a no-op and returns False.  If it
    is absent it is appended to the end of the roots list so ``lake build
    SGDAlgorithms`` includes the newly-created file and returns True.
    """
    lakefile = PROJECT_ROOT / "lakefile.lean"
    if not lakefile.exists():
        console.print(f"[yellow][lakefile] lakefile.lean not found — skipping auto-update")
        return False

    module_name = f"`Algorithms.{algorithm}"
    content = lakefile.read_text(encoding="utf-8")

    if module_name in content:
        return False  # already registered — no-op

    # Find the closing bracket of the SGDAlgorithms roots list and insert before it.
    # Pattern matches the last backtick-module entry in the roots := #[...] block.
    roots_re = re.compile(
        r"(lean_lib SGDAlgorithms.*?roots\s*:=\s*#\[)(.*?)(\])",
        re.DOTALL,
    )
    m = roots_re.search(content)
    if not m:
        console.print(
            "[yellow][lakefile] Could not find SGDAlgorithms roots list — "
            "please add the module manually."
        )
        return False

    updated = content[: m.start(3)] + f", {module_name}" + content[m.start(3) :]
    lakefile.write_text(updated, encoding="utf-8")
    console.print(f"[green][lakefile] Added {module_name} to SGDAlgorithms roots.")
    return True


def _remove_algorithm_from_lakefile(algorithm: str) -> None:
    """Remove Algorithms.<algorithm> from lakefile.lean SGDAlgorithms roots (rollback).

    Called when a pipeline run fails or is interrupted to undo the temporary
    registration added at the start of Phase 3.
    """
    lakefile = PROJECT_ROOT / "lakefile.lean"
    if not lakefile.exists():
        return

    module_name = f"`Algorithms.{algorithm}"
    content = lakefile.read_text(encoding="utf-8")
    if module_name not in content:
        return

    # Try removing ", `Algorithms.X" (module was appended after existing entries).
    updated = re.sub(r",\s*" + re.escape(module_name), "", content)
    if updated == content:
        # Fallback: module appears first — remove "`Algorithms.X, " or "`Algorithms.X".
        updated = re.sub(re.escape(module_name) + r",?\s*", "", content)

    lakefile.write_text(updated, encoding="utf-8")
    console.print(f"[yellow][lakefile] Removed {module_name} from SGDAlgorithms roots (rollback).")


def _parse_persister_json(raw: str) -> list:
    """Robustly parse Agent4 JSON output. Strips markdown blocks, tolerates trailing text.
    Coerces a bare JSON object into a single-element list for forward compatibility."""
    text = raw.strip()
    # Step 1: Strip markdown code block if present.
    match = re.search(r'```(?:json)?\s*(.*?)\s*```', text, re.DOTALL)
    if match:
        text = match.group(1).strip()
    text = text.strip()
    if not text:
        raise ValueError("Persister output is empty")
    # Step 2: If text doesn't start with { or [, find first occurrence (Agent4 may return prose before JSON)
    start_idx = 0
    for i, c in enumerate(text):
        if c in ('{', '['):
            start_idx = i
            break
    else:
        raise ValueError("No JSON object or array found in persister output")
    # Step 3: Parse from the first { or [
    decoder = json.JSONDecoder()
    obj, _ = decoder.raw_decode(text, start_idx)
    # Step 4: Coerce bare object to list (Agent4 sometimes returns a single op as an object)
    if isinstance(obj, dict):
        obj = [obj]
    return obj


# ---------------------------------------------------------------------------
# Agent2 guided lookup helper
# ---------------------------------------------------------------------------

def _extract_new_identifiers_from_guidance(guidance: str) -> list[str]:
    """Extract identifiers from a guidance/patch block that look like Lean API names.

    Returns names that are likely external references (not local variables/binders):
    - Contain a dot (namespace separator) or
    - Are snake_case with ≥2 segments and not in _LEAN_KEYWORDS.
    """
    # Collect all identifiers from <<<REPLACE>>> sections first (highest signal).
    replace_blocks: list[str] = re.findall(
        r"<<<REPLACE>>>(.*?)<<<END>>>", guidance, re.DOTALL
    )
    search_space = "\n".join(replace_blocks) if replace_blocks else guidance

    # Dotted names (Lean namespace.lemma style).
    dotted = re.findall(r"\b[\w]+(?:\.[\w]+)+\b", search_space)
    # Snake_case project lemma names (≥2 segments, not keywords).
    snake = [
        m for m in _PROJECT_IDENT_RE.findall(search_space)
        if m not in _LEAN_KEYWORDS
    ]
    seen: set[str] = set()
    result: list[str] = []
    for name in dotted + snake:
        if name not in seen:
            seen.add(name)
            result.append(name)
    return result


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

def _execute_single_tool_and_format(
    registry: "ToolRegistry",
    tool_name: str,
    arguments: dict,
    target_file: str,
) -> tuple[str, dict | None, bool]:
    """Execute one Agent3 tool call and return a formatted result string.

    Returns (result_msg, verify_result_or_None, edited_flag).
    - result_msg   : the string to feed back to Agent3.
    - verify_result: the raw dict from run_lean_verify, or None.
    - edited_flag  : True when a write/patch tool was called.

    Error handling:
    - PermissionError → BLOCKED message; edited_flag=False.
    - ValueError (patch mismatch, etc.) → detailed error; edited_flag=False.
    - Unknown tool name → error string; edited_flag=False.
    - Any other exception → error string; edited_flag=False.
    """
    verify_result: dict | None = None
    edited = False

    try:
        result = registry.call(tool_name, **arguments)
    except KeyError as exc:
        return (
            f"## Tool error\ntool `{tool_name}` is not registered. "
            f"Available: read_file, search_in_file, edit_file_patch, write_new_file, "
            f"write_staging_lemma, get_lean_goal, check_lean_have, run_lean_verify, "
            f"request_agent6_glue, request_agent2_help, request_agent7_interface_audit.\nError: {exc}\n"
            "Choose a valid tool.",
            None,
            False,
        )
    except PermissionError as exc:
        return (
            f"## Tool error — BLOCKED\n"
            f"Security violation: {exc}\n"
            "You may only edit files inside Algorithms/ or Lib/.",
            None,
            False,
        )
    except ValueError as exc:
        err_str = str(exc)
        # Surface patch-mismatch clearly so Agent3 knows to re-read the file.
        if tool_name == "edit_file_patch" and (
            "not found in target file" in err_str or "old_str not found" in err_str
        ):
            from orchestrator.file_io import load_file
            tgt_content = ""
            try:
                tgt_content = load_file(target_file)[:6000]
            except Exception:  # noqa: BLE001
                pass
            return (
                f"## Tool error — PATCH MISMATCH\n"
                f"edit_file_patch failed: the SEARCH string was not found in the file.\n"
                f"You MUST copy SEARCH verbatim from the current file (exact whitespace).\n\n"
                f"### Current file content\n```lean\n{tgt_content}\n```\n"
                "Read the file again if needed, then retry with the exact matching string.",
                None,
                False,
            )
        return (f"## Tool error\n{tool_name} failed: {err_str}", None, False)
    except Exception as exc:  # noqa: BLE001
        return (f"## Tool error\n{tool_name} raised: {exc}", None, False)

    # Success path
    if tool_name == "run_lean_verify":
        verify_result = result
        exit_code = int(result.get("exit_code", 1))
        sorry_count = int(result.get("sorry_count", 0))
        errors = result.get("errors", [])
        err_text = "\n".join(errors) if isinstance(errors, list) else str(errors)
        warnings = result.get("warnings", [])
        warn_text = "\n".join(warnings) if isinstance(warnings, list) else str(warnings)

        from orchestrator.file_io import load_file
        tgt_content = ""
        try:
            tgt_path = Path(target_file) if Path(target_file).is_absolute() else PROJECT_ROOT / target_file
            if tgt_path.exists():
                tgt_content = load_file(target_file)[:6000]
        except Exception:  # noqa: BLE001
            pass

        parts = [
            f"## run_lean_verify result",
            f"exit_code: {exit_code}  |  sorry_count: {sorry_count}",
            "",
            "### Build errors",
            "```",
            err_text[:3000] if err_text else "(none)",
            "```",
        ]
        if warn_text:
            parts += [
                "",
                "### Warnings (informational only)",
                "```",
                warn_text[:1000],
                "```",
            ]
        parts += [
            "",
            f"### Current file ({target_file})",
            "```lean",
            tgt_content or "(file does not exist)",
            "```",
        ]
        if exit_code == 0 and sorry_count == 0:
            parts += ["", "Build is CLEAN and sorry_count=0. Output done if finished."]
        result_msg = "\n".join(parts)
    elif tool_name in ("edit_file_patch", "write_new_file"):
        edited = True
        result_msg = (
            f"## {tool_name} result\n"
            f"SUCCESS. File updated.\n"
            "Call run_lean_verify to check the build."
        )
    elif tool_name == "write_staging_lemma":
        edited = True
        # Auto-verify staging after append (mirrors _call_agent2_with_tools logic)
        if result.get("success") and result.get("path"):
            _stg_verify = registry.call("run_lean_verify", result["path"])
            if _stg_verify.get("exit_code", 0) != 0:
                result["staging_compile_ok"] = False
                result["staging_compile_errors"] = _stg_verify.get("errors", [])
                result["note"] = (
                    "STAGING COMPILE ERROR: type errors found (sorry is OK, "
                    "type errors are NOT). Fix the signature with edit_file_patch "
                    "on the staging file. If you cannot fix locally, escalate via request_agent2_help."
                )
            else:
                result["staging_compile_ok"] = True
                result["staging_sorry_count"] = _stg_verify.get("sorry_count", 0)
        if result.get("staging_compile_ok") is True:
            result_msg = (
                f"## write_staging_lemma result\n"
                f"SUCCESS. Lemma appended. staging_compile_ok=true.\n"
                f"Call run_lean_verify on the target file to check the full build."
            )
        elif result.get("staging_compile_ok") is False:
            err_list = result.get("staging_compile_errors", [])
            err_text = "\n".join(err_list) if isinstance(err_list, list) else str(err_list)
            result_msg = (
                f"## write_staging_lemma result\n"
                f"Lemma appended but staging_compile_ok=false — type errors in staging file.\n\n"
                f"### Staging compile errors\n```\n{err_text[:2000]}\n```\n\n"
                f"Fix the type errors with edit_file_patch on the staging file. "
                f"If you cannot fix after trying, call request_agent2_help."
            )
        elif not result.get("success"):
            result_msg = f"## write_staging_lemma result\nFAILED: {result.get('error', 'unknown error')}"
        else:
            result_msg = (
                f"## write_staging_lemma result\n"
                f"SUCCESS. Lemma appended (path={result.get('path', '')}). "
                f"Call run_lean_verify on the target file."
            )
    else:
        # read_file, search_in_file, overwrite_file, etc.
        if isinstance(result, dict):
            result_msg = f"## {tool_name} result\n" + "\n".join(
                f"{k}: {v}" for k, v in result.items()
            )
        elif isinstance(result, str):
            result_msg = f"## {tool_name} result\n{result}"
        else:
            result_msg = f"## {tool_name} result\n{result!r}"

    return result_msg, verify_result, edited


def _format_done_rejection(verify_result: dict, target_file: str) -> str:
    """Return feedback for when Agent3 signals done but verification is not clean."""
    exit_code = int(verify_result.get("exit_code", 1))
    sorry_count = int(verify_result.get("sorry_count", 0))
    errors = verify_result.get("errors", [])
    err_text = "\n".join(errors) if isinstance(errors, list) else str(errors)

    from orchestrator.file_io import load_file
    tgt_content = ""
    try:
        tgt_path = Path(target_file) if Path(target_file).is_absolute() else PROJECT_ROOT / target_file
        if tgt_path.exists():
            tgt_content = load_file(target_file)[:6000]
    except Exception:  # noqa: BLE001
        pass

    return "\n".join([
        "## done signal rejected — build is NOT clean",
        f"exit_code: {exit_code}  |  sorry_count: {sorry_count}",
        "",
        "### Build errors",
        "```",
        err_text[:3000] if err_text else "(none)",
        "```",
        "",
        f"### Current file ({target_file})",
        "```lean",
        tgt_content or "(file does not exist)",
        "```",
        "",
        "You signalled done but the build is not clean. Continue fixing.",
    ])


# ---------------------------------------------------------------------------
# Phase implementations
# ---------------------------------------------------------------------------

def phase1_generate_prompt(
    algorithm: str,
    update_rule: str,
    proof_sketch: str,
    archetype: str,
) -> str:
    """Phase 1: Agent1 generates the Prover prompt via Meta-Prompt A."""
    console.rule("[bold cyan]Phase 1/5 — Generate Prover Prompt")

    agent1 = Agent("orchestrator")
    meta_a = load_meta_prompt_a()
    card = build_algorithm_card(algorithm, update_rule, proof_sketch, archetype)

    phase1_prompt = (
        f"Generate a complete Prover prompt by instantiating the Meta-Prompt A "
        f"template below with the algorithm card.\n\n"
        f"## Meta-Prompt A Template\n{meta_a}\n\n"
        f"## Algorithm Card\n{card}"
    )
    prompt_text = agent1.call(phase1_prompt)
    AuditLogger.get().log_phase1_detail(phase1_prompt, prompt_text)
    console.print(
        f"[green]\\[Agent1] Prover prompt generated "
        f"({len(prompt_text)} chars)."
    )
    return prompt_text


def phase2_plan_and_approve(
    prover_prompt: str,
    force_low_leverage: bool = False,
) -> tuple[str, Agent, Agent]:
    """Phase 2: Agent1 ↔ Agent2 approval loop + leverage gate.

    Returns (approved_plan, agent1, agent2) so they can be reused.
    """
    console.rule("[bold cyan]Phase 2/5 — Plan & Approve")

    agent1 = Agent("orchestrator")
    agent2 = Agent("planner")

    if "subgradient" in prover_prompt.lower() or "subdifferential" in prover_prompt.lower():
        prover_prompt = prover_prompt + _SUBGRADIENT_CONTEXT

    plan = agent2.call(prover_prompt)
    console.print(Panel(
        plan[:500] + "..." if len(plan) > 500 else plan,
        title="[cyan]Agent2 — Initial Plan",
    ))

    round_num = 0
    while True:
        # Python-level symbol_manifest gate (zero token cost).
        # Catch BLOCKED symbols before spending tokens on Agent1 review.
        # Whitelisted symbols (subdifferential, mem_subdifferential_iff) bypass the gate.
        _manifest = _extract_symbol_manifest(plan)
        _blocked = [
            e for e in _manifest
            if str(e.get("status", "")).startswith("BLOCKED")
            and e.get("symbol", "") not in _SYMBOL_WHITELIST
        ]
        if _blocked:
            _blocked_names = ", ".join(e.get("symbol", "?") for e in _blocked)
            console.print(
                f"[red][Python Gate] symbol_manifest BLOCKED: {_blocked_names}. "
                "Forcing Agent2 revision (no Agent1 token spend)."
            )
            plan = agent2.call(
                f"Your plan's symbol_manifest contains BLOCKED entries: {_blocked_names}.\n"
                "Apply Principle A (Primitive First): replace each BLOCKED symbol with "
                "a direct math primitive (inequality, ∀/∃ quantifier, inner product) "
                "before resubmitting.\n"
                "Do NOT invent a new abstract name as a replacement — use raw math."
            )
            console.print(Panel(
                plan[:500] + "..." if len(plan) > 500 else plan,
                title="[cyan]Agent2 — Revised Plan (Python Gate: BLOCKED symbols)",
            ))
            continue  # re-check symbol_manifest before Agent1 review

        round_num += 1
        review_prompt = (
            "Review the plan from Agent2. Return ONLY valid JSON:\n"
            '{"decision": "APPROVED" | "AMEND" | "REJECTED", "feedback": "..."}\n\n'
            "Decision rules:\n"
            "- AMEND: Use for fixable issues (missing docs section, Used-in tags, format). Provide specific feedback.\n"
            "- REJECTED: Use ONLY for unfixable math errors or safety violations. Do NOT use for docs/tags.\n"
            "- APPROVED: Plan meets all criteria.\n\n"
            f"Plan to review:\n{plan}"
        )
        review: dict = {}
        for _retry in range(3):
            review_raw = agent1.call(review_prompt)
            if not review_raw.strip():
                console.print(
                    f"[yellow][Phase 2] Reviewer returned empty response "
                    f"(attempt {_retry + 1}/3)"
                )
                continue
            # Extract the JSON object even if the LLM prepended prose text.
            # Try three strategies in order:
            #   1. Direct parse (LLM followed instructions exactly)
            #   2. Find first '{' and parse from there
            #   3. Extract a ```json ... ``` fenced block
            _parsed: dict | None = None
            _parse_err: json.JSONDecodeError | None = None
            for _candidate in _json_candidates(review_raw):
                try:
                    _obj = json.loads(_candidate)
                    if isinstance(_obj, dict):
                        _parsed = _obj
                        break
                except json.JSONDecodeError as _exc:
                    _parse_err = _exc
            if _parsed is not None:
                review = _parsed
                break
            exc = _parse_err or json.JSONDecodeError("no JSON found", review_raw, 0)
            if _retry < 2:
                console.print(
                    f"[yellow][Phase 2] Reviewer returned invalid JSON "
                    f"(attempt {_retry + 1}/3): {exc.msg}"
                )
                review_prompt = (
                    "Your previous response could not be parsed as JSON. "
                    "Return ONLY a single JSON object with NO surrounding text:\n"
                    '{"decision": "APPROVED" | "AMEND" | "REJECTED", "feedback": "..."}\n\n'
                    "Do NOT include any explanation, markdown, or code fences.\n\n"
                    f"Plan to review:\n{plan}"
                )
                continue
            raise RuntimeError(
                "[Phase 2] Reviewer returned invalid JSON after 3 attempts. "
                f"line={exc.lineno}, col={exc.colno}, msg={exc.msg}"
            ) from exc
        else:
            raise RuntimeError("[Phase 2] Reviewer returned empty response after 3 attempts.")

        if not isinstance(review, dict):
            raise RuntimeError("[Phase 2] Reviewer response must be a JSON object.")

        decision = str(review.get("decision", "")).strip().upper()
        feedback = review.get("feedback", "")
        feedback_text = feedback if isinstance(feedback, str) else str(feedback)

        AuditLogger.get().log_phase2_round(
            round_num, plan, review_prompt, review_raw, decision, feedback_text
        )

        if decision == "APPROVED":
            console.print(
                f"[green]\\[Agent1 ↔ Agent2] Plan APPROVED after {round_num} round(s)."
            )
            break

        if decision == "AMEND":
            if not isinstance(feedback, str) or not feedback.strip():
                raise RuntimeError(
                    "[Phase 2] decision=AMEND requires a non-empty feedback field."
                )
            console.print(Panel(
                feedback_text[:400] + "..." if len(feedback_text) > 400 else feedback_text,
                title=f"[yellow]Agent1 — AMEND Feedback (round {round_num})",
            ))
            # Automatic rollback to planner stage.
            plan = agent2.call(
                "Revise your plan based on reviewer feedback below.\n\n"
                f"{feedback_text}"
            )
            console.print(Panel(
                plan[:500] + "..." if len(plan) > 500 else plan,
                title=f"[cyan]Agent2 — Revised Plan (round {round_num})",
            ))
            continue

        if decision == "REJECTED":
            raise RuntimeError(
                "[Phase 2] Plan REJECTED by reviewer. "
                f"Feedback: {feedback_text or '(none)'}"
            )

        raise RuntimeError(
            "[Phase 2] Invalid decision from reviewer. "
            f"Expected APPROVED/REJECTED/AMEND, got: {decision!r}"
        )

    passed, leverage = check_leverage_gate(plan)
    console.print(
        f"[{'green' if passed else 'red'}]"
        f"\\[Gate 1] Leverage = {leverage:.1%} "
        f"({'PASS' if passed else 'BLOCKED'})"
    )
    if not passed and not force_low_leverage:
        console.print(
            "[red bold]Leverage below 50%.  Use --force-low-leverage to override."
        )
        sys.exit(1)

    return plan, agent1, agent2


# ---------------------------------------------------------------------------
# Escalation context helpers (Change 4 / 6b)
# ---------------------------------------------------------------------------

_ESCALATION_CHAR_LIMIT = 20_000


def _extract_declaration_skeleton(lines: list[str]) -> str:
    """Return a skeleton of *lines*: keep declaration headers, strip proof bodies.

    A 'proof body' is everything between a line that ends with ':= by' (or
    starts a ``:=`` assignment) and the next line at column 0 that starts a new
    top-level declaration (``def``, ``theorem``, ``lemma``, ``noncomputable``,
    ``structure``, ``namespace``, ``end``, ``--``, ``#``, blank).
    """
    DECL_KW = re.compile(r"^\s*(def |theorem |lemma |noncomputable |structure |namespace |end |@\[|--|\s*#)")
    in_body = False
    result: list[str] = []
    for line in lines:
        stripped = line.rstrip()
        if DECL_KW.match(line):
            in_body = False
        if in_body:
            continue
        result.append(stripped)
        if re.search(r":=\s*by\s*$", stripped) or re.search(r":=\s*$", stripped):
            result.append("  sorry  -- (proof body omitted in skeleton)")
            in_body = True
    return "\n".join(result)


def _build_escalation_file_context(target_file: str, stuck_line: int | None = None) -> str:
    """Return file content for Agent2 escalation with a soft 20k-char cap.

    If the file fits within *_ESCALATION_CHAR_LIMIT* characters it is returned
    verbatim.  Otherwise a declaration skeleton plus a ±200-line window around
    *stuck_line* (when provided) is returned instead.
    """
    try:
        content = load_file(target_file)
    except Exception:  # noqa: BLE001
        return "(file missing or unreadable)"

    if len(content) <= _ESCALATION_CHAR_LIMIT:
        return content

    lines = content.splitlines()
    skeleton = _extract_declaration_skeleton(lines)

    if stuck_line is not None:
        window_start = max(0, stuck_line - 200)
        window_end = min(len(lines), stuck_line + 200)
        window = "\n".join(lines[window_start:window_end])
        return (
            f"-- SKELETON (proof bodies omitted for brevity)\n{skeleton}\n\n"
            f"-- FULL CONTEXT around line {stuck_line} (±200 lines)\n{window}"
        )
    return f"-- SKELETON (proof bodies omitted; file exceeds {_ESCALATION_CHAR_LIMIT} chars)\n{skeleton}"


def _audit_staging_usage(
    target_file: str,
    staging_path: "Path",
    console_print: "Any",
) -> dict[str, bool]:
    """Return ``{lemma_name: used}`` for all declarations in the staging file.

    Scans the final algorithm file for each declaration name found in the
    staging file and reports whether it is referenced at least once.
    """
    staging_content = ""
    if staging_path.exists():
        staging_content = staging_path.read_text(encoding="utf-8")
    else:
        try:
            _rel = str(staging_path.relative_to(PROJECT_ROOT))
            staging_content = snapshot_file(_rel)
        except Exception:  # noqa: BLE001
            staging_content = ""
    if not staging_content:
        return {}
    try:
        target_content = load_file(target_file)
    except Exception:  # noqa: BLE001
        target_content = ""

    decl_names = re.findall(r"(?:theorem|lemma|def)\s+(\w+)", staging_content)

    usage: dict[str, bool] = {}
    for name in decl_names:
        used = bool(re.search(rf"\b{re.escape(name)}\b", target_content))
        usage[name] = used
        status = "USED" if used else "UNUSED (candidate for cleanup)"
        console_print(f"  [Staging] {name} — {status}")

    return usage


def phase3_prove(
    agent2: Agent,
    target_file: str,
    plan: str,
    *,
    max_retries: int = MAX_PHASE3_RETRIES,
    archetype: str = "A",
    max_tool_turns: int | None = None,
) -> tuple[bool, int, str, dict]:
    """Phase 3: Agent2 ↔ Agent3 proving loop + Agent5 escalation.

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
    #   Created by Agent3 write_new_file or pre-existing. Always lives in Algorithms/.
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
    _file_absent_suffix = (
        "\n\nCRITICAL: The target file does NOT exist yet. Your guidance MUST instruct "
        f'Agent3 to call write_new_file(path="{target_file}", content=<full Lean scaffold>) '
        "as the FIRST tool call. Output the complete file content in a code block for "
        "Agent3 to pass to write_new_file. Do NOT suggest edit_file_patch — the file "
        "must be created first."
        if not initial_exists
        else ""
    )
    # Pre-compute imported API signatures once; reused for every Agent2 + Agent3 call.
    _imported_sigs = _extract_imported_algo_sigs(target_file)
    _imported_sigs_block = (
        f"\n\n{_imported_sigs}"
        if _imported_sigs else ""
    )
    guidance = _call_agent2_with_tools(
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
        + _file_absent_suffix
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
    agent7_invocations: list[dict] = []
    agent7_step_execution_log: list[dict] = []
    agent7_plan_revisions: list[dict] = []
    agent7_blocked_actions: list[dict] = []
    agent7_forced_trigger_count = 0
    agent7_force_gate_entries: list[dict] = []
    agent7_force_gate_rejections: list[dict] = []
    agent7_force_gate_reason_samples: list[str] = []
    token_char_budget = 0

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

    for attempt in range(1, max_retries + 1):
        attempts = attempt
        attempt_start_hash: str | None = _file_hash(target_file)
        # Keep previous verify context available before prequery (attempt>1 path).
        # These are re-initialized later for per-attempt tracking, but must exist
        # before first use in _prequery_sorry_goals.
        last_exit_code = 1
        last_verify_text = ""
        _file_absent_prefix = (
            "CRITICAL: Target file does NOT exist. You MUST call write_new_file(path="
            f'"{target_file}", content=<complete Lean code>) as your FIRST tool call. '
            "The guidance below contains the full file content — pass it to write_new_file. "
            "Only after the file exists do you call run_lean_verify.\n\n"
            if not _target_exists_overlay()
            else ""
        )
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
        prover_prompt = (
            _attempt_awareness
            + _file_absent_prefix
            + "Use tools to close sorry placeholders.\n"
            "Return ONLY valid JSON with exactly three keys: thought, tool, arguments.\n"
            "Output ONE action per response. After each action you will receive its "
            "result before deciding the next action.\n"
            'Example: {"thought": "...", "tool": "read_file", "arguments": {"path": "..."}}\n'
            "To signal no further actions are needed: "
            '{"thought": "...", "tool": "done", "arguments": {}}\n'
            "Allowed tools: read_file, read_file_readonly, search_in_file, search_in_file_readonly, "
            "search_codebase, edit_file_patch, write_new_file, write_staging_lemma, get_lean_goal, "
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
            # Fix 2: staging cannot reference definitions from the target algorithm file.
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

        # Pre-query Lean goal states for sorry lines mentioned in guidance.
        # Skip when staging has errors (elaboration would fail / timeout).
        _staging_has_errors = (
            last_exit_code != 0
            and last_verify_text
            and any("Staging" in e.get("file", "") for e in _parse_lean_errors(last_verify_text))
        ) if attempt > 1 else False  # no prior error on attempt 1
        _goal_block = _prequery_sorry_goals(
            registry,
            target_file,
            guidance,
            _goal_cache,
            _staging_has_errors,
            errors_text=last_verify_text,
        )
        if _goal_block:
            console.print(
                f"  [GoalPreQuery] attempt {attempt} — injected goal states for "
                f"{_goal_block.count('Line ')} sorry line(s)"
            )
            prover_prompt = prover_prompt + "\n\n" + _goal_block

        raw_reply = agent3.call(prover_prompt)
        token_char_budget += len(prover_prompt) + len(raw_reply)

        # Per-attempt state tracking
        exec_results: list[ExecutionResult] = []
        edited_this_attempt = False
        patch_mismatch_in_attempt = False
        last_exit_code = 1
        last_sorry_in_attempt = 0
        last_verify_text = ""
        last_verify_result: dict | None = None
        # Runtime trajectory check (P2): track whether Agent3 has done any
        # symbol lookup since last edit, so we can warn when it patches blind.
        _lookup_done_since_last_edit: bool = False
        _patch_without_lookup_count: int = 0

        # Staging file lint check at start of each attempt.
        # If the staging file already has known API misspellings, alert Agent3
        # immediately so it fixes them before the first verify.
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
                raw_reply = agent3.call(_lint_feedback)
                token_char_budget += len(_lint_feedback) + len(raw_reply)

        # -------------------------------------------------------------------
        # Single-step interactive tool loop
        # Each iteration: parse one action, execute it, return result to Agent3.
        # -------------------------------------------------------------------
        _inner_break_reason = ""
        _escalation_count = 0  # limit Agent3→Agent2 escalations per attempt
        _agent6_escalation_count = 0  # limit request_agent6_glue per attempt
        _last_local_error_sig: str | None = None  # for Agent6 auto-route repeat detection
        _agent6_first_goal_sig: str | None = None
        _agent6_first_progress_ok: bool = False
        _agent6_second_min_progress = RETRY_LIMITS.get("AGENT6_SECOND_ESCALATION_MIN_PROGRESS", 1)
        _agent6_second_require_same_goal = bool(
            RETRY_LIMITS.get("AGENT6_SECOND_ESCALATION_REQUIRE_SAME_GOAL", 1)
        )
        _agent7_invocations_this_attempt = 0
        _agent7_max_invocations = RETRY_LIMITS.get("MAX_AGENT7_INVOCATIONS_PER_ATTEMPT", 2)
        _agent7_no_progress_threshold = RETRY_LIMITS.get("AGENT7_STEP_NO_PROGRESS_THRESHOLD", 2)
        _agent7_approved_agent6 = False  # True when Agent7 plan includes route_to agent6 or step request_agent6_glue
        _active_agent7_plan: dict | None = None
        _agent7_current_step_idx = 0
        _agent7_pending_verify = False
        _agent7_last_step_id: str | None = None
        _agent7_prev_sorry = last_sorry_count
        _agent7_no_progress_count = 0
        _agent7_force_stale_threshold = RETRY_LIMITS.get("AGENT7_FORCE_STALE_LINE_THRESHOLD", 3)
        _agent7_force_no_progress_turns_threshold = RETRY_LIMITS.get("AGENT7_FORCE_NO_PROGRESS_TURNS", 2)
        _agent7_force_after_soft_warn = RETRY_LIMITS.get("AGENT7_FORCE_AFTER_SOFT_WARN", 1)
        _agent7_soft_warned = False
        _agent7_force_gate_active = False
        _agent7_force_warn_turn: int | None = None
        _agent7_no_progress_turns = 0
        _agent7_last_verified_sorry: int | None = None
        _stale_err_line: int | None = None
        _stale_err_count: int = 0
        _tools_used_this_attempt: set[str] = set()
        for tool_turn in range(max_tool_turns):
            # Parse Agent3's single action
            try:
                payload = json.loads(raw_reply)
            except json.JSONDecodeError as exc:
                err_msg = (
                    f"Invalid JSON (line {exc.lineno}, col {exc.colno}): {exc.msg}. "
                    "Return valid JSON with keys: thought, tool, arguments."
                )
                diag_log.append(f"attempt={attempt} turn={tool_turn} {err_msg}")
                exec_results.append(ExecutionResult(
                    status_code="ERROR", message=err_msg, attempt=attempt,
                ))
                last_errors = err_msg
                _inner_break_reason = "json_error"
                break

            if not isinstance(payload, dict):
                err_msg = "Agent3 JSON must be an object with keys: thought, tool, arguments."
                diag_log.append(f"attempt={attempt} turn={tool_turn} {err_msg}")
                exec_results.append(ExecutionResult(
                    status_code="ERROR", message=err_msg, attempt=attempt,
                ))
                last_errors = err_msg
                _inner_break_reason = "json_error"
                break

            tool_name = str(payload.get("tool", ""))
            arguments = payload.get("arguments", {})
            if not isinstance(arguments, dict):
                arguments = {}
            if tool_name:
                _tools_used_this_attempt.add(tool_name)

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
            # Agent6 is used only when Agent7's interface audit indicates a missing glue lemma.
            # ---------------------------------------------------------------
            if tool_name == "request_agent6_glue":
                if not _agent7_approved_agent6:
                    raw_reply = agent3.call(
                        "## request_agent6_glue rejected — Agent7 gate\n"
                        "Agent6 is used only when Agent7's interface audit indicates a missing glue lemma. "
                        "Call request_agent7_interface_audit first."
                    )
                    token_char_budget += len(raw_reply)
                    continue
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
                    new_guidance = _call_agent2_with_tools(
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
                if _escalation_count > 3:
                    esc_msg = (
                        "## Escalation limit reached\n"
                        "You have already escalated 3 times this attempt. "
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
                new_guidance = _call_agent2_with_tools(
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
                    f"to add it to {_staging_rel} NOW — do not just describe it.",
                )
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

            # Execute single tool and format result for Agent3
            result_msg, verify_result, edited = _execute_single_tool_and_format(
                registry, tool_name, arguments, target_file
            )
            token_char_budget += len(result_msg)
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

                console.print(
                    f"  [Agent3] attempt {attempt}/{max_retries} "
                    f"turn {tool_turn + 1}/{max_tool_turns} — "
                    f"exit={last_exit_code}, sorry={last_sorry_in_attempt}"
                )
                if last_exit_code != 0 and last_verify_text:
                    console.print(f"[dim]  {last_verify_text[:400]}[/dim]")

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
                        if _tgt.exists():
                            _tgt.unlink()
                        initial_exists = False
                        initial_hash = None
                        file_changed = False
                    guidance = _call_agent2_with_tools(
                        agent2,
                        staging_registry,
                        f"[STATEMENT ERROR — SIGNATURE HALLUCINATION]\n"
                        f"Lean error excerpt:\n```\n"
                        f"{_prioritize_error_text(_structured_errors_inner, last_verify_text, _inner_err_line, target_file, max_chars=800)}"
                        f"\n```\n\n"
                        "The theorem STATEMENT itself is broken: it references a symbol "
                        "that does not exist in Lean or Lib/.\n"
                        "The old file has been DELETED. You MUST now rewrite it from scratch.\n\n"
                        "CONSTRAINT (non-negotiable — Principle A):\n"
                        "Use ONLY mathematical primitives in the new theorem signature.\n"
                        "Do NOT invent any new abstract type, set constructor, or class name —\n"
                        "including any name resembling the one that just failed.\n"
                        "Express every property as a direct inequality, ∀/∃ quantifier,\n"
                        "or inner-product expression (e.g. ∀ y, f y ≥ f x + ⟪g, y-x⟫_ℝ).\n\n"
                        "Output a complete corrected file. Agent3 will use write_new_file.",
                    )
                    _inner_break_reason = "hallucination"
                    break  # start next attempt with fresh guidance

                if error_type == "DEFINITION_ZONE_ERROR":
                    # Do NOT bump _stale_err_count to 3 — let normal stale logic apply
                    result_msg = (
                        "## DEFINITION ZONE ERROR\n"
                        "Type mismatch occurs in declaration/definition zone (before proof tactics).\n"
                        "This usually means a called function is being applied with the wrong signature.\n"
                        "Read the callee definition first, then patch.\n\n"
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
                                new_guidance = _call_agent2_with_tools(
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
                        _stale_err_count >= _agent7_force_stale_threshold
                        and _agent7_no_progress_turns >= _agent7_force_no_progress_turns_threshold
                    )
                    _reason = (
                        f"stale_line_count={_stale_err_count}, "
                        f"no_progress_turns={_agent7_no_progress_turns}, "
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
                    guidance = _call_agent2_with_tools(
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

        # File-not-created check
        if not _target_exists_overlay():
            guidance = _call_agent2_with_tools(
                agent2,
                staging_registry,
                f"Attempt {attempt} failed: Target file still does not exist.\n"
                f"Agent3 did NOT call write_new_file. You MUST output the FULL Lean file content "
                f'and explicitly instruct Agent3 to call write_new_file(path="{target_file}", '
                "content=<complete file>) as the FIRST tool call.\n"
                f"Guidance format: Provide a code block with the complete {target_file} "
                "scaffold (imports, setup, theorem stubs with sorry). Agent3 will pass it to write_new_file.",
            )
            console.print(
                f"  [Agent3] attempt {attempt}/{max_retries} — "
                "build=FAIL (file not created)"
            )
            continue

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
                guidance = _call_agent2_with_tools(agent2, staging_registry, _noop_ctx)
                console.print(
                    f"  [Agent3] attempt {attempt}/{max_retries} — "
                    f"build={last_exit_code} (file UNCHANGED — NOOP forced)"
                )
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
            guidance = _call_agent2_with_tools(
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
            guidance = _call_agent2_with_tools(
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
                f"\n=== AGENT3'S CURRENT FILE ({target_file}) ===\n"
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
                ),
            )
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
            guidance = _call_agent2_with_tools(
                agent2,
                staging_registry,
                f"Attempt {attempt} failed.\n"
                "Agent3 returned invalid JSON. Last error: " + last_errors + "\n"
                "Adjust your guidance so Agent3 outputs strict single-action JSON.",
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
        guidance = _call_agent2_with_tools(
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
            ),
        )

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

    console.print("[red bold]Max retries exhausted — escalating to Agent5.")
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


def _apply_lib_insert(file_path: str, anchor_id: str, content: str) -> str:
    """Insert content into a Lib/Glue file at the given anchor. Returns updated content."""
    if file_path not in LIB_GLUE_ANCHORS:
        raise ValueError(f"[Phase 4] Unknown Lib file for lib_write: {file_path}")
    anchors = LIB_GLUE_ANCHORS[file_path]
    if anchor_id not in anchors:
        raise ValueError(
            f"[Phase 4] Unknown anchor_id '{anchor_id}' for {file_path}. "
            f"Allowed: {list(anchors.keys())}"
        )
    cfg = anchors[anchor_id]
    regex = cfg["regex"]
    insert_mode = cfg.get("insert", "before")

    original = snapshot_file(file_path)
    if not original:
        raise FileNotFoundError(f"[Phase 4] Lib file does not exist: {file_path}")

    matches = list(re.finditer(regex, original, flags=re.MULTILINE))
    if not matches:
        raise ValueError(
            f"[Phase 4] Anchor regex not found in {file_path}: {regex[:50]}..."
        )
    if len(matches) > 1:
        raise ValueError(
            f"[Phase 4] Anchor matches {len(matches)} locations in {file_path}"
        )
    m = matches[0]
    insert_body = "\n\n" + content.strip() + "\n"
    if insert_mode == "before":
        insert_at = m.start()
        updated = original[:insert_at] + insert_body + original[insert_at:]
    else:
        insert_at = m.end()
        updated = original[:insert_at] + insert_body + original[insert_at:]
    return updated


def phase4_persist(
    algorithm: str,
    target_file: str,
    plan: str,
    baseline_tracked: set[str],
    baseline_untracked: set[str],
) -> int:
    """Phase 4: Agent4 persists documentation (Glue + Layer 1).

    Returns new_tricks_added.
    """
    console.rule("[bold cyan]Phase 4/5 — Persist Documentation")
    registry = ToolRegistry()
    registry.register_default_tools()

    # Strict precondition: only persist after build is green and sorry is zero.
    verify_result = registry.call("run_lean_verify", target_file)
    if int(verify_result.get("exit_code", 1)) != 0 or int(verify_result.get("sorry_count", 1)) != 0:
        raise RuntimeError(
            "[Phase 4] BLOCKED: build must be green and sorry_count must be 0 "
            "before documentation persistence."
        )

    tricks_before = snapshot_file("docs/GLUE_TRICKS.md")
    tricks_sections_before = count_glue_tricks_sections()

    modified_lean_files = _get_modified_lean_files(
        baseline_tracked,
        baseline_untracked,
    )
    console.print(
        f"[cyan]\\[Phase 4] Modified Lean files detected: "
        f"{modified_lean_files or [target_file]}"
    )

    meta_b = load_meta_prompt_b()
    agent4 = Agent("persister", extra_files=modified_lean_files or [target_file])
    allowed_anchors = DOC_ANCHORS

    lib_anchor_info = "\n".join(
        f"- {f}: {list(a.keys())}" for f, a in LIB_GLUE_ANCHORS.items()
    )

    persistence_output = agent4.call(
        f"Persist the completed proof for algorithm '{algorithm}' using "
        f"Meta-Prompt B below.\n\n## Meta-Prompt B\n{meta_b}\n\n"
        f"## Approved proof plan (use this as [PROOF INPUT] for Meta-Prompt B)\n{plan}\n\n"
        f"## Modified Lean files\n"
        + "\n".join(f"- {f}" for f in (modified_lean_files or [target_file]))
        + "\n\n## Allowed doc anchor IDs\n"
        + "\n".join(f"- {k}" for k in sorted(allowed_anchors))
        + "\n\n## Lib/Glue anchor IDs (for lib_write ops)\n"
        + lib_anchor_info
    )
    console.print(
        f"[green]\\[Agent4] Persistence output generated "
        f"({len(persistence_output)} chars)."
    )

    try:
        patch_ops = _parse_persister_json(persistence_output)
    except json.JSONDecodeError as exc:
        raise RuntimeError(
            "[Phase 4] Persister returned invalid JSON. "
            f"line={exc.lineno}, col={exc.colno}, msg={exc.msg}"
        ) from exc

    if not isinstance(patch_ops, list):
        raise RuntimeError("[Phase 4] Persister output must be a JSON array.")

    patterns_from_output: list[str] = []
    catalog_patch_fragments: list[str] = []
    patch_ops_summary: list[dict] = []
    lib_write_ops: list[dict] = []
    algorithm_refactor_ops: list[dict] = []
    # Guard A: track anchors already patched in this run to prevent double-insert
    # when Agent4 emits two ops with the same anchor in one response.
    patched_anchors: set[str] = set()

    for idx, op in enumerate(patch_ops, start=1):
        if not isinstance(op, dict):
            raise RuntimeError(f"[Phase 4] patch_ops[{idx}] must be an object.")
        op_type = op.get("op", "doc_patch")

        if op_type == "doc_patch" or op_type is None:
            anchor_id = op.get("anchor")
            content = op.get("content")
            if not isinstance(anchor_id, str) or not isinstance(content, str):
                raise RuntimeError(
                    f"[Phase 4] patch_ops[{idx}] doc_patch requires 'anchor' and 'content'."
                )
            if anchor_id not in allowed_anchors:
                raise RuntimeError(
                    f"[Phase 4] patch_ops[{idx}] uses non-allowed anchor: {anchor_id}"
                )
            # Guard A: skip if this anchor was already patched earlier in this run.
            if anchor_id in patched_anchors:
                console.print(
                    f"[yellow]\\[Agent4] Skipping duplicate anchor {anchor_id} in same run"
                )
                continue
            # Guard B: for CATALOG_ALGO_LAYER, skip if algorithm section already exists.
            if anchor_id == "CATALOG_ALGO_LAYER":
                catalog_text = (PROJECT_ROOT / "docs/CATALOG.md").read_text(encoding="utf-8")
                algo_pat = (
                    rf"^## Algorithm Layer \(Layer 2\)\s+—\s+`Algorithms/{re.escape(algorithm)}\.lean`"
                )
                if re.search(algo_pat, catalog_text, re.MULTILINE):
                    console.print(
                        f"[cyan]\\[Agent4] Algorithm section already exists in CATALOG.md — skipping"
                    )
                    continue
            cfg = allowed_anchors[anchor_id]
            patch_result = registry.call(
                "apply_doc_patch",
                path=cfg["path"],
                anchor=cfg["regex"],
                new_content=content,
            )
            changed = bool(patch_result.get("changed", False))
            patch_ops_summary.append({
                "op": "doc_patch",
                "anchor": anchor_id,
                "path": cfg["path"],
                "changed": changed,
            })
            if changed:
                patched_anchors.add(anchor_id)
                console.print(
                    f"[green]\\[Agent4] Patched {cfg['path']} via anchor {anchor_id}"
                )
                if cfg["path"] == "docs/GLUE_TRICKS.md":
                    patterns_from_output.extend(re.findall(
                        r"^#{3,4}\s+Pattern[^\n]*",
                        content,
                        flags=re.MULTILINE,
                    ))
                if cfg["path"] == "docs/CATALOG.md":
                    catalog_patch_fragments.append(content)
            else:
                console.print(
                    f"[cyan]\\[Agent4] Skipped duplicate content for {cfg['path']} ({anchor_id})"
                )
        elif op_type == "lib_write":
            lib_write_ops.append(op)
        elif op_type == "algorithm_refactor":
            algorithm_refactor_ops.append(op)
        else:
            raise RuntimeError(
                f"[Phase 4] patch_ops[{idx}] unknown op: {op_type}. "
                "Allowed: doc_patch, lib_write, algorithm_refactor."
            )

    lib_snapshots: dict[str, str] = {}
    algo_snapshots: dict[str, str] = {}

    if lib_write_ops:
        console.print("[cyan]\\[Phase 4] Applying lib_write ops...")
        for idx, op in enumerate(lib_write_ops, start=1):
            file_path = op.get("file")
            anchor_id = op.get("anchor_id")
            content = op.get("content")
            if not all(isinstance(x, str) for x in (file_path, anchor_id, content)):
                raise RuntimeError(
                    f"[Phase 4] lib_write op {idx} requires file, anchor_id, content."
                )
            if file_path not in lib_snapshots:
                lib_snapshots[file_path] = snapshot_file(file_path)
            updated = _apply_lib_insert(file_path, anchor_id, content)
            registry.call("overwrite_file", path=file_path, content=updated)
            patch_ops_summary.append({
                "op": "lib_write",
                "path": file_path,
                "anchor_id": anchor_id,
            })
            console.print(f"[green]\\[Agent4] Inserted lemma into {file_path} via {anchor_id}")

        # Full-library build: catches cascade failures in algorithm files caused
        # by changes to Lib/Glue lemma signatures or new lemma insertions.
        build_result = registry.call("run_repo_verify")
        if int(build_result.get("exit_code", 1)) != 0:
            console.print("[red]\\[Phase 4] lib_write caused build failure. Rolling back...")
            for path, snap in lib_snapshots.items():
                registry.call("overwrite_file", path=path, content=snap)
            raise RuntimeError(
                "[Phase 4] Lib/refactor caused build failure. Rolled back.\n"
                + ("\n".join(build_result.get("errors", [])) or "Unknown error")
            )

    if algorithm_refactor_ops:
        console.print("[cyan]\\[Phase 4] Applying algorithm_refactor ops...")
        for idx, op in enumerate(algorithm_refactor_ops, start=1):
            file_path = op.get("file")
            patches = op.get("patches")
            if not isinstance(file_path, str) or not isinstance(patches, list):
                raise RuntimeError(
                    f"[Phase 4] algorithm_refactor op {idx} requires file and patches list."
                )
            if file_path not in algo_snapshots:
                algo_snapshots[file_path] = snapshot_file(file_path)
            for pidx, patch in enumerate(patches):
                old_str = patch.get("old_str")
                new_str = patch.get("new_str")
                if not isinstance(old_str, str) or not isinstance(new_str, str):
                    raise RuntimeError(
                        f"[Phase 4] algorithm_refactor op {idx} patch {pidx} "
                        "requires old_str and new_str."
                    )
                registry.call("edit_file_patch", path=file_path, old_str=old_str, new_str=new_str)
            patch_ops_summary.append({
                "op": "algorithm_refactor",
                "path": file_path,
                "patches_count": len(patches),
            })
            console.print(f"[green]\\[Agent4] Refactored {file_path} ({len(patches)} patch(es))")

        # Full-library build: catches cascade failures across all algorithm files,
        # not just the directly refactored ones.
        build_result = registry.call("run_repo_verify")
        if int(build_result.get("exit_code", 1)) != 0:
            console.print("[red]\\[Phase 4] algorithm_refactor caused build failure. Rolling back...")
            for path, snap in algo_snapshots.items():
                registry.call("overwrite_file", path=path, content=snap)
            raise RuntimeError(
                "[Phase 4] Algorithm refactor caused build failure. Rolled back.\n"
                + ("\n".join(build_result.get("errors", [])) or "Unknown error")
            )

    # Doc-code alignment: if CATALOG lemma status was touched, the lemmas must exist in Lib/.
    if catalog_patch_fragments:
        lib_names = _collect_lib_declaration_names()
        touched_lemmas: set[str] = set()
        for fragment in catalog_patch_fragments:
            touched_lemmas.update(_extract_catalog_lemma_names(fragment))
        missing = sorted(name for name in touched_lemmas if name not in lib_names)
        if missing:
            raise RuntimeError(
                "[Phase 4] CATALOG-Lib alignment failed. Missing Lib declarations: "
                + ", ".join(missing)
            )

    tricks_after = snapshot_file("docs/GLUE_TRICKS.md")
    tricks_sections_after = count_glue_tricks_sections()
    new_tricks = tricks_sections_after - tricks_sections_before

    # Gate 3: GLUE_TRICKS validation (BLOCKING)
    glue_changed = (tricks_before != tricks_after) or (new_tricks > 0)
    unique_patterns = sorted(set(patterns_from_output))
    gate3_ok, missing_patterns = check_glue_tricks_gate(
        tricks_before,
        tricks_after,
        unique_patterns,
    )
    if not gate3_ok:
        raise RuntimeError(
            "[Gate 3] Missing GLUE_TRICKS pattern entries: "
            + ", ".join(missing_patterns)
        )

    if glue_changed:
        console.print(
            f"[green]\\[Gate 3] GLUE_TRICKS.md updated — "
            f"{new_tricks} new pattern(s)."
        )
    else:
        console.print("[green]\\[Gate 3] No new patterns — GLUE_TRICKS.md unchanged.")

    # Gate 4: Used-in tag check — covers all modified Lean files, not just target
    modified = modified_lean_files or [target_file]
    missing = check_used_in_tags(modified)
    if missing:
        raise Gate4Error(missing)
    else:
        console.print("[green]\\[Gate 4] All Used-in tags present.")

    AuditLogger.get().add_phase4_data(patch_ops_summary)
    return new_tricks


def phase5_finalize(
    algorithm: str,
    new_tricks: int,
    phase3_audit: dict,
    total_attempts: int,
) -> None:
    """Phase 5: Persist physical metrics and print audit report."""
    console.rule("[bold cyan]Phase 5/5 — Finalize Metrics")

    store = MetricsStore()
    record = capture_physical_metrics(
        algorithm=algorithm,
        new_tricks_added=new_tricks,
        phase3_execution_history=phase3_audit.get("execution_history", []),
        phase3_attempts=total_attempts,
        estimated_token_consumption=int(
            phase3_audit.get("estimated_token_consumption", 0)
        ),
    )
    store.append(record)

    console.print(Panel(
        f"Algorithm:          {algorithm}\n"
        f"Build exit code:    {record.physical_exit_code}\n"
        f"Repo sorry count:   {record.total_repo_sorry_count}\n"
        f"\n"
        f"── Leverage Metrics ────────────────────────────────────\n"
        f"New Lib decls:      {record.new_lib_declarations}\n"
        f"Algo call hits:     {record.algorithm_calls_to_new_lib_declarations}\n"
        f"Physical leverage:  {record.physical_leverage_rate:.1%}  "
        f"[calls/(calls+decls)]\n"
        f"L_coverage:         {record.lib_coverage_rate:.1%}  "
        f"[used decls / total new decls]\n"
        f"L_density:          {record.lib_density_rate:.2f}  "
        f"[total calls / used decls]\n"
        f"\n"
        f"── Phase 3 Cost ────────────────────────────────────────\n"
        f"P3 retries:         {record.phase3_retry_count}\n"
        f"Sorry attempts:     {total_attempts}\n"
        f"Est. token usage:   {record.estimated_token_consumption}\n"
        f"\n"
        f"── Documentation ───────────────────────────────────────\n"
        f"Total glue lemmas:  {record.total_glue_lemmas}\n"
        f"Total L1 lemmas:    {record.total_layer1_lemmas}\n"
        f"New tricks added:   {new_tricks}\n"
        f"Final sorry count:  {record.final_sorry_count}\n"
        f"Doc-code aligned:   {'YES' if record.doc_code_alignment_ok else 'NO'}\n",
        title="[bold green]Run Complete (Physical Audit)",
    ))
    if not record.doc_code_alignment_ok:
        console.print(Panel(
            "\n".join(record.doc_code_alignment_missing or []),
            title="[red]Audit Mismatch: Doc-Code Alignment",
        ))


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
    )


if __name__ == "__main__":
    main()
