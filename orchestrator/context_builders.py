"""Context-building and formatting utilities for the orchestration pipeline."""
from __future__ import annotations

import json
import re
from collections import Counter
from pathlib import Path

from rich.console import Console

from orchestrator.config import (
    AGENT_CONFIGS,
    ALGORITHM_REFERENCES,
    PROJECT_ROOT,
    REFERENCE_FILES_WITH_DESCRIPTIONS,
    RETRY_LIMITS,
    _get_default_references,
)
from orchestrator.error_classifier import _llm_classify_error
from orchestrator.file_io import load_file, snapshot_file
from orchestrator.git_utils import _file_hash
from orchestrator.prompts import AGENT_FILES

console = Console()

_CATALOG_LEMMA_HEADING_RE = re.compile(r"^####\s+`([^`]+)`", re.MULTILINE)
_LIB_DECL_RE = re.compile(
    r"^(?:theorem|lemma|noncomputable\s+def|def)\s+([A-Za-z_]\w*)",
    re.MULTILINE,
)

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

_TOP_LEVEL_KEYWORDS = re.compile(
    r"^(?:noncomputable\s+)?(?:def|theorem|lemma|abbrev|structure|class|instance"
    r"|namespace|section|end|open|variable|attribute|@\[|--)",
    re.MULTILINE,
)

_DECL_START = re.compile(
    r"^(?:noncomputable\s+)?(?:def|theorem|lemma|abbrev)\s+\w",
)


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


def _prequery_error_line_goal(
    registry,
    target_file: str,
    error_line: int | None,
    goal_cache: dict,
) -> str:
    """Query get_lean_goal at the primary error line (not a sorry).

    Used to give Agent2 the exact ``⊢`` type and hypotheses at a failing
    proof-body line so it can generate a PATCH with correctly-typed terms
    instead of guessing coercions.

    Returns a formatted string block, or empty string on any failure.
    """
    if error_line is None:
        return ""
    current_hash = _file_hash(target_file)
    cache_key = (target_file, error_line, current_hash)
    if cache_key in goal_cache:
        cached = goal_cache[cache_key]
    else:
        try:
            cached = registry.call(
                "get_lean_goal", file_path=target_file, sorry_line=error_line
            )
        except Exception:
            return ""
        goal_cache[cache_key] = cached
    if not cached or cached.get("error") or not cached.get("goal"):
        return ""
    result = f"## Lean Goal State at Error Line {error_line} (from LSP — authoritative)\n"
    result += f"{cached['goal']}\n"
    hyps = (cached.get("hypotheses") or [])[:6]
    if hyps:
        result += f"  Hypotheses: {'; '.join(hyps)}\n"
    return result + "\n"


def _parse_sorry_classification(guidance: str) -> list[dict]:
    """Extract per-sorry TACTICAL/STRUCTURAL classifications from Agent2 guidance.

    Looks for a block of the form (anywhere in the guidance):
      ## SORRY CLASSIFICATION
      - Line N: STRUCTURAL — <reason>
        dependency_symbols: [...]
        diagnosis: "..."
      - Line M: TACTICAL — <tactic hint>

    Returns a list of dicts, each with keys:
      line (int), type ("STRUCTURAL"|"TACTICAL"), reason (str),
      dependency_symbols (list[str]), diagnosis (str), tactic_hint (str)

    Tolerant: returns [] when the block is absent or malformed.
    """
    results: list[dict] = []
    # Locate the classification section (case-insensitive header match).
    section_re = re.compile(
        r"##\s*SORRY\s+CLASSIFICATION\b.*?(?=\n##|\Z)",
        re.DOTALL | re.IGNORECASE,
    )
    m = section_re.search(guidance)
    if not m:
        return results

    block = m.group(0)

    # Each entry starts with "- Line N: TYPE — reason".
    # TYPE may be STRUCTURAL_GLUE, STRUCTURAL_INTERFACE, STRUCTURAL (legacy), or TACTICAL.
    entry_re = re.compile(
        r"-\s+Line\s+(\d+)\s*:\s*"
        r"(STRUCTURAL_GLUE|STRUCTURAL_INTERFACE|STRUCTURAL|TACTICAL)"
        r"\s*[—\-]+\s*(.+?)(?=\n\s*-\s+Line\s|\Z)",
        re.DOTALL | re.IGNORECASE,
    )
    dep_re = re.compile(r'dependency_symbols\s*:\s*(\[[^\]]*\])', re.IGNORECASE)
    diag_re = re.compile(r'diagnosis\s*:\s*"([^"]*)"', re.IGNORECASE)

    for entry_m in entry_re.finditer(block):
        line_no = int(entry_m.group(1))
        raw_type = entry_m.group(2).upper()
        # Normalise: STRUCTURAL_GLUE / STRUCTURAL_INTERFACE → type="STRUCTURAL" + subtype
        # STRUCTURAL (legacy) → type="STRUCTURAL", subtype="STRUCTURAL_INTERFACE" (default)
        # TACTICAL → type="TACTICAL", subtype="TACTICAL"
        if raw_type.startswith("STRUCTURAL"):
            sorry_type = "STRUCTURAL"
            subtype = raw_type  # "STRUCTURAL_GLUE", "STRUCTURAL_INTERFACE", or "STRUCTURAL"
            if subtype == "STRUCTURAL":
                subtype = "STRUCTURAL_INTERFACE"  # legacy default
        else:
            sorry_type = "TACTICAL"
            subtype = "TACTICAL"
        body = entry_m.group(3)
        reason = body.splitlines()[0].strip() if body.strip() else ""

        dep_symbols: list[str] = []
        dep_match = dep_re.search(body)
        if dep_match:
            try:
                dep_symbols = json.loads(dep_match.group(1))
            except (json.JSONDecodeError, ValueError):
                dep_symbols = [
                    s.strip().strip('"\'')
                    for s in dep_match.group(1).strip("[]").split(",")
                    if s.strip()
                ]

        diagnosis = ""
        diag_match = diag_re.search(body)
        if diag_match:
            diagnosis = diag_match.group(1).strip()

        results.append({
            "line": line_no,
            "type": sorry_type,       # "STRUCTURAL" or "TACTICAL" (backward-compat)
            "subtype": subtype,        # "STRUCTURAL_GLUE", "STRUCTURAL_INTERFACE", or "TACTICAL"
            "reason": reason,
            "dependency_symbols": dep_symbols,
            "diagnosis": diagnosis,
            "tactic_hint": reason if sorry_type == "TACTICAL" else "",
        })

    return results


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


