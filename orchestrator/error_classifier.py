"""Lean error parsing, classification, and LLM-assisted diagnosis."""
from __future__ import annotations

import json
import re
from concurrent.futures import ThreadPoolExecutor, TimeoutError as FuturesTimeoutError
from pathlib import Path

from orchestrator.config import AGENT_CONFIGS, PROJECT_ROOT
from orchestrator.providers import call_llm
from orchestrator.prompts import build_error_classification_prompt

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

# Structural field/projection errors in declaration zone — route to Agent7.
_FIELD_NOTATION_RE = re.compile(
    r"Invalid field notation|does not have a field",
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
                                 (e.g. import dep) → fix dep, do NOT rewrite target.
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

    # Normalise target path for comparison.
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
            return ep.name == tp.name

    target_errors = [e for e in errors if _is_target_file(e["file"])]
    dep_errors = [e for e in errors if not _is_target_file(e["file"])]

    # Primary errors come from a dependency file — route to dep-fix branch.
    if dep_errors and not target_errors:
        return "DEPENDENCY_COMPILE_ERROR", errors

    # Even if some target errors exist, if the primary (first) error is in a dep, treat
    # as dependency compile error.
    if dep_errors and errors[0]["file"] and not _is_target_file(errors[0]["file"]):
        return "DEPENDENCY_COMPILE_ERROR", errors

    # Build per-declaration zone map once for this target file.
    tgt_path = PROJECT_ROOT / target_file
    try:
        _tgt_lines = tgt_path.read_text(encoding="utf-8").splitlines()
        _decl_zones = _build_decl_zone_map(_tgt_lines)
    except OSError:
        _tgt_lines = []
        _decl_zones = []

    # Conservative fallback flag: when zone detection yielded no zones (file
    # unreadable, or only has declarations without closeable := by) we cannot
    # distinguish declaration zone from proof body.  In that case we prefer to
    # escalate interface-like errors rather than silently route to LOCAL_PROOF_ERROR.
    _zone_detection_uncertain = len(_decl_zones) == 0

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
            if _is_in_declaration_zone(line, _decl_zones):
                return "DEFINITION_ZONE_ERROR", errors
            # Conservative fallback: when zone detection is uncertain, prefer
            # DEFINITION_ZONE_ERROR over PROOF_ERROR for type-mismatch errors.
            if _zone_detection_uncertain:
                return "DEFINITION_ZONE_ERROR", errors

        if _FIELD_NOTATION_RE.search(msg):
            if _is_in_declaration_zone(line, _decl_zones):
                return "DEFINITION_ZONE_ERROR", errors
            # Conservative fallback: field notation errors are almost always API
            # mismatches; prefer DEFINITION_ZONE_ERROR when zone detection is uncertain.
            if _zone_detection_uncertain:
                return "DEFINITION_ZONE_ERROR", errors
            # In proof body and zone detection is reliable — fall through to PROOF_ERROR

        if _UNKNOWN_SYMBOL_RE.search(msg):
            # Only SIGNATURE_HALLUCINATION when error is in the declaration zone.
            if _is_in_declaration_zone(line, _decl_zones):
                return "SIGNATURE_HALLUCINATION", errors
            # Conservative fallback: unknown symbol outside any mapped zone is most
            # likely an API/interface mismatch (e.g. calling a non-existent function
            # in an equation-style def body that wasn't captured in the zone map).
            # Prefer SIGNATURE_HALLUCINATION (forces Agent7/rewrite) over LOCAL_PROOF_ERROR.
            if _zone_detection_uncertain:
                return "SIGNATURE_HALLUCINATION", errors
            return "LOCAL_PROOF_ERROR", errors

    # Conservative end-of-loop: if none of the per-error checks triggered a return
    # but all errors are interface-like (type mismatch family), prefer DEFINITION_ZONE_ERROR
    # over PROOF_ERROR so Agent7/Agent2 is consulted.
    _all_interface_like = all(
        _TYPE_MISMATCH_RE.search(e["message"])
        or _FIELD_NOTATION_RE.search(e["message"])
        or _UNKNOWN_SYMBOL_RE.search(e["message"])
        for e in target_errors
    ) if target_errors else False
    if _all_interface_like:
        return "DEFINITION_ZONE_ERROR", errors

    return "PROOF_ERROR", errors


_DECL_START_RE = re.compile(
    r"^(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev)\s"
)
_PROOF_BODY_RE = re.compile(r":=\s*by\b|:=\s*$")

# Top-level Lean 4 structural keywords that end any open declaration block.
# When one of these appears at column 0 (not indented), any pending equation-style
# def tracking should be closed.
_TOP_LEVEL_RESET_RE = re.compile(
    r"^(?:structure|class|instance|inductive|mutual|section|namespace|end|open|set_option|#)\s*",
    re.IGNORECASE,
)


def _build_decl_zone_map(lines: list[str]) -> list[tuple[int, int]]:
    """Return a list of (sig_start, sig_end) pairs — one per declaration.

    sig_start is the 1-indexed line of the ``theorem``/``lemma``/``def`` keyword.
    sig_end   is the 1-indexed line of the closing marker for that declaration.

    **Closing rules** (in priority order):
    1. ``:= by`` / ``:=`` alone on its line — standard proof-body opener.
    2. A *new* top-level declaration keyword at the same or outer indentation level —
       this handles **equation-style** ``def``/``abbrev`` declarations that use
       ``| pattern => body`` syntax instead of ``:= by``.  The previous open zone is
       closed at the line immediately before the new declaration.
    3. A structural keyword (``structure``, ``namespace``, ``end``, …) at column 0
       — always terminates any open tracking.
    4. End-of-file — closes any still-open declaration.

    This means the body of an equation-style def (its ``| branch =>`` lines) is
    part of its zone, so type-API errors inside branches are correctly identified
    as declaration-zone (interface) errors and routed to Agent7/Agent2.
    """
    zones: list[tuple[int, int]] = []
    decl_start: int | None = None
    for i, line in enumerate(lines, start=1):
        stripped = line.strip()

        # Rule 3: structural keyword at column 0 resets tracking.
        if not line or (line[0] != " " and line[0] != "\t" and _TOP_LEVEL_RESET_RE.match(stripped)):
            if decl_start is not None:
                # Close the previous open declaration conservatively.
                zones.append((decl_start, i - 1))
                decl_start = None

        # Rule 2: a NEW top-level declaration while one is already open → close old one.
        if _DECL_START_RE.match(stripped):
            if decl_start is not None:
                # The previous declaration was equation-style (never saw := by).
                # Close it at the line before this new declaration starts.
                zones.append((decl_start, i - 1))
            decl_start = i
            continue  # don't fall into rule 1 for the opening line itself

        # Rule 1: proof-body opener for the current := by / := style declaration.
        if decl_start is not None and _PROOF_BODY_RE.search(line):
            zones.append((decl_start, i))
            decl_start = None

    # Rule 4: end-of-file closes any still-open declaration.
    if decl_start is not None:
        zones.append((decl_start, len(lines)))

    return zones


def _is_in_declaration_zone(error_line: int, decl_zone_map: list[tuple[int, int]]) -> bool:
    """Return True iff *error_line* falls within any declaration's signature zone.

    A line is "in the declaration zone" of a declaration D when it lies between
    D's keyword line and the ``:= by`` / ``:=`` line (inclusive on both ends).
    Lines in proof bodies (after ``:= by``) are NOT in any declaration zone.
    """
    for sig_start, sig_end in decl_zone_map:
        if sig_start <= error_line <= sig_end:
            return True
    return False


def _get_decl_zone_end(tgt_path: Path) -> int:
    """Return the last line number of the declaration zone in a Lean file.

    Kept for backward compatibility with callers that only need a single
    threshold (e.g. legacy fallback paths).  New code should use
    ``_build_decl_zone_map`` + ``_is_in_declaration_zone`` for per-error
    accuracy in multi-theorem files.

    Returns the sig_end of the LAST declaration whose signature we can parse,
    or ``_PROOF_BODY_LINE_THRESHOLD`` if the file is unreadable / has no decls.
    """
    if not tgt_path.exists():
        return _PROOF_BODY_LINE_THRESHOLD
    try:
        lines = tgt_path.read_text(encoding="utf-8").splitlines()
    except OSError:
        return _PROOF_BODY_LINE_THRESHOLD

    zones = _build_decl_zone_map(lines)
    if zones:
        # Return the sig_end of the last parsed declaration so that the threshold
        # covers the full file's declaration zones rather than stopping at the first.
        return zones[-1][1]
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
        return ep.name == tp.name


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
    blocked_sorry_count = int(verify_result.get("blocked_sorry_count", 0))
    if blocked_sorry_count > 0:
        n_clean = int(verify_result.get("sorry_declarations", 0))
        parts.extend([
            "",
            f"### Blocked sorrys: {blocked_sorry_count} of {sorry_count} source sorrys are "
            f"inside declarations that have compile errors above.",
            f"Only {n_clean} declaration(s) have clean sorrys (no other errors).",
            "**Fix the compilation errors listed above BEFORE attempting to fill any sorry.**",
            "Filling a sorry inside a broken declaration will have no effect until the "
            "declaration compiles successfully.",
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
    3. All other dependency errors

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
        is_target = efile == target_basename
        tier = 0 if near_edit else (1 if is_target else 2)
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

