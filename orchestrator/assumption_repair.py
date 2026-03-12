"""Automatic assumption repair engine for the StochOptLib orchestrator.

When Agent5 (diagnostician) identifies missing assumptions or deterministic
staging proof errors, this module applies patches without human intervention.

Two repair categories:

1. Missing Assumption Repair:
   - Extract unsolved goals from Lean build errors
   - Classify each goal as MISSING_ASSUMPTION or PROOF_OBLIGATION
   - Generate a hypothesis name and type
   - Patch the theorem signature (and propagate upward to callers)

2. Staging Auto-Fix:
   - Rule-based repair for two known deterministic error patterns in
     Lib/Glue/Staging/ files:
     (a) Over-specified simp set (def-unfold item causes unsolved goals)
     (b) `exact h_xxx` after `convert ... using 1` needs `funext`
"""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

from orchestrator.config import PROJECT_ROOT

# ---------------------------------------------------------------------------
# Goal extraction — parse `lake build` stderr for unsolved goal blocks
# ---------------------------------------------------------------------------

# Matches a Lean error block:
#   path/to/file.lean:LINE:COL: error: MESSAGE
_LEAN_ERROR_RE = re.compile(
    r"(\S+\.lean):(\d+):(\d+): error: (.+?)(?=\n\S+\.lean:|\Z)",
    re.DOTALL,
)

# Matches the `⊢ GOAL` line(s) inside an unsolved-goals block.
_GOAL_LINE_RE = re.compile(r"⊢\s*(.+)", re.MULTILINE)

# The `unsolved goals` error message body — goals follow immediately after.
_UNSOLVED_GOALS_RE = re.compile(
    r"unsolved goals\n(.*?)(?=\n\S+\.lean:|\Z)", re.DOTALL
)


def extract_unsolved_goals(error_text: str) -> list[dict[str, Any]]:
    """Parse lake build error output and return all unsolved goal records.

    Returns a list of dicts:
      {"file": str, "line": int, "col": int, "goal": str}
    """
    results: list[dict[str, Any]] = []
    for m in _LEAN_ERROR_RE.finditer(error_text):
        file_, line, col, body = m.group(1), int(m.group(2)), int(m.group(3)), m.group(4)
        if "unsolved goals" not in body:
            continue
        for goal_m in _GOAL_LINE_RE.finditer(body):
            goal = goal_m.group(1).strip()
            if goal:
                results.append({"file": file_, "line": line, "col": col, "goal": goal})
    return results


# ---------------------------------------------------------------------------
# Goal classification — rule-based, no LLM needed
# ---------------------------------------------------------------------------

# Goals starting with these prefixes are input assumptions that can be added
# to the theorem signature.  All others are proof obligations.
_ASSUMPTION_PREFIXES = (
    "Integrable ",
    "AEMeasurable ",
    "Measurable ",
    "IsProbabilityMeasure",
    "HasBoundedVariance",
    "AEStronglyMeasurable ",
    "MeasureTheory.Integrable ",
    "MeasureTheory.AEMeasurable ",
    "MeasureTheory.AEStronglyMeasurable ",
)


def classify_goal(goal: str) -> str:
    """Return 'MISSING_ASSUMPTION' or 'PROOF_OBLIGATION' for a single goal."""
    stripped = goal.lstrip("⊢ ")
    for prefix in _ASSUMPTION_PREFIXES:
        if stripped.startswith(prefix):
            return "MISSING_ASSUMPTION"
    return "PROOF_OBLIGATION"


def all_goals_are_assumptions(goals: list[dict[str, Any]]) -> bool:
    """True iff every extracted goal is a missing-assumption type."""
    return bool(goals) and all(classify_goal(g["goal"]) == "MISSING_ASSUMPTION" for g in goals)


# ---------------------------------------------------------------------------
# Hypothesis naming — deterministic names from goal type
# ---------------------------------------------------------------------------

def generate_hyp_name(goal: str, existing_names: set[str] | None = None) -> str:
    """Generate a hypothesis name from an unsolved goal string.

    Names follow the h_<kind>_<suffix> convention used in the codebase.
    A numeric suffix is appended if the base name already exists.
    """
    stripped = goal.lstrip("⊢ ")

    if stripped.startswith(("Integrable ", "MeasureTheory.Integrable ")):
        # Try to extract the function description for a better name
        if "‖" in stripped and "‖ ^ 2" in stripped:
            base = "h_int_norm_sq"
        elif "inner" in stripped.lower() or "⟪" in stripped:
            base = "h_int_inner"
        elif "gradL" in stripped or "gradF" in stripped:
            base = "h_int_grad"
        elif "oracle" in stripped.lower():
            base = "h_int_oracle"
        else:
            base = "h_int"
    elif stripped.startswith(("Measurable ", "AEMeasurable ",
                               "MeasureTheory.AEMeasurable ",
                               "AEStronglyMeasurable ",
                               "MeasureTheory.AEStronglyMeasurable ")):
        if "process" in stripped.lower() or "svrgProcess" in stripped:
            base = "h_meas_process"
        elif "gradL" in stripped or "gradF" in stripped:
            base = "h_meas_grad"
        else:
            base = "h_meas"
    elif stripped.startswith("IsProbabilityMeasure"):
        base = "h_prob"
    elif stripped.startswith("HasBoundedVariance"):
        base = "h_bdd_var"
    else:
        base = "h_assm"

    if existing_names is None or base not in existing_names:
        return base

    # Append numeric suffix to avoid collision
    i = 2
    while f"{base}_{i}" in existing_names:
        i += 1
    return f"{base}_{i}"


# ---------------------------------------------------------------------------
# Signature patcher — insert hypothesis into theorem declaration
# ---------------------------------------------------------------------------

def _find_theorem_sig_end(content: str, theorem_name: str) -> tuple[int, int] | None:
    """Find the byte range of the theorem signature.

    Returns (sig_end_pos, colon_pos) where sig_end_pos is the position just
    before the final ' :' that precedes ':=' / 'by', so we can insert a new
    hypothesis there.

    Returns None if the theorem is not found.
    """
    # Match 'theorem NAME' or 'lemma NAME'
    decl_re = re.compile(
        r"\b(?:theorem|lemma)\s+" + re.escape(theorem_name) + r"\b"
    )
    m = decl_re.search(content)
    if not m:
        return None

    start = m.start()
    # Scan forward from the declaration to find ' :=' or the block opener 'by'
    # that is NOT inside parentheses/brackets.
    depth = 0
    i = m.end()
    last_colon_before_close: int | None = None
    n = len(content)
    while i < n:
        ch = content[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif depth == 0:
            # Look for ':=' at top level
            if content[i : i + 2] == ":=":
                return (i, i)
            # Look for standalone 'by' at top level (not inside identifiers)
            if content[i : i + 2] == "by" and (i == 0 or not content[i - 1].isalnum()):
                next_ch = content[i + 2] if i + 2 < n else ""
                if not next_ch.isalnum() and next_ch not in ("_",):
                    return (i, i)
        i += 1
    return None


def patch_signature(
    file_path: Path,
    theorem_name: str,
    hyp_name: str,
    hyp_type: str,
    insert_after_hyp: str | None = None,
) -> bool:
    """Insert (hyp_name : hyp_type) into the signature of theorem_name.

    If insert_after_hyp is given, insert after that parameter.  Otherwise,
    insert just before the ':=' / 'by' body opener.

    Returns True if the file was modified, False if theorem not found.
    """
    content = file_path.read_text(encoding="utf-8")
    new_hyp = f"    ({hyp_name} : {hyp_type})"

    if insert_after_hyp:
        # Find the closing paren of the named hypothesis
        pattern = re.compile(
            r"\(" + re.escape(insert_after_hyp) + r"\s*:[^)]+\)"
        )
        m = pattern.search(content)
        if m:
            insert_pos = m.end()
            new_content = content[:insert_pos] + "\n" + new_hyp + content[insert_pos:]
            file_path.write_text(new_content, encoding="utf-8")
            return True

    # Fall back: insert just before ':=' or 'by'
    result = _find_theorem_sig_end(content, theorem_name)
    if result is None:
        return False

    sig_end, _ = result
    # Insert the hypothesis on a new line before the body opener
    new_content = content[:sig_end] + new_hyp + "\n    " + content[sig_end:]
    file_path.write_text(new_content, encoding="utf-8")
    return True


# ---------------------------------------------------------------------------
# Caller propagation — find callers and pass through new hypotheses
# ---------------------------------------------------------------------------

def find_callers_in_file(file_path: Path, callee_name: str) -> list[str]:
    """Return names of theorems in file_path that call callee_name."""
    content = file_path.read_text(encoding="utf-8")
    # Find all theorem/lemma declarations
    decl_re = re.compile(r"\b(?:theorem|lemma)\s+(\w+)\b")
    callers: list[str] = []
    decl_positions: list[tuple[str, int]] = [
        (m.group(1), m.start()) for m in decl_re.finditer(content)
    ]
    for i, (name, pos) in enumerate(decl_positions):
        end = decl_positions[i + 1][1] if i + 1 < len(decl_positions) else len(content)
        body = content[pos:end]
        if re.search(r"\b" + re.escape(callee_name) + r"\b", body):
            callers.append(name)
    return callers


def _hyp_already_present(file_path: Path, theorem_name: str, hyp_type: str) -> bool:
    """True if theorem_name already has a hypothesis with matching type."""
    content = file_path.read_text(encoding="utf-8")
    decl_re = re.compile(r"\b(?:theorem|lemma)\s+" + re.escape(theorem_name) + r"\b")
    m = decl_re.search(content)
    if not m:
        return False
    result = _find_theorem_sig_end(content, theorem_name)
    if result is None:
        return False
    sig = content[m.start() : result[0]]
    # Simple substring check — types are long enough that false positives are rare
    return hyp_type.replace(" ", "") in sig.replace(" ", "")


def propagate_assumption(
    file_path: Path,
    callee_name: str,
    hyp_name: str,
    hyp_type: str,
) -> int:
    """Add hyp_name to all callers of callee_name in file_path.

    Returns count of theorems patched.
    """
    callers = find_callers_in_file(file_path, callee_name)
    patched = 0
    for caller in callers:
        if caller == callee_name:
            continue
        if _hyp_already_present(file_path, caller, hyp_type):
            continue
        if patch_signature(file_path, caller, hyp_name, hyp_type):
            patched += 1
    return patched


# ---------------------------------------------------------------------------
# Apply assumption patches from Agent5's structured diagnosis
# ---------------------------------------------------------------------------

def apply_assumption_patches(
    target_file: str,
    assumptions_to_add: list[dict[str, Any]],
    *,
    propagate: bool = True,
) -> int:
    """Apply a list of assumption patches from Agent5's JSON diagnosis.

    Each entry:
      {"theorem": str, "hyp_name": str, "hyp_type": str, "insert_after": str|null}

    Returns number of successful patches.
    """
    file_path = Path(target_file) if Path(target_file).is_absolute() else PROJECT_ROOT / target_file
    if not file_path.exists():
        return 0

    patched = 0
    seen_hypotheses: set[tuple[str, str]] = set()

    for entry in assumptions_to_add:
        theorem = entry.get("theorem", "")
        hyp_name = entry.get("hyp_name", "")
        hyp_type = entry.get("hyp_type", "")
        insert_after = entry.get("insert_after")

        if not (theorem and hyp_name and hyp_type):
            continue

        key = (theorem, hyp_name)
        if key in seen_hypotheses:
            continue
        seen_hypotheses.add(key)

        if _hyp_already_present(file_path, theorem, hyp_type):
            continue

        if patch_signature(file_path, theorem, hyp_name, hyp_type, insert_after):
            patched += 1
            if propagate:
                propagate_assumption(file_path, theorem, hyp_name, hyp_type)

    return patched


# ---------------------------------------------------------------------------
# Staging auto-fix rules
# ---------------------------------------------------------------------------

# Pattern: line reports "unsolved goals" and the offending code line contains
# a simp call that mixes a *definition* simp lemma with @[simp] lemmas.
#
# We detect this by checking if the simp set contains a term that looks like
# a namespace-qualified *definition* (e.g. SVRGSetup.svrgProcess) alongside
# @[simp]-tagged lemmas (e.g. SVRGSetup.process_zero).
#
# Heuristic: any `Namespace.name` where `name` starts with a lowercase letter
# and does NOT end in a recognisable simp-lemma suffix pattern is a def unfold.

_SIMP_CALL_RE = re.compile(r"(simp\s*\[)([^\]]+)(\])")
_DEF_UNFOLD_ITEM_RE = re.compile(
    r"\b([A-Z]\w+\.[a-z]\w+)\b"  # e.g. SVRGSetup.svrgProcess
)
_SIMP_LEMMA_SUFFIXES = (
    "process_zero", "process_succ", "process_step",
    "_zero", "_succ", "_base", "_step", "_def",
)


def _is_def_unfold(item: str) -> bool:
    """Return True if `item` looks like a definition-unfold (not a simp lemma)."""
    item = item.strip()
    m = _DEF_UNFOLD_ITEM_RE.match(item)
    if not m:
        return False
    # If it ends with a known simp-lemma suffix it's a legitimate simp lemma
    for suffix in _SIMP_LEMMA_SUFFIXES:
        if item.endswith(suffix):
            return False
    return True


def _fix_overspecified_simp(line: str) -> str | None:
    """Remove def-unfold items from a simp call.  Returns fixed line or None."""
    m = _SIMP_CALL_RE.search(line)
    if not m:
        return None
    items = [i.strip() for i in m.group(2).split(",")]
    def_unfolds = [i for i in items if _is_def_unfold(i)]
    if not def_unfolds:
        return None
    kept = [i for i in items if i not in def_unfolds]
    if not kept:
        return None
    new_simp = m.group(1) + ", ".join(kept) + m.group(3)
    return line[: m.start()] + new_simp + line[m.end() :]


# Pattern: "No goals to be solved" at an `exact h_xxx` line that follows
# `convert ... using 1`.  Fix: exact h_xxx → exact funext h_xxx.
_EXACT_RE = re.compile(r"^(\s*)(exact\s+)(\w+)(\s*)$")


def _fix_exact_needs_funext(line: str) -> str | None:
    """Wrap `exact h` with `exact funext h` if the exact pattern matches."""
    m = _EXACT_RE.match(line)
    if not m:
        return None
    # Only apply to identifiers that look like hypothesis names (h_xxx)
    name = m.group(3)
    if not (name.startswith("h_") or name.startswith("h")):
        return None
    return m.group(1) + "exact funext " + name + m.group(4)


def _find_actual_tactic_line(lines: list[str], error_lineno: int, error_msg: str) -> int:
    """Resolve the Lean error line to the actual failing tactic.

    Lean reports "unsolved goals" / "No goals to be solved" at the position of
    the ``by`` keyword that opens a tactic block (e.g. the end of a long
    ``have ... := by`` declaration), NOT at the failing tactic inside.

    This helper scans forward from *error_lineno* up to 10 lines to find the
    first line whose content matches the expected failing tactic:
    - ``simp`` for "unsolved goals"
    - ``exact`` for "No goals to be solved"

    If the error line does not end with ``by``, it is returned unchanged.
    """
    if error_lineno < 1 or error_lineno > len(lines):
        return error_lineno
    line = lines[error_lineno - 1]
    if not line.rstrip().endswith("by"):
        return error_lineno
    for offset in range(1, 10):
        idx = error_lineno - 1 + offset
        if idx >= len(lines):
            break
        candidate = lines[idx]
        if "unsolved goals" in error_msg and "simp" in candidate:
            return error_lineno + offset
        if "No goals to be solved" in error_msg and "exact" in candidate:
            return error_lineno + offset
    return error_lineno


def apply_staging_rules(
    staging_path: Path,
    error_text: str,
) -> int:
    """Apply deterministic fix rules to a staging file.

    Returns number of lines fixed.
    """
    if not staging_path.exists():
        return 0

    lines = staging_path.read_text(encoding="utf-8").splitlines(keepends=True)

    # Build a map of error-line → error-message from the error output
    error_by_line: dict[int, str] = {}
    for m in re.finditer(
        re.escape(staging_path.name) + r":(\d+):\d+: error: (.+?)(?=\n\S|\Z)",
        error_text,
        re.DOTALL,
    ):
        lineno = int(m.group(1))
        msg = m.group(2).strip()
        error_by_line[lineno] = msg

    if not error_by_line:
        # Also try relative path match (skip if outside project root)
        try:
            rel = str(staging_path.relative_to(PROJECT_ROOT))
        except ValueError:
            rel = staging_path.name
        for m in re.finditer(
            re.escape(rel) + r":(\d+):\d+: error: (.+?)(?=\n\S|\Z)",
            error_text,
            re.DOTALL,
        ):
            lineno = int(m.group(1))
            error_by_line[lineno] = m.group(2).strip()

    if not error_by_line:
        return 0

    fixed = 0
    for lineno, msg in error_by_line.items():
        if lineno < 1 or lineno > len(lines):
            continue
        # Lean reports errors at the `by` keyword, not at the failing tactic.
        # Resolve to the actual tactic line before applying any fix.
        actual_lineno = _find_actual_tactic_line(lines, lineno, msg)
        if actual_lineno < 1 or actual_lineno > len(lines):
            actual_lineno = lineno
        idx = actual_lineno - 1
        original = lines[idx]

        # Simp over-specification: "simp made no progress", "unknown identifier … simp",
        # or residual "unsolved goals" after a bad simp call.
        _simp_related = (
            "simp made no progress" in msg
            or "unknown identifier" in msg and "simp" in msg
            or "unsolved goals" in msg
        )
        if _simp_related:
            fixed_line = _fix_overspecified_simp(original)
            if fixed_line is not None:
                lines[idx] = fixed_line
                fixed += 1

        # "No goals to be solved" has two distinct meanings depending on context:
        #   (a) Lean hinted "try 'exact funext h'" → the exact needs funext wrapping
        #   (b) No funext hint → `convert` already closed all goals; the `exact` is
        #       redundant and should be deleted
        if "No goals to be solved" in msg:
            if "exact funext" in msg:
                # Case (a): Lean suggested funext
                fixed_line = _fix_exact_needs_funext(original)
                if fixed_line is not None:
                    lines[idx] = fixed_line
                    fixed += 1
            elif original.strip().startswith("exact "):
                # Case (b): redundant exact — replace with empty string
                lines[idx] = ""
                fixed += 1

        # `exact h` that should be `exact funext h` due to "type mismatch" with
        # an explicit funext hint in the error message.
        elif "exact funext" in msg or ("type mismatch" in msg and "exact" in original):
            fixed_line = _fix_exact_needs_funext(original)
            if fixed_line is not None:
                lines[idx] = fixed_line
                fixed += 1
            else:
                # Also try the line immediately before the error line
                # (the `exact` might be on the same line as `convert` output)
                if actual_lineno >= 2:
                    prev_line = lines[actual_lineno - 2]
                    fixed_prev = _fix_exact_needs_funext(prev_line.rstrip("\n"))
                    if fixed_prev is not None:
                        lines[actual_lineno - 2] = fixed_prev + "\n"
                        fixed += 1

    if fixed > 0:
        staging_path.write_text("".join(lines), encoding="utf-8")

    return fixed


# ---------------------------------------------------------------------------
# LM staging patch application — for when rule engine returns 0
# ---------------------------------------------------------------------------

def apply_lm_staging_patches(
    staging_path: Path,
    patches: list[dict[str, Any]],
) -> int:
    """Apply LLM-generated search/replace patches to the staging file.

    Each patch entry must have ``search`` (exact verbatim text to replace) and
    ``replace`` (corrected Lean code).  Only patches whose ``search`` string is
    found exactly once in the file are applied.

    Returns the number of patches successfully applied.
    """
    if not staging_path.exists() or not patches:
        return 0

    content = staging_path.read_text(encoding="utf-8")
    applied = 0
    for patch in patches:
        if not isinstance(patch, dict):
            continue
        search = patch.get("search", "")
        replace = patch.get("replace", "")
        if not search:
            continue
        occurrences = content.count(search)
        if occurrences != 1:
            # Skip ambiguous or missing patches
            continue
        content = content.replace(search, replace, 1)
        applied += 1

    if applied > 0:
        staging_path.write_text(content, encoding="utf-8")
    return applied


# ---------------------------------------------------------------------------
# Parse structured JSON from Agent5 diagnosis text
# ---------------------------------------------------------------------------

_JSON_BLOCK_RE = re.compile(r"```(?:json)?\s*(\{.*?\})\s*```", re.DOTALL)


def parse_diagnosis_json(diagnosis_text: str) -> dict[str, Any]:
    """Extract and parse the structured JSON block from Agent5's diagnosis.

    Returns the parsed dict, or {"auto_repairable": False} if no valid JSON.
    Required keys validated: classification (str), auto_repairable (bool).
    """
    for m in _JSON_BLOCK_RE.finditer(diagnosis_text):
        try:
            data = json.loads(m.group(1))
            if not isinstance(data, dict):
                continue
            # Enforce required keys
            if "classification" not in data:
                data["classification"] = "UNKNOWN"
            if "auto_repairable" not in data:
                data["auto_repairable"] = False
            # Validate assumptions_to_add entries
            if "assumptions_to_add" in data:
                valid = []
                for entry in data["assumptions_to_add"]:
                    if not isinstance(entry, dict):
                        continue
                    if not entry.get("theorem") or not entry.get("hyp_name") or not entry.get("hyp_type"):
                        continue
                    valid.append(entry)
                data["assumptions_to_add"] = valid
                if not valid:
                    data["auto_repairable"] = False
            return data
        except json.JSONDecodeError:
            continue
    return {"auto_repairable": False, "classification": "UNKNOWN"}


# ---------------------------------------------------------------------------
# Theorem-location helpers — find which theorem contains a given line
# ---------------------------------------------------------------------------

def detect_theorem_at_line(file_path: Path, line_no: int) -> str | None:
    """Find the theorem/lemma name that contains the given 1-based line number.

    Searches backwards from *line_no* for the nearest `theorem`/`lemma`
    declaration.  Returns the declaration name, or None if not found.
    """
    try:
        lines = file_path.read_text(encoding="utf-8").split("\n")
    except OSError:
        return None
    decl_re = re.compile(r"\b(?:theorem|lemma)\s+(\w+)\b")
    limit = min(line_no - 1, len(lines) - 1)
    for i in range(limit, -1, -1):
        m = decl_re.search(lines[i])
        if m:
            return m.group(1)
    return None


def goals_to_patch_list(
    goals: list[dict[str, Any]],
    file_path: Path,
    *,
    existing_names: set[str] | None = None,
) -> list[dict[str, Any]]:
    """Convert extracted unsolved goals into patch entries for apply_assumption_patches.

    Only MISSING_ASSUMPTION goals are included.  Duplicate types are deduplicated.
    Each entry has: theorem, hyp_name, hyp_type, insert_after (None).
    """
    patches: list[dict[str, Any]] = []
    seen_types: set[str] = set()
    _names: set[str] = set(existing_names) if existing_names else set()

    for g in goals:
        if classify_goal(g["goal"]) != "MISSING_ASSUMPTION":
            continue
        hyp_type = g["goal"].lstrip("⊢ ").strip()
        if not hyp_type or hyp_type in seen_types:
            continue
        seen_types.add(hyp_type)

        theorem_name = detect_theorem_at_line(file_path, g["line"])
        if not theorem_name:
            continue

        hyp_name = generate_hyp_name(hyp_type, _names)
        _names.add(hyp_name)

        patches.append({
            "theorem": theorem_name,
            "hyp_name": hyp_name,
            "hyp_type": hyp_type,
            "insert_after": None,
        })

    return patches
