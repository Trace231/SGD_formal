"""Automatic assumption repair engine for the StochOptLib orchestrator.

When Agent5 (diagnostician) identifies missing assumptions, this module
applies patches without human intervention.

Repair category:

1. Missing Assumption Repair:
   - Extract unsolved goals from Lean build errors
   - Classify each goal as MISSING_ASSUMPTION or PROOF_OBLIGATION
   - Generate a hypothesis name and type
   - Patch the theorem signature (and propagate upward to callers)
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
