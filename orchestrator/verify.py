"""Verification gates for the orchestration pipeline.

Hard gates (block pipeline on failure):
  1. Glue reuse >= 50%  (pre-proof)
  2. lake build exit 0 + sorry = 0  (post-proof)
  3. GLUE_TRICKS validation gate  (post-persistence, BLOCKING)
  4. Used-in tag check  (post-persistence)

Soft check:
  - Probe selection criteria (printed warning, human confirms)
"""

from __future__ import annotations

import re
import subprocess
from dataclasses import dataclass
from pathlib import Path

from orchestrator.config import LEAN_BUILD_TIMEOUT, LEVERAGE_THRESHOLD, PROJECT_ROOT


# ---------------------------------------------------------------------------
# Data classes
# ---------------------------------------------------------------------------

@dataclass
class BuildResult:
    success: bool
    errors: str
    sorry_count: int
    returncode: int


# ---------------------------------------------------------------------------
# Hard Gate 2: lake build + sorry count
# ---------------------------------------------------------------------------

def lake_build(target: str | None = None) -> BuildResult:
    """Run ``lake build`` and count remaining sorry's in the target file.

    If *target* is ``None`` the default ``lake build`` is run (builds the
    whole project).
    """
    cmd = ["lake", "build"]
    if target:
        cmd.append(target)

    result = subprocess.run(
        cmd,
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
        timeout=LEAN_BUILD_TIMEOUT,
    )
    errors = (result.stderr + result.stdout) if result.returncode != 0 else ""
    sorry_count = _count_sorry_in_output(result.stderr + result.stdout)
    return BuildResult(
        success=result.returncode == 0 and sorry_count == 0,
        errors=errors,
        sorry_count=sorry_count,
        returncode=result.returncode,
    )


def count_sorrys(filepath: str | Path) -> int:
    """Count sorry and admit (both are proof placeholders) in a Lean source file."""
    p = Path(filepath)
    if not p.is_absolute():
        p = PROJECT_ROOT / p
    if not p.exists():
        return 0
    content = p.read_text(encoding="utf-8")
    return _count_sorry_in_source(content)


_SORRY_SOURCE_RE = re.compile(r"\bsorry\b")
_ADMIT_SOURCE_RE = re.compile(r"\badmit\b")
# Only match the Lean compiler's semantic warning, not raw "sorry" strings in
# build output prose.  This avoids counting sorry occurrences in error messages,
# documentation echoes, or user-visible strings.
_SORRY_OUTPUT_RE = re.compile(r"declaration uses 'sorry'")
# Matches Lean block comments (possibly multi-line).
_BLOCK_COMMENT_RE = re.compile(r"/-.*?-/", re.DOTALL)


def _count_sorry_in_source(text: str) -> int:
    # 1. Strip block comments (/-...-/) which may span multiple lines.
    text = _BLOCK_COMMENT_RE.sub("", text)
    count = 0
    for line in text.split("\n"):
        # 2. Strip inline line comment (everything after the first "--").
        code_part = line.split("--")[0]
        count += len(_SORRY_SOURCE_RE.findall(code_part))
        count += len(_ADMIT_SOURCE_RE.findall(code_part))
    return count


def _count_sorry_in_output(text: str) -> int:
    return len(_SORRY_OUTPUT_RE.findall(text))


def get_build_errors(target: str | None = None) -> str:
    """Run lake build and return only the error output."""
    result = lake_build(target)
    return result.errors


def verify_lean(target_file: str) -> tuple[bool, str, int]:
    """Convenience: build + sorry count, return (ok, errors, sorry_count)."""
    p = Path(target_file)
    if not p.is_absolute():
        p = PROJECT_ROOT / p
    if not p.exists():
        return False, f"Target file does not exist: {target_file}", 0

    result = lake_build()
    sorry_count = count_sorrys(target_file)
    ok = result.returncode == 0 and sorry_count == 0
    return ok, result.errors, sorry_count


# ---------------------------------------------------------------------------
# Hard Gate 1: Glue reuse >= 50%
# ---------------------------------------------------------------------------

_LEVERAGE_RE = re.compile(
    r"(?:reuse[d]?\s*(?:existing)?[^=]*=\s*(\d+).*?new[^=]*=\s*(\d+))"
    r"|(?:leverage[^:]*:\s*(\d+)\s*/\s*\(\s*\d+\s*\+\s*(\d+)\s*\))",
    re.IGNORECASE,
)

_RATIO_RE = re.compile(
    r"(?:leverage|reuse\s*ratio)\s*[:=]\s*[`]?(\d+)\s*/\s*\(\s*(\d+)\s*\+\s*(\d+)\s*\)",
    re.IGNORECASE,
)

# Matches the mandatory machine-readable block emitted by the Planner:
#   {"leverage_stats": {"reused": N, "new": M}}
_LEVERAGE_JSON_RE = re.compile(
    r'"leverage_stats"\s*:\s*\{\s*"reused"\s*:\s*(\d+)\s*,\s*"new"\s*:\s*(\d+)\s*\}',
)


def parse_leverage_from_plan(plan_text: str) -> tuple[int, int]:
    """Extract (reused, new) counts from a plan's leverage section.

    Prefers the structured JSON block ``{"leverage_stats": {"reused": N, "new": M}}``
    emitted by the Planner.  Falls back to free-text regex parsing for plans
    that pre-date the JSON requirement.  Returns (0, 0) if nothing is found.
    """
    m = _LEVERAGE_JSON_RE.search(plan_text)
    if m:
        return int(m.group(1)), int(m.group(2))

    m = _RATIO_RE.search(plan_text)
    if m:
        reused = int(m.group(1))
        new = int(m.group(3))
        return reused, new

    m = _LEVERAGE_RE.search(plan_text)
    if m:
        if m.group(1) is not None:
            return int(m.group(1)), int(m.group(2))
        return int(m.group(3)), int(m.group(4))

    return 0, 0


def check_leverage_gate(plan_text: str) -> tuple[bool, float]:
    """Return (passed, leverage_ratio).

    Blocks if leverage < LEVERAGE_THRESHOLD (default 0.5).
    """
    reused, new = parse_leverage_from_plan(plan_text)
    total = reused + new
    if total == 0:
        return False, 0.0
    leverage = reused / total
    return leverage >= LEVERAGE_THRESHOLD, leverage


# ---------------------------------------------------------------------------
# Hard Gate 3: GLUE_TRICKS validation gate
# ---------------------------------------------------------------------------

def check_glue_tricks_gate(
    before_snapshot: str,
    after_content: str,
    new_patterns: list[str],
) -> tuple[bool, list[str]]:
    """Check that every entry in *new_patterns* appears in the updated
    GLUE_TRICKS.md.

    Returns (passed, list_of_missing_patterns).
    """
    missing: list[str] = []
    for pattern in new_patterns:
        if pattern and pattern not in after_content:
            missing.append(pattern)
    return len(missing) == 0, missing


# ---------------------------------------------------------------------------
# Hard Gate 4: Used-in tag check
# ---------------------------------------------------------------------------

_LEMMA_DEF_RE = re.compile(
    r"^(?:theorem|lemma|noncomputable\s+def|def)\s+(\w+)",
    re.MULTILINE,
)


def extract_new_lemmas(filepath: str | Path) -> list[str]:
    """Return names of theorem/lemma/def declarations in *filepath*."""
    p = Path(filepath)
    if not p.is_absolute():
        p = PROJECT_ROOT / p
    if not p.exists():
        return []
    content = p.read_text(encoding="utf-8")
    return _LEMMA_DEF_RE.findall(content)


def _get_docstring_for_lemma(content: str, lemma_name: str) -> str:
    """Extract the docstring (/-  … -/) immediately preceding *lemma_name*."""
    pattern = re.compile(
        r"(/\-\-.*?\-/)\s*\n\s*(?:omit\b[^\n]*\n\s*)?(?:theorem|lemma|noncomputable\s+def|def)\s+"
        + re.escape(lemma_name),
        re.DOTALL,
    )
    m = pattern.search(content)
    return m.group(1) if m else ""


def _is_simp_lemma(content: str, lemma_name: str) -> bool:
    """Return True if the declaration is preceded by ``@[simp]`` within ~200 chars.

    ``@[simp]`` declarations are called implicitly by the simp tactic and are
    exempt from the Convention 4 ``Used in:`` requirement.
    """
    decl_pat = re.compile(
        r"^(?:theorem|lemma|noncomputable\s+def|def)\s+" + re.escape(lemma_name),
        re.MULTILINE,
    )
    m = decl_pat.search(content)
    if not m:
        return False
    snippet = content[:m.start()][-200:]
    return "@[simp" in snippet


def check_used_in_tags(modified_files: list[str | Path]) -> list[str]:
    """Return a list of ``file:lemma`` strings that are missing ``Used in:``
    tags.  Empty list means all checks passed.

    Declarations tagged with ``@[simp]`` are exempt — they are invoked
    implicitly by the simp tactic and do not require explicit callsite
    documentation (Convention 4 exception).
    """
    missing: list[str] = []
    for f in modified_files:
        p = Path(f)
        if not p.is_absolute():
            p = PROJECT_ROOT / p
        if not p.exists() or not p.suffix == ".lean":
            continue
        content = p.read_text(encoding="utf-8")
        for lemma in _LEMMA_DEF_RE.findall(content):
            if _is_simp_lemma(content, lemma):
                continue  # @[simp] declarations are exempt from Used-in requirement
            doc = _get_docstring_for_lemma(content, lemma)
            if "Used in:" not in doc:
                missing.append(f"{p.relative_to(PROJECT_ROOT)}:{lemma}")
    return missing


# ---------------------------------------------------------------------------
# Soft check: probe selection criteria
# ---------------------------------------------------------------------------

def check_probe_selection(
    has_new_technique: bool,
    predicted_leverage: float,
    proof_known: bool,
) -> list[str]:
    """Return a list of warnings (empty if all criteria met)."""
    warnings: list[str] = []
    if not has_new_technique:
        warnings.append("Probe selection: algorithm does not introduce >= 1 new technique")
    if predicted_leverage < LEVERAGE_THRESHOLD:
        warnings.append(
            f"Probe selection: predicted reuse {predicted_leverage:.0%} "
            f"< {LEVERAGE_THRESHOLD:.0%} threshold"
        )
    if not proof_known:
        warnings.append("Probe selection: no known natural-language proof reference")
    return warnings
