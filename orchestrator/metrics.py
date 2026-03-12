"""Metrics tracking with physical measurements and audit signals.

This module is also a natural place to document high-level audit modes and
where audit artifacts (JSON + snapshots) are written.
"""

from __future__ import annotations

import json
import re
import subprocess
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from orchestrator.config import LIB_DIR, METRICS_PATH, PROJECT_ROOT
from orchestrator.file_io import load_file
from orchestrator.tools import run_repo_verify


# ---------------------------------------------------------------------------
# Run record
# ---------------------------------------------------------------------------

@dataclass
class RunRecord:
    algorithm: str
    timestamp: str = ""
    glue_hit_rate: float = 0.0
    total_glue_lemmas: int = 0
    total_layer1_lemmas: int = 0
    new_layer1_lemmas: int = 0
    layer1_fields_added: int = 0
    new_glue_lemmas: int = 0
    new_tricks_added: int = 0
    sorry_close_attempts: int = 0
    final_sorry_count: int = 0
    physical_exit_code: int = 1
    total_repo_sorry_count: int = 0
    new_lib_declarations: int = 0
    algorithm_calls_to_new_lib_declarations: int = 0
    physical_leverage_rate: float = 0.0
    # Dual leverage metrics
    # L_coverage: fraction of new Lib decls actually used in Algorithms/
    lib_coverage_rate: float = 0.0
    # L_density: avg calls per used new Lib decl (reuse intensity)
    lib_density_rate: float = 0.0
    phase3_retry_count: int = 0
    estimated_token_consumption: int = 0
    doc_code_alignment_ok: bool = True
    doc_code_alignment_missing: list[str] | None = None

    def __post_init__(self) -> None:
        if not self.timestamp:
            self.timestamp = datetime.now(timezone.utc).isoformat(timespec="seconds")


# ---------------------------------------------------------------------------
# Codebase scanning helpers
# ---------------------------------------------------------------------------

_DECL_RE = re.compile(
    r"^(?:theorem|lemma|noncomputable\s+def|def)\s+\w+",
    re.MULTILINE,
)
_DECL_NAME_RE = re.compile(
    r"^(?:theorem|lemma|noncomputable\s+def|def)\s+([A-Za-z_]\w*)",
    re.MULTILINE,
)
_DIFF_ADDED_DECL_RE = re.compile(
    r"^\+(?:theorem|lemma|noncomputable\s+def|def)\s+([A-Za-z_]\w*)",
    re.MULTILINE,
)
_CATALOG_LEMMA_HEADING_RE = re.compile(r"^####\s+`([^`]+)`", re.MULTILINE)


def _count_declarations(directory: Path) -> int:
    """Count theorem/lemma/def declarations in all .lean files under *directory*."""
    count = 0
    if not directory.exists():
        return 0
    for f in directory.rglob("*.lean"):
        content = f.read_text(encoding="utf-8")
        count += len(_DECL_RE.findall(content))
    return count


def count_glue_lemmas() -> int:
    return _count_declarations(LIB_DIR / "Glue")


def count_layer1_lemmas() -> int:
    return _count_declarations(LIB_DIR / "Layer1")


def count_glue_tricks_sections() -> int:
    """Count ``### Pattern`` or ``#### Pattern`` headings in GLUE_TRICKS.md."""
    path = PROJECT_ROOT / "docs" / "GLUE_TRICKS.md"
    if not path.exists():
        return 0
    content = load_file(path)
    return len(re.findall(r"^#{3,4}\s+Pattern", content, re.MULTILINE))


def diff_line_count(filepath: str | Path) -> int:
    """Return number of added lines in *filepath* since HEAD (unstaged)."""
    try:
        result = subprocess.run(
            ["git", "diff", "--numstat", "--", str(filepath)],
            cwd=PROJECT_ROOT,
            capture_output=True,
            text=True,
            timeout=10,
        )
        if result.returncode != 0 or not result.stdout.strip():
            return 0
        parts = result.stdout.strip().split("\t")
        return int(parts[0]) if parts[0] != "-" else 0
    except (subprocess.TimeoutExpired, ValueError):
        return 0


def _new_lib_declarations_from_diff() -> list[str]:
    """Extract added declaration names in Lib/ from git diff."""
    try:
        result = subprocess.run(
            ["git", "diff", "--unified=0", "--", "Lib"],
            cwd=PROJECT_ROOT,
            capture_output=True,
            text=True,
            timeout=20,
        )
    except subprocess.TimeoutExpired:
        return []
    if result.returncode != 0:
        return []
    names = _DIFF_ADDED_DECL_RE.findall(result.stdout)
    return sorted(set(names))


def _count_algorithm_calls(symbols: list[str]) -> int:
    """Count textual usages of *symbols* in Algorithms/*.lean."""
    if not symbols:
        return 0
    total = 0
    algo_root = PROJECT_ROOT / "Algorithms"
    if not algo_root.exists():
        return 0
    for lean_file in algo_root.rglob("*.lean"):
        content = lean_file.read_text(encoding="utf-8")
        for sym in symbols:
            total += len(re.findall(rf"\b{re.escape(sym)}\b", content))
    return total


def _used_symbol_set(symbols: list[str]) -> set[str]:
    """Return subset of *symbols* that appear at least once in Algorithms/*.lean.

    Used to compute L_coverage = |Used| / |Total|.
    """
    if not symbols:
        return set()
    used: set[str] = set()
    algo_root = PROJECT_ROOT / "Algorithms"
    if not algo_root.exists():
        return used
    file_contents = [
        f.read_text(encoding="utf-8")
        for f in algo_root.rglob("*.lean")
    ]
    for sym in symbols:
        pattern = re.compile(rf"\b{re.escape(sym)}\b")
        if any(pattern.search(c) for c in file_contents):
            used.add(sym)
    return used


def _collect_lib_and_algo_decl_names() -> set[str]:
    """Collect declaration names from Lib/ and Algorithms/ for alignment audit."""
    names: set[str] = set()
    for root in (PROJECT_ROOT / "Lib", PROJECT_ROOT / "Algorithms"):
        if not root.exists():
            continue
        for lean_file in root.rglob("*.lean"):
            content = lean_file.read_text(encoding="utf-8")
            names.update(_DECL_NAME_RE.findall(content))
    return names


def _audit_doc_code_alignment() -> tuple[bool, list[str]]:
    """Check that lemma headings in CATALOG correspond to real declarations."""
    catalog = PROJECT_ROOT / "docs" / "CATALOG.md"
    if not catalog.exists():
        return False, ["docs/CATALOG.md missing"]
    content = catalog.read_text(encoding="utf-8")
    doc_names = set(_CATALOG_LEMMA_HEADING_RE.findall(content))
    code_names = _collect_lib_and_algo_decl_names()
    missing = sorted(name for name in doc_names if name not in code_names)
    return len(missing) == 0, missing


def capture_physical_metrics(
    algorithm: str,
    *,
    new_tricks_added: int,
    phase3_execution_history: list[dict[str, Any]] | None = None,
    phase3_attempts: int = 0,
    estimated_token_consumption: int = 0,
) -> RunRecord:
    """Capture repository-grounded metrics instead of agent-estimated values."""
    repo_verify = run_repo_verify()
    new_lib_symbols = _new_lib_declarations_from_diff()
    algo_calls = _count_algorithm_calls(new_lib_symbols)
    used_symbols = _used_symbol_set(new_lib_symbols)

    total_new = len(new_lib_symbols)
    used_new = len(used_symbols)

    # L_coverage: fraction of new Lib decls used at least once in Algorithms/
    lib_coverage = (used_new / total_new) if total_new > 0 else 1.0
    # L_density: average call frequency per used Lib decl
    lib_density = (algo_calls / used_new) if used_new > 0 else 0.0
    # Composite physical leverage rate (legacy formula kept for backward compat)
    denom = algo_calls + total_new
    leverage = (algo_calls / denom) if denom > 0 else 1.0

    retries = 0
    if phase3_execution_history:
        retries = sum(
            1
            for entry in phase3_execution_history
            if entry.get("status_code") in {"ERROR", "BLOCKED"}
        )

    alignment_ok, alignment_missing = _audit_doc_code_alignment()

    return RunRecord(
        algorithm=algorithm,
        glue_hit_rate=leverage,
        total_glue_lemmas=count_glue_lemmas(),
        total_layer1_lemmas=count_layer1_lemmas(),
        new_tricks_added=new_tricks_added,
        sorry_close_attempts=phase3_attempts,
        final_sorry_count=int(repo_verify.get("total_sorry_count", 0)),
        physical_exit_code=int(repo_verify.get("exit_code", 1)),
        total_repo_sorry_count=int(repo_verify.get("total_sorry_count", 0)),
        new_lib_declarations=total_new,
        algorithm_calls_to_new_lib_declarations=algo_calls,
        physical_leverage_rate=leverage,
        lib_coverage_rate=lib_coverage,
        lib_density_rate=lib_density,
        phase3_retry_count=retries,
        estimated_token_consumption=estimated_token_consumption,
        doc_code_alignment_ok=alignment_ok,
        doc_code_alignment_missing=alignment_missing,
    )


# ---------------------------------------------------------------------------
# MetricsStore — persistence
# ---------------------------------------------------------------------------

class MetricsStore:
    """Append-only JSON store at ``orchestrator/metrics.json``."""

    def __init__(self, path: Path = METRICS_PATH):
        self.path = path
        self._data: dict = self._load()

    def _load(self) -> dict:
        if self.path.exists():
            return json.loads(self.path.read_text(encoding="utf-8"))
        return {"runs": []}

    def _save(self) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.path.write_text(
            json.dumps(self._data, indent=2, ensure_ascii=False) + "\n",
            encoding="utf-8",
        )

    @property
    def runs(self) -> list[dict]:
        return self._data.setdefault("runs", [])

    def append(self, record: RunRecord) -> None:
        """Append a run record and flush to disk."""
        self.runs.append(asdict(record))
        self._save()

    def build_record(
        self,
        algorithm: str,
        *,
        glue_hit_rate: float = 0.0,
        new_glue_lemmas: int = 0,
        new_layer1_lemmas: int = 0,
        layer1_fields_added: int = 0,
        new_tricks_added: int = 0,
        sorry_close_attempts: int = 0,
        final_sorry_count: int = 0,
    ) -> RunRecord:
        """Create a ``RunRecord`` with live codebase counts filled in."""
        return RunRecord(
            algorithm=algorithm,
            glue_hit_rate=glue_hit_rate,
            total_glue_lemmas=count_glue_lemmas(),
            total_layer1_lemmas=count_layer1_lemmas(),
            new_layer1_lemmas=new_layer1_lemmas,
            layer1_fields_added=layer1_fields_added,
            new_glue_lemmas=new_glue_lemmas,
            new_tricks_added=new_tricks_added,
            sorry_close_attempts=sorry_close_attempts,
            final_sorry_count=final_sorry_count,
        )
