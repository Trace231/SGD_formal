"""Metrics tracking: scan codebase for lemma counts and persist run
statistics to ``orchestrator/metrics.json``."""

from __future__ import annotations

import json
import re
import subprocess
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path

from orchestrator.config import LIB_DIR, METRICS_PATH, PROJECT_ROOT


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
    content = path.read_text(encoding="utf-8")
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
