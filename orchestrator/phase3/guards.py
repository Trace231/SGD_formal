"""Guard helpers for Phase3 proof orchestration."""

from __future__ import annotations

import re

from orchestrator.config import PROJECT_ROOT


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

