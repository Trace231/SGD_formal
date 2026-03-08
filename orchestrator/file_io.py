"""File I/O utilities for reading and atomically writing project files."""

from __future__ import annotations

from pathlib import Path

from orchestrator.config import PROJECT_ROOT


# ---------------------------------------------------------------------------
# Loading files into context strings
# ---------------------------------------------------------------------------

def load_file(path: str | Path) -> str:
    """Read a single file and return its contents."""
    p = Path(path)
    if not p.is_absolute():
        p = PROJECT_ROOT / p
    return p.read_text(encoding="utf-8")


def load_files(paths: list[str | Path]) -> str:
    """Read multiple files and return them as a single context block.

    Each file is wrapped in ``<file path="…">…</file>`` tags so the LLM
    can distinguish sources.
    """
    parts: list[str] = []
    for p in paths:
        try:
            content = load_file(p)
            parts.append(f'<file path="{p}">\n{content}\n</file>')
        except FileNotFoundError:
            parts.append(f'<file path="{p}">\n[FILE NOT FOUND]\n</file>')
    return "\n\n".join(parts)


# ---------------------------------------------------------------------------
# Snapshot helpers (for diff-based gates)
# ---------------------------------------------------------------------------

def snapshot_file(path: str | Path) -> str:
    """Return the contents of *path*, or empty string if it doesn't exist."""
    try:
        return load_file(path)
    except FileNotFoundError:
        return ""
