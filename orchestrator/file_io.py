"""File I/O utilities for reading and atomically writing project files."""

from __future__ import annotations

import os
import tempfile
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
# Writing Lean files (atomic)
# ---------------------------------------------------------------------------

def write_lean_file(path: str | Path, content: str) -> Path:
    """Write *content* to *path* atomically (write-to-temp then rename).

    Returns the resolved ``Path`` that was written.
    """
    p = Path(path)
    if not p.is_absolute():
        p = PROJECT_ROOT / p
    p.parent.mkdir(parents=True, exist_ok=True)

    fd, tmp = tempfile.mkstemp(dir=p.parent, suffix=".lean.tmp")
    try:
        os.write(fd, content.encode("utf-8"))
        os.close(fd)
        os.replace(tmp, p)
    except BaseException:
        os.close(fd) if not os.get_inheritable(fd) else None  # noqa: B018
        if os.path.exists(tmp):
            os.unlink(tmp)
        raise
    return p


# ---------------------------------------------------------------------------
# Writing text / markdown files (atomic)
# ---------------------------------------------------------------------------

def write_text_file(path: str | Path, content: str, *, append: bool = False) -> Path:
    """Write *content* to *path* atomically (write-to-temp then rename).

    When *append* is ``True`` the existing file content is prepended to
    *content* before writing, so the result is the original file followed by
    the new content.

    Returns the resolved ``Path`` that was written.
    """
    p = Path(path)
    if not p.is_absolute():
        p = PROJECT_ROOT / p
    p.parent.mkdir(parents=True, exist_ok=True)

    if append and p.exists():
        existing = p.read_text(encoding="utf-8")
        content = existing + "\n" + content

    fd, tmp = tempfile.mkstemp(dir=p.parent, suffix=".txt.tmp")
    try:
        os.write(fd, content.encode("utf-8"))
        os.close(fd)
        os.replace(tmp, p)
    except BaseException:
        try:
            os.close(fd)
        except OSError:
            pass
        if os.path.exists(tmp):
            os.unlink(tmp)
        raise
    return p


# ---------------------------------------------------------------------------
# Snapshot helpers (for diff-based gates)
# ---------------------------------------------------------------------------

def snapshot_file(path: str | Path) -> str:
    """Return the contents of *path*, or empty string if it doesn't exist."""
    try:
        return load_file(path)
    except FileNotFoundError:
        return ""
