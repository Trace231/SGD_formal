"""File I/O utilities for reading project files, writing Lean sources, and
parsing LLM-emitted code blocks."""

from __future__ import annotations

import os
import re
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
# Parsing code blocks from LLM output
# ---------------------------------------------------------------------------

_CODE_BLOCK_RE = re.compile(
    r"```\w*\s*\n(.*?)```",
    re.DOTALL,
)

_FILE_PATH_RE = re.compile(
    r"(?:--|//-)\s*(?:File|Path|Target):\s*(.+)",
    re.IGNORECASE,
)


def parse_code_blocks(text: str) -> list[dict[str, str]]:
    """Extract fenced code blocks from *text*.

    Returns a list of dicts with keys ``code`` and optionally ``path``
    (if the block contains a ``-- File: …`` or ``-- Path: …`` comment on
    its first line).
    """
    results: list[dict[str, str]] = []
    for m in _CODE_BLOCK_RE.finditer(text):
        code = m.group(1).strip()
        path_match = _FILE_PATH_RE.search(code.split("\n", 1)[0])
        entry: dict[str, str] = {"code": code}
        if path_match:
            entry["path"] = path_match.group(1).strip()
        results.append(entry)
    return results


def extract_full_file(text: str, target_path: str) -> str | None:
    """Try to extract a complete replacement file for *target_path* from LLM
    output.  Returns ``None`` if no matching block is found."""
    blocks = parse_code_blocks(text)
    for block in blocks:
        if block.get("path") and target_path in block["path"]:
            return block["code"]
    # Fallback: if there is exactly one large code block, assume it is the file
    if len(blocks) == 1 and blocks[0]["code"].count("\n") > 10:
        return blocks[0]["code"]
    return None


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
