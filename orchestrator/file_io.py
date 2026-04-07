"""File I/O utilities for reading and atomically writing project files."""

from __future__ import annotations

import re
from pathlib import Path

from orchestrator.config import PROJECT_ROOT, RUNTIME_ARTIFACT_EXCLUDE_GLOBS

_LEAN_DECL_RE = re.compile(
    r"^(?:theorem|lemma|noncomputable\s+def|def|structure|class|abbrev)\s+\w+",
)


def _is_excluded_runtime_path(path: str | Path) -> bool:
    import fnmatch

    p = Path(path)
    rel = str(p)
    if p.is_absolute():
        try:
            rel = str(p.relative_to(PROJECT_ROOT))
        except ValueError:
            rel = str(p)
    rel = rel.lstrip("./")
    return any(fnmatch.fnmatch(rel, glob) for glob in RUNTIME_ARTIFACT_EXCLUDE_GLOBS)


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
        if _is_excluded_runtime_path(p):
            continue
        try:
            content = load_file(p)
            parts.append(f'<file path="{p}">\n{content}\n</file>')
        except FileNotFoundError:
            parts.append(f'<file path="{p}">\n[FILE NOT FOUND]\n</file>')
    return "\n\n".join(parts)


# ---------------------------------------------------------------------------
# Snapshot helpers (for diff-based gates)
# ---------------------------------------------------------------------------

def generate_project_manifest(paths: list[str | Path]) -> str:
    """Generate a compact declaration index from Lean and Markdown files.

    For .lean files: extracts theorem/lemma/def/structure/class/abbrev lines
    with their 1-indexed line numbers, truncated to 80 characters.
    For .md files: extracts lines starting with '#' (section headings).
    Each file is wrapped in ``<manifest path="…">…</manifest>`` tags.

    Use this to give agents a cheap overview of available symbols so they can
    issue targeted ``read_file`` calls instead of loading full file content.
    """
    parts: list[str] = []
    seen_blocks: set[str] = set()
    for p in paths:
        p_str = str(p)
        if _is_excluded_runtime_path(p_str):
            continue
        try:
            content = load_file(p)
            lines = content.splitlines()
            if p_str.endswith(".lean"):
                decl_lines: list[str] = []
                for i, line in enumerate(lines, 1):
                    if _LEAN_DECL_RE.match(line):
                        decl_lines.append(f"  line {i:4}: {line.rstrip()[:80]}")
                body = "\n".join(decl_lines) if decl_lines else "  (no top-level declarations)"
            else:
                headings = [line.rstrip() for line in lines if line.startswith("#")]
                headings = list(dict.fromkeys(headings))
                body = "\n".join(headings) if headings else "  (no headings)"
            block = f'<manifest path="{p}">\n{body}\n</manifest>'
            if block in seen_blocks:
                continue
            seen_blocks.add(block)
            parts.append(block)
        except FileNotFoundError:
            block = f'<manifest path="{p}">\n[FILE NOT FOUND]\n</manifest>'
            if block in seen_blocks:
                continue
            seen_blocks.add(block)
            parts.append(block)
    return "\n\n".join(parts)


def snapshot_file(path: str | Path) -> str:
    """Return the contents of *path*, or empty string if it doesn't exist."""
    try:
        return load_file(path)
    except FileNotFoundError:
        return ""
