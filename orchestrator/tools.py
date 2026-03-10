"""Controlled tool functions for orchestrator agents.

These helpers intentionally restrict file access and mutation patterns to make
agent behavior safer and more predictable.
"""

from __future__ import annotations

import os
import re
import tempfile
from pathlib import Path
from typing import Any

from orchestrator.config import LEAN_VERIFY_PATHS, PROJECT_ROOT, WHITELIST_PATHS
from orchestrator.verify import count_sorrys, lake_build

_READ_WRITE_ALLOWLIST = tuple(p.rstrip("/") for p in WHITELIST_PATHS)
_LEAN_VERIFY_ALLOWLIST = tuple(p.rstrip("/") for p in LEAN_VERIFY_PATHS)
_DOC_ALLOWLIST = tuple(p for p in _READ_WRITE_ALLOWLIST if p == "docs")


def _is_under(path: Path, root: Path) -> bool:
    """Return True when *path* is inside *root* (or equals *root*)."""
    try:
        path.relative_to(root)
        return True
    except ValueError:
        return False


def _resolve_allowed_path(path: str | Path, allowed_roots: tuple[str, ...]) -> Path:
    """Resolve a user path under PROJECT_ROOT and enforce directory allowlist."""
    candidate = Path(path)
    if not candidate.is_absolute():
        candidate = (PROJECT_ROOT / candidate).resolve()
    else:
        candidate = candidate.resolve()

    project_root = PROJECT_ROOT.resolve()
    if not _is_under(candidate, project_root):
        raise PermissionError(f"Path escapes project root: {path}")

    allowed_abs = [(project_root / root).resolve() for root in allowed_roots]
    if not any(_is_under(candidate, root) for root in allowed_abs):
        roots = ", ".join(allowed_roots)
        raise PermissionError(
            f"Path not in allowlist ({roots}): {path}"
        )
    return candidate


def _atomic_write(path: Path, content: str) -> None:
    """Write text content atomically to *path*."""
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(dir=path.parent, suffix=".tools.tmp")
    try:
        os.write(fd, content.encode("utf-8"))
        os.close(fd)
        os.replace(tmp, path)
    except BaseException:
        try:
            os.close(fd)
        except OSError:
            pass
        if os.path.exists(tmp):
            os.unlink(tmp)
        raise


def read_file(
    path: str | Path,
    start_line: int | None = None,
    end_line: int | None = None,
    with_line_numbers: bool = True,
) -> str:
    """Read a file under Algorithms/, Lib/, or docs/.

    Args:
        path: File path (relative to project root or absolute).
        start_line: First line to return, 1-indexed (default: 1).
        end_line: Last line to return, inclusive, 1-indexed (default: last line).
        with_line_numbers: Prefix each line with its line number (default: True).

    Returns:
        File content as a string, optionally annotated with line numbers.
        Returns an error string (not an exception) for out-of-bounds requests.
    """
    resolved = _resolve_allowed_path(path, _READ_WRITE_ALLOWLIST)
    lines = resolved.read_text(encoding="utf-8").splitlines(keepends=True)
    total = len(lines)

    # Resolve defaults
    s = max(0, (start_line or 1) - 1)   # convert to 0-indexed, clamp negatives
    e = min(total, end_line or total)    # clamp end beyond EOF

    # Validate after clamping
    if start_line is not None and start_line > total:
        return (
            f"Error: start_line ({start_line}) exceeds total lines ({total}) "
            f"in {path}"
        )
    if start_line is not None and end_line is not None and start_line > end_line:
        return (
            f"Error: start_line ({start_line}) is greater than end_line ({end_line})"
        )

    slice_ = lines[s:e]
    first_num = s + 1  # 1-indexed line number of first returned line

    if not with_line_numbers:
        content = "".join(slice_)
    else:
        content = "".join(f"{first_num + i:6}|{line}" for i, line in enumerate(slice_))

    # Prepend a header when a sub-range was requested
    if start_line is not None or end_line is not None:
        header = (
            f"# Lines {first_num}–{first_num + len(slice_) - 1} "
            f"of {total} ({path})\n"
        )
        return header + content

    return content


def search_in_file(
    path: str | Path,
    pattern: str,
    context_lines: int = 3,
    max_matches: int = 20,
) -> dict[str, Any]:
    """Search a file for a regex pattern, returning matching lines with context.

    Args:
        path: File path under Algorithms/, Lib/, or docs/.
        pattern: Python regex pattern to search for.
        context_lines: Number of lines of context to show before and after each match.
        max_matches: Maximum number of matches to return (default 20).
                     Use a more specific pattern if too many results are found.

    Returns:
        dict with keys:
          path, pattern, total_matches, shown_matches, truncated,
          truncation_note (only when truncated), formatted (human-readable string),
          matches (list of {line, content, context}).
    """
    resolved = _resolve_allowed_path(path, _READ_WRITE_ALLOWLIST)
    lines = resolved.read_text(encoding="utf-8").splitlines()

    all_match_indices: list[int] = [
        i for i, line in enumerate(lines) if re.search(pattern, line)
    ]
    total = len(all_match_indices)
    truncated = total > max_matches
    shown_indices = all_match_indices[:max_matches]

    matches: list[dict[str, Any]] = []
    formatted_parts: list[str] = []

    for idx in shown_indices:
        ctx_start = max(0, idx - context_lines)
        ctx_end = min(len(lines), idx + context_lines + 1)
        context = [
            {"line": j + 1, "content": lines[j]}
            for j in range(ctx_start, ctx_end)
        ]
        matches.append({"line": idx + 1, "content": lines[idx], "context": context})

        # Build formatted block for this match
        block: list[str] = []
        for j in range(ctx_start, ctx_end):
            marker = ">>>" if j == idx else "   "
            block.append(f"{j + 1:6}|{marker} {lines[j]}")
        formatted_parts.append("\n".join(block))

    result: dict[str, Any] = {
        "path": str(resolved.relative_to(PROJECT_ROOT)),
        "pattern": pattern,
        "total_matches": total,
        "shown_matches": len(shown_indices),
        "truncated": truncated,
        "formatted": "\n---\n".join(formatted_parts) if formatted_parts else "(no matches)",
        "matches": matches,
    }
    if truncated:
        result["truncation_note"] = (
            f"Found {total} matches, showing first {max_matches}. "
            "Please use a more specific pattern."
        )
    return result


def edit_file_patch(path: str | Path, old_str: str, new_str: str) -> dict[str, Any]:
    """Apply an exact single-string replacement instead of full overwrite.

    The replacement is intentionally strict:
    - old_str must exist
    - old_str must appear exactly once (to avoid ambiguous patches)
    """
    if old_str == "":
        raise ValueError("old_str must be non-empty for precise patching")

    resolved = _resolve_allowed_path(path, _READ_WRITE_ALLOWLIST)
    if not resolved.exists():
        raise FileNotFoundError(f"Target file does not exist: {path}")

    original = resolved.read_text(encoding="utf-8")
    occurrences = original.count(old_str)
    if occurrences == 0:
        raise ValueError("old_str not found in target file")
    if occurrences > 1:
        raise ValueError(
            f"old_str appears {occurrences} times; patch would be ambiguous"
        )

    updated = original.replace(old_str, new_str, 1)
    _atomic_write(resolved, updated)

    return {
        "path": str(resolved.relative_to(PROJECT_ROOT)),
        "replacements": 1,
        "changed": original != updated,
        # For full-audit, callers can log before/after/patch based on these.
        "before": original,
        "after": updated,
    }


def write_new_file(path: str | Path, content: str) -> dict[str, Any]:
    """Create a brand-new file under Algorithms/ or Lib/.

    Raises FileExistsError if the file already exists — use edit_file_patch
    to modify an existing file.
    """
    resolved = _resolve_allowed_path(path, _READ_WRITE_ALLOWLIST)
    if resolved.exists():
        raise FileExistsError(
            f"File already exists: {path}. Use edit_file_patch to modify it."
        )
    _atomic_write(resolved, content)
    return {
        "path": str(resolved.relative_to(PROJECT_ROOT)),
        "created": True,
        "size_bytes": len(content.encode("utf-8")),
        "after": content,
    }


def overwrite_file(path: str | Path, content: str) -> dict[str, Any]:
    """Overwrite an existing file with content. Used for restore/rollback."""
    resolved = _resolve_allowed_path(path, _READ_WRITE_ALLOWLIST)
    if not resolved.exists():
        raise FileNotFoundError(f"Target file does not exist: {path}")
    original = resolved.read_text(encoding="utf-8")
    _atomic_write(resolved, content)
    return {
        "path": str(resolved.relative_to(PROJECT_ROOT)),
        "overwritten": True,
        "before": original,
        "after": content,
    }


def _path_to_lean_module(rel_path: str) -> str:
    """Convert a relative .lean path to a dotted Lean module name.

    Example: 'Algorithms/SVRGOuterLoop.lean' → 'Algorithms.SVRGOuterLoop'
    """
    return rel_path.removesuffix(".lean").replace("/", ".")


def _extract_lean_error_lines(raw: str) -> list[str]:
    """Extract Lean compiler error lines from lake build output.

    Handles both Lake error formats:
      Single-line: file.lean:L:C: error: message
      Two-line:    file.lean:L:C: (alone)
                   error: message         (next line)

    Two-line entries are merged into a single line so that all downstream
    regex consumers (lean_error_lines filter, _extract_first_error_line,
    _classify_lean_error) work without modification.
    """
    result: list[str] = []
    lines = raw.splitlines()
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        # Format 1: file.lean:L:C: error: message (everything on one line)
        if re.search(r"\.lean:\d+:\d+:\s*error:", line):
            result.append(line)
        # Format 2: file.lean:L:C: alone, followed by error: ... on the next line
        elif re.search(r"\.lean:\d+:\d+:\s*$", line) and i + 1 < len(lines):
            next_line = lines[i + 1].strip()
            if next_line.startswith("error:"):
                # Merge into a single line preserving the file:line:col: prefix
                result.append(line.rstrip(": ") + ": " + next_line)
                i += 1  # next line already consumed
        i += 1
    return result


def run_lean_verify(file_path: str | Path) -> dict[str, Any]:
    """Run Lean verification and return a JSON-serializable result."""
    resolved = _resolve_allowed_path(file_path, _LEAN_VERIFY_ALLOWLIST)

    # Guard: do not run lake build if the target file does not yet exist.
    if not resolved.exists():
        return {
            "target": str(file_path),
            "success": False,
            "exit_code": 1,
            "sorry_count": 0,
            "error_count": 1,
            "errors": [
                f"Target file does not exist: {file_path}. "
                "Call write_new_file(path, content) first to create it."
            ],
        }

    rel = str(resolved.relative_to(PROJECT_ROOT))

    build = lake_build(target=_path_to_lean_module(rel))
    sorry_count = count_sorrys(rel)

    all_lines = [line.strip() for line in build.errors.splitlines() if line.strip()]
    # Prefer lines that carry a specific file:line:col: error: location — these
    # are real Lean compiler errors.  Info/warning lines and the generic Lake
    # summary "error: build failed" are filtered into separate buckets so the
    # line-number extractor in main.py always sees the actionable errors first.
    # _extract_lean_error_lines handles both single-line and two-line Lake formats.
    lean_error_lines = _extract_lean_error_lines(build.errors)
    warning_lines = [
        l for l in all_lines if re.search(r"\.lean:\d+:\d+:\s*warning:", l)
    ]
    # Fall back to the full output when no specific error lines were found
    # (e.g. a top-level "error: build failed" with no per-file location).
    error_lines = lean_error_lines if lean_error_lines else all_lines

    return {
        "target": rel,
        "success": build.returncode == 0 and sorry_count == 0,
        "exit_code": build.returncode,
        "sorry_count": sorry_count,
        "error_count": len(error_lines),
        "errors": error_lines,
        "warnings": warning_lines,
    }


def run_repo_verify() -> dict[str, Any]:
    """Run full-project Lean verification and measure total repo sorry count."""
    build = lake_build()
    total_sorry = 0
    lean_files = list(PROJECT_ROOT.rglob("*.lean"))
    for lean_file in lean_files:
        rel = lean_file.relative_to(PROJECT_ROOT)
        total_sorry += count_sorrys(rel)

    error_lines = [
        line.strip()
        for line in build.errors.splitlines()
        if line.strip()
    ]
    return {
        "success": build.returncode == 0 and total_sorry == 0,
        "exit_code": build.returncode,
        "total_sorry_count": total_sorry,
        "lean_file_count": len(lean_files),
        "error_count": len(error_lines),
        "errors": error_lines,
    }


def apply_doc_patch(path: str | Path, anchor: str, new_content: str) -> dict[str, Any]:
    """Insert *new_content* near a regex *anchor* in a docs file.

    Rules:
    - Only docs/ paths are allowed.
    - Anchor must exist (no fallback append).
    - If content already exists, no-op.
    """
    if not anchor.strip():
        raise ValueError("anchor must be non-empty")
    if not new_content.strip():
        raise ValueError("new_content must be non-empty")

    resolved = _resolve_allowed_path(path, _DOC_ALLOWLIST)
    if not resolved.exists():
        raise FileNotFoundError(f"Target doc file does not exist: {path}")

    original = resolved.read_text(encoding="utf-8")
    if new_content in original:
        return {
            "path": str(resolved.relative_to(PROJECT_ROOT)),
            "changed": False,
            "reason": "content already present",
        }

    matches = list(re.finditer(anchor, original, flags=re.MULTILINE))
    if not matches:
        raise ValueError(
            f"Anchor not found in {resolved.relative_to(PROJECT_ROOT)}: {anchor}"
        )
    if len(matches) > 1:
        positions = [m.start() for m in matches]
        raise ValueError(
            f"Anchor matches {len(matches)} locations in "
            f"{resolved.relative_to(PROJECT_ROOT)} "
            f"(positions {positions}); anchor must be unique. "
            "Refine the regex to target a single match."
        )

    insert_at = matches[0].end()
    patch_body = "\n\n" + new_content.strip() + "\n"
    updated = original[:insert_at] + patch_body + original[insert_at:]
    _atomic_write(resolved, updated)

    return {
        "path": str(resolved.relative_to(PROJECT_ROOT)),
        "changed": True,
        "anchor": anchor,
        "before": original,
        "after": updated,
    }
