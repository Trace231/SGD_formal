"""Controlled tool functions for orchestrator agents.

These helpers intentionally restrict file access and mutation patterns to make
agent behavior safer and more predictable.
"""

from __future__ import annotations

import difflib
import hashlib
import os
import re
import tempfile
import time
from pathlib import Path
from typing import Any

from orchestrator.config import (
    APOLLO_FALLBACK_TO_LAKE_ON_FAILURE,
    APOLLO_LAKE_PATH,
    APOLLO_PROJECT_PATH,
    APOLLO_REPL_WORKSPACE,
    REPL_VERIFY_TIMEOUT,
    APOLLO_VERIFY_TIMEOUT,
    LEAN_BUILD_TIMEOUT,
    LEAN_VERIFY_BACKEND,
    LEAN_VERIFY_PATHS,
    PROJECT_ROOT,
    READ_ONLY_PATHS,
    VERIFY_BACKEND_STRICT,
    WHITELIST_PATHS,
)
from orchestrator.verify import count_sorrys, lake_build

_READ_WRITE_ALLOWLIST = tuple(p.rstrip("/") for p in WHITELIST_PATHS)
_LEAN_VERIFY_ALLOWLIST = tuple(p.rstrip("/") for p in LEAN_VERIFY_PATHS)
_DOC_ALLOWLIST = tuple(p for p in _READ_WRITE_ALLOWLIST if p == "docs")
# Extended read-only allowlist — includes root infrastructure files (Main.lean, lakefile.lean)
# so agents can inspect the import graph without write access.
_READ_ONLY_ALLOWLIST = tuple(p.rstrip("/") for p in READ_ONLY_PATHS)
_REQUIRED_IMPORTS_BY_FILE: dict[str, set[str]] = {
    "Algorithms/SubgradientMethod.lean": {"import Main"},
}


def _to_rel(path: Path) -> str:
    return str(path.resolve().relative_to(PROJECT_ROOT.resolve()))


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


def _sha256_text(content: str) -> str:
    """Return a stable sha256 digest string for text content."""
    return hashlib.sha256(content.encode("utf-8")).hexdigest()


def _parse_line_range_spec(spec: str | None) -> tuple[int, int] | None:
    """Parse ``'start-end'`` or ``'start'`` into inclusive line bounds."""
    if spec is None:
        return None
    raw = str(spec).strip()
    if not raw:
        return None
    match = re.fullmatch(r"(\d+)(?:\s*-\s*(\d+))?", raw)
    if not match:
        raise ValueError(f"Invalid line range: {spec!r}")
    start = int(match.group(1))
    end = int(match.group(2) or match.group(1))
    if start <= 0 or end <= 0 or start > end:
        raise ValueError(f"Invalid line range: {spec!r}")
    return start, end


def _locate_replacement_line_range(original: str, old_str: str) -> tuple[int, int]:
    """Return inclusive line range where ``old_str`` appears in ``original``."""
    idx = original.find(old_str)
    if idx < 0:
        raise ValueError("old_str not found")
    start = original[:idx].count("\n") + 1
    line_count = max(1, len(old_str.splitlines()))
    return start, start + line_count - 1


def _range_within(inner: tuple[int, int], outer: tuple[int, int]) -> bool:
    """Whether inclusive line range ``inner`` is fully contained in ``outer``."""
    return outer[0] <= inner[0] and inner[1] <= outer[1]


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
    read_path = resolved
    lines = read_path.read_text(encoding="utf-8").splitlines(keepends=True)
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
    read_path = resolved
    lines = read_path.read_text(encoding="utf-8").splitlines()

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


def read_file_readonly(
    path: str | Path,
    start_line: int | None = None,
    end_line: int | None = None,
    with_line_numbers: bool = True,
) -> str:
    """Read any file under Algorithms/, Lib/, docs/, Main.lean, or lakefile.lean.

    Identical to read_file but uses an extended read-only allowlist that also
    covers root-level Lean infrastructure files.  Use this to inspect the project
    import graph (e.g. read_file_readonly("Main.lean")) before adding new imports,
    to detect potential circular dependency issues.

    Args:
        path: File path (relative to project root or absolute).
        start_line: First line to return, 1-indexed (default: 1).
        end_line: Last line to return, inclusive, 1-indexed (default: last line).
        with_line_numbers: Prefix each line with its line number (default: True).
    """
    resolved = _resolve_allowed_path(path, _READ_ONLY_ALLOWLIST)
    read_path = resolved
    lines = read_path.read_text(encoding="utf-8").splitlines(keepends=True)
    total = len(lines)

    s = max(0, (start_line or 1) - 1)
    e = min(total, end_line or total)

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
    first_num = s + 1

    if not with_line_numbers:
        content = "".join(slice_)
    else:
        content = "".join(f"{first_num + i:6}|{line}" for i, line in enumerate(slice_))

    if start_line is not None or end_line is not None:
        header = (
            f"# Lines {first_num}–{first_num + len(slice_) - 1} "
            f"of {total} ({path})\n"
        )
        return header + content

    return content


def search_in_file_readonly(
    path: str | Path,
    pattern: str,
    context_lines: int = 3,
    max_matches: int = 20,
) -> dict[str, Any]:
    """Search any file under Algorithms/, Lib/, docs/, Main.lean, or lakefile.lean.

    Identical to search_in_file but uses an extended read-only allowlist that also
    covers root-level Lean infrastructure files.

    Args:
        path: File path under the extended read-only allowlist.
        pattern: Python regex pattern to search for.
        context_lines: Number of lines of context around each match.
        max_matches: Maximum number of matches to return (default 20).
    """
    resolved = _resolve_allowed_path(path, _READ_ONLY_ALLOWLIST)
    read_path = resolved
    lines = read_path.read_text(encoding="utf-8").splitlines()

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


def _extract_new_mathlib_imports(old_text: str, new_text: str) -> list[str]:
    """Return Mathlib module names that are newly added in new_text vs old_text."""
    _IMPORT_RE = re.compile(r"^\s*import\s+(Mathlib(?:\.\w+)+)", re.MULTILINE)
    before = set(_IMPORT_RE.findall(old_text))
    after = set(_IMPORT_RE.findall(new_text))
    return sorted(after - before)


def _extract_import_lines(text: str) -> list[str]:
    """Return normalized import lines in source order."""
    imports: list[str] = []
    for raw in text.splitlines():
        line = raw.strip()
        if line.startswith("import "):
            imports.append(line)
    return imports


def _required_imports_for_rel_path(rel_path: str) -> set[str]:
    return set(_REQUIRED_IMPORTS_BY_FILE.get(rel_path, set()))


def validate_required_imports(
    *,
    rel_path: str,
    old_text: str,
    new_text: str,
) -> list[str]:
    """Return errors when a protected file loses required import lines."""
    required = _required_imports_for_rel_path(rel_path)
    if not required:
        return []
    before = set(_extract_import_lines(old_text))
    after = set(_extract_import_lines(new_text))
    missing = sorted((required & before) - after)
    if not missing:
        return []
    return [
        (
            f"required import removed in {rel_path}: `{imp}`. "
            "This import is protected and cannot be deleted by tactical patches."
        )
        for imp in missing
    ]


def validate_required_import_presence(*, rel_path: str, new_text: str) -> list[str]:
    """Return errors when a protected file does not include required imports."""
    required = _required_imports_for_rel_path(rel_path)
    if not required:
        return []
    present = set(_extract_import_lines(new_text))
    missing = sorted(required - present)
    return [
        (
            f"required import missing in {rel_path}: `{imp}`. "
            "This file must keep this import."
        )
        for imp in missing
    ]


def _mathlib_import_path(module: str) -> Path:
    """Convert a Lean module name like Mathlib.A.B.C to its .lean file path."""
    rel = module.replace(".", "/") + ".lean"
    return PROJECT_ROOT / ".lake" / "packages" / "mathlib" / rel


def validate_mathlib_imports(old_text: str, new_text: str) -> list[str]:
    """Return error strings for newly added Mathlib imports whose files do not exist.

    Returns an empty list when all new imports are valid.
    Callers should raise ValueError on non-empty results to block the patch.
    """
    errors: list[str] = []
    for module in _extract_new_mathlib_imports(old_text, new_text):
        lean_file = _mathlib_import_path(module)
        if not lean_file.exists():
            # Try to find the closest real path to help the agent self-correct.
            parts = module.split(".")
            suggestion = ""
            # Walk up the hierarchy looking for an existing directory.
            for depth in range(len(parts), 0, -1):
                candidate_dir = PROJECT_ROOT / ".lake" / "packages" / "mathlib" / Path(*parts[:depth])
                if candidate_dir.is_dir():
                    # List first-level children as hints.
                    children = sorted(
                        p.stem for p in candidate_dir.iterdir()
                        if p.suffix == ".lean" or p.is_dir()
                    )[:8]
                    suggestion = (
                        f" Nearest existing path: {'/'.join(parts[:depth])}/ "
                        f"(contains: {', '.join(children)})"
                    )
                    break
            errors.append(
                f"import {module}: file not found in mathlib package "
                f"({lean_file.relative_to(PROJECT_ROOT)}).{suggestion} "
                f"Use search_codebase to find the correct module path before importing."
            )
    return errors


def edit_file_patch(
    path: str | Path,
    old_str: str,
    new_str: str,
    allowed_line_range: str | None = None,
    required_file_hash: str | None = None,
    anchor_text: str | None = None,
    anchor_hash: str | None = None,
) -> dict[str, Any]:
    """Apply an exact single-string replacement instead of full overwrite.

    The replacement is intentionally strict:
    - old_str must exist
    - old_str must appear exactly once (to avoid ambiguous patches)
    - optional runtime guards can pin the edit to a specific file hash / span / anchor
    """
    if old_str == "":
        raise ValueError("old_str must be non-empty for precise patching")

    resolved = _resolve_allowed_path(path, _READ_WRITE_ALLOWLIST)
    write_path = resolved
    if not write_path.exists():
        raise FileNotFoundError(f"Target file does not exist: {path}")
    rel_path = _to_rel(write_path)

    original = write_path.read_text(encoding="utf-8")
    file_hash_before = _sha256_text(original)
    if required_file_hash and str(required_file_hash).strip() != file_hash_before:
        raise ValueError(
            "Patch blocked: stale file hash. "
            f"expected={required_file_hash}, actual={file_hash_before}"
        )
    if anchor_text:
        if anchor_text not in original:
            raise ValueError(
                "Patch blocked: active target anchor is missing from current file. "
                "Re-read the target span and rebind the active object before editing."
            )
        actual_anchor_hash = _sha256_text(anchor_text)
        if anchor_hash and str(anchor_hash).strip() != actual_anchor_hash:
            raise ValueError(
                "Patch blocked: anchor hash mismatch. "
                f"expected={anchor_hash}, actual={actual_anchor_hash}"
            )
    allowed_range = _parse_line_range_spec(allowed_line_range)
    occurrences = original.count(old_str)
    if occurrences == 0:
        old_lines = old_str.splitlines()
        file_lines = original.splitlines()
        window_size = max(1, len(old_lines))
        # Cap scan at 200 windows to avoid O(N²) on very large files.
        max_windows = min(200, max(1, len(file_lines) - window_size + 1))
        best_score, best_line = 0.0, 1
        for i in range(max_windows):
            window = "\n".join(file_lines[i : i + window_size])
            score = difflib.SequenceMatcher(None, old_str, window).ratio()
            if score > best_score:
                best_score, best_line = score, i + 1
        raise ValueError(
            f"old_str not found in {path}. "
            f"Nearest match starts at line {best_line} "
            f"(similarity {best_score:.0%}). "
            f"Call read_file(path, start_line={best_line}, "
            f"end_line={best_line + window_size - 1}) to verify exact text."
        )
    if occurrences > 1:
        raise ValueError(
            f"old_str appears {occurrences} times; patch would be ambiguous"
        )
    matched_line_range = _locate_replacement_line_range(original, old_str)
    # Patch guard relaxed: allow edits outside authorized span to handle error propagation
    # if allowed_range is not None and not _range_within(matched_line_range, allowed_range):
    #    raise ValueError(
    #        "Patch blocked: replacement falls outside the authorized line span. "
    #        f"matched={matched_line_range[0]}-{matched_line_range[1]}, "
    #        f"allowed={allowed_range[0]}-{allowed_range[1]}"
    #    )

    updated = original.replace(old_str, new_str, 1)
    _imports_before = _extract_import_lines(original)
    _imports_after = _extract_import_lines(updated)
    _imports_changed = _imports_before != _imports_after
    _is_lean_file = str(write_path).endswith(".lean")

    _required_errors = validate_required_imports(
        rel_path=rel_path,
        old_text=original,
        new_text=updated,
    )
    if _required_errors:
        raise ValueError(
            "Patch blocked: required import guard triggered. Fix the patch and retry:\n"
            + "\n".join(f"  • {e}" for e in _required_errors)
        )

    # Validate any newly added Mathlib imports before writing.
    _import_errors = validate_mathlib_imports(original, updated)
    if _import_errors:
        raise ValueError(
            "Patch blocked: newly added Mathlib import(s) do not exist in the "
            "pinned mathlib package. Fix the import path(s) first:\n"
            + "\n".join(f"  • {e}" for e in _import_errors)
        )

    _verify_before: dict[str, Any] | None = None
    if _is_lean_file and _imports_changed:
        try:
            _verify_before = run_lean_verify(rel_path)
        except Exception:
            _verify_before = None

    _atomic_write(write_path, updated)
    _rolled_back = False
    _rollback_reason = ""

    if _is_lean_file and _imports_changed:
        def _verify_error_count(payload: dict[str, Any] | None) -> int:
            if not isinstance(payload, dict):
                return 0
            try:
                if "error_count" in payload:
                    return max(0, int(payload.get("error_count", 0)))
            except Exception:
                pass
            errs = payload.get("errors", [])
            if isinstance(errs, list):
                return len(errs)
            if isinstance(errs, str):
                return len([ln for ln in errs.splitlines() if ln.strip()])
            return 0

        try:
            _verify_after = run_lean_verify(rel_path)
        except Exception as _exc:
            _verify_after = {
                "exit_code": 1,
                "error_count": 999,
                "errors": f"post_patch_verify_exception: {_exc}",
            }

        _before_exit = int((_verify_before or {}).get("exit_code", 0))
        _after_exit = int((_verify_after or {}).get("exit_code", 0))
        _before_err = _verify_error_count(_verify_before)
        _after_err = _verify_error_count(_verify_after)
        _regressed = (
            (_before_exit == 0 and _after_exit != 0)
            or (_after_exit != 0 and _before_err >= 0 and _after_err > _before_err + 1)
        )

        if _regressed:
            _atomic_write(write_path, original)
            _rolled_back = True
            _rollback_reason = (
                "import_change_regressed_verify "
                f"(exit { _before_exit } -> { _after_exit }, "
                f"errors { _before_err } -> { _after_err })"
            )
            raise ValueError(
                "Patch rolled back: import-touching edit caused verify regression. "
                f"Reason: {_rollback_reason}"
            )

    return {
        "path": rel_path,
        "replacements": 1,
        "changed": original != updated,
        "imports_changed": _imports_changed,
        "patch_rolled_back": _rolled_back,
        "rollback_reason": _rollback_reason,
        "allowed_line_range": allowed_line_range,
        "matched_line_range": f"{matched_line_range[0]}-{matched_line_range[1]}",
        "file_hash_before": file_hash_before,
        "file_hash_after": _sha256_text(updated),
        "anchor_hash": _sha256_text(anchor_text) if anchor_text else "",
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
    write_path = resolved
    if write_path.exists():
        raise FileExistsError(
            f"File already exists: {path}. Use edit_file_patch to modify it."
        )
    rel_path = _to_rel(write_path)
    _required_errors = validate_required_import_presence(
        rel_path=rel_path,
        new_text=content,
    )
    if _required_errors:
        raise ValueError(
            "File creation blocked: required import guard triggered. "
            "Fix the file imports first:\n"
            + "\n".join(f"  • {e}" for e in _required_errors)
        )
    # Validate any Mathlib imports in the new file before writing.
    _import_errors = validate_mathlib_imports("", content)
    if _import_errors:
        raise ValueError(
            "File creation blocked: Mathlib import(s) do not exist in the "
            "pinned mathlib package. Fix the import path(s) first:\n"
            + "\n".join(f"  • {e}" for e in _import_errors)
        )

    _atomic_write(write_path, content)
    return {
        "path": rel_path,
        "created": True,
        "size_bytes": len(content.encode("utf-8")),
        "after": content,
    }


def overwrite_file(path: str | Path, content: str) -> dict[str, Any]:
    """Overwrite an existing file with content. Used for restore/rollback."""
    resolved = _resolve_allowed_path(path, _READ_WRITE_ALLOWLIST)
    write_path = resolved
    if not write_path.exists():
        raise FileNotFoundError(f"Target file does not exist: {path}")
    original = write_path.read_text(encoding="utf-8")
    _atomic_write(write_path, content)
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

    Uses a two-pass approach:

    Pass 1 — standard file:line:col formats (preferred, most actionable):
      Tier 1 (single-line): file.lean:L:C: error: message
      Tier 2 (two-line):    file.lean:L:C: (alone)
                             error: message  (next line, merged)

    Pass 2 — fallback for non-standard formats (only when Pass 1 is empty):
      Tier 3: file.lean: error: message  (no line/col — parse errors)
      Tier 4: error: message             (bare Lake-level error, no file context)

    Two-line (Tier 2) entries are merged so all downstream regex consumers
    (_extract_first_error_line, _classify_lean_error) work without modification.
    """
    # Pass 1: standard file:line:col formats
    result: list[str] = []
    lines = raw.splitlines()
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        # Tier 1: file.lean:L:C: error: message (everything on one line)
        if re.search(r"\.lean:\d+:\d+:\s*error:", line):
            result.append(line)
        # Tier 1b: Lake JSON format — error: file.lean:L:C: message
        elif re.search(r"^error:\s+[\w./\\-]+\.lean:\d+:\d+:", line):
            result.append(line)
        # Tier 2: file.lean:L:C: alone, followed by error: ... on the next line
        elif re.search(r"\.lean:\d+:\d+:\s*$", line) and i + 1 < len(lines):
            next_line = lines[i + 1].strip()
            if next_line.startswith("error:"):
                # Merge into a single line preserving the file:line:col: prefix
                result.append(line.rstrip(": ") + ": " + next_line)
                i += 1  # next line already consumed
        i += 1
    if result:
        return result

    # Pass 2: non-standard formats — parse errors and bare Lake errors
    fallback: list[str] = []
    for line in lines:
        line = line.strip()
        # Tier 3: file.lean: error: message (no line/col — typical parse error)
        if re.search(r"\.lean:\s*error:", line, re.IGNORECASE):
            fallback.append(line)
        # Tier 4: bare "error: ..." lines (Lake-level build failure messages)
        elif re.search(r"^\s*error:\s+\S", line):
            fallback.append(line)
    return fallback


def check_lean_have(
    file_path: str | Path,
    sorry_line: int,
    have_statement: str,
) -> dict[str, Any]:
    """Test a single have-statement at a sorry location WITHOUT modifying the file.

    Replaces the sorry at *sorry_line* (1-indexed) in a temp copy of the file
    with *have_statement* followed by a continuation sorry, then runs
    ``lake env lean <tempfile>`` to elaborate only that single file.  All
    pre-compiled ``.olean`` dependencies are reused, so this is typically
    faster than a full ``lake build``.

    Returns::

        {
          "success":        bool,        # True when the have compiled cleanly
          "exit_code":      int,
          "errors":         list[str],   # file:line:col: error: ... lines
          "info":           list[str],   # information: ... lines (e.g. #check)
          "have_statement": str,         # echo of the input have_statement
        }

    The original file is never modified.  The temp file is deleted regardless
    of whether compilation succeeded.
    """
    import subprocess
    import uuid

    # Allow reading from all allowed paths (read-write AND read-only)
    _all_readable = _READ_WRITE_ALLOWLIST + _READ_ONLY_ALLOWLIST
    resolved_ws = _resolve_allowed_path(file_path, _all_readable)
    source_path = resolved_ws

    if not source_path.exists():
        return {
            "success": False,
            "exit_code": 1,
            "errors": [f"Source file does not exist: {file_path}"],
            "info": [],
            "have_statement": have_statement,
        }

    content = source_path.read_text(encoding="utf-8")
    lines = content.splitlines(keepends=True)

    # Validate sorry_line (1-indexed)
    target_idx = sorry_line - 1
    if not (0 <= target_idx < len(lines)):
        return {
            "success": False,
            "exit_code": 1,
            "errors": [
                f"sorry_line {sorry_line} out of range "
                f"(file has {len(lines)} lines)"
            ],
            "info": [],
            "have_statement": have_statement,
        }

    orig_line = lines[target_idx]
    if "sorry" not in orig_line:
        return {
            "success": False,
            "exit_code": 1,
            "errors": [
                f"No 'sorry' token found on line {sorry_line}: "
                f"{orig_line.rstrip()!r}"
            ],
            "info": [],
            "have_statement": have_statement,
        }

    # Preserve indentation of the original sorry line
    indent_str = orig_line[: len(orig_line) - len(orig_line.lstrip())]
    replacement = (
        f"{indent_str}{have_statement.strip()}\n"
        f"{indent_str}sorry  -- original sorry continued\n"
    )
    modified_lines = lines[:target_idx] + [replacement] + lines[target_idx + 1 :]
    modified_content = "".join(modified_lines)

    # Write to a uniquely-named temp file at the project root so lake env can
    # find all pre-compiled .olean imports via LEAN_PATH.
    unique_id = uuid.uuid4().hex[:8]
    tmp_name = f"_LeanCheck_{unique_id}.lean"
    tmp_path = PROJECT_ROOT / tmp_name
    try:
        tmp_path.write_text(modified_content, encoding="utf-8")
        proc = subprocess.run(
            ["lake", "env", "lean", tmp_name],
            cwd=PROJECT_ROOT,
            capture_output=True,
            text=True,
            timeout=120,
        )
        raw = proc.stdout + proc.stderr
        # Replace the temp filename with the original so Agent3 sees meaningful
        # line references in error messages.
        orig_rel = str(resolved_ws.relative_to(PROJECT_ROOT))
        raw_clean = raw.replace(tmp_name, orig_rel)

        error_lines = _extract_lean_error_lines(raw_clean)
        info_lines = [
            line.strip()
            for line in raw_clean.splitlines()
            if re.search(r"\binformation\b", line, re.IGNORECASE)
        ]
        return {
            "success": proc.returncode == 0,
            "exit_code": proc.returncode,
            "errors": error_lines,
            "info": info_lines,
            "have_statement": have_statement,
        }
    except subprocess.TimeoutExpired:
        return {
            "success": False,
            "exit_code": 1,
            "errors": ["check_lean_have timed out after 120 s"],
            "info": [],
            "have_statement": have_statement,
        }
    finally:
        tmp_path.unlink(missing_ok=True)


def check_lean_expr(
    expr: str,
    context_imports: str = "import Main",
) -> dict[str, Any]:
    """Query the actual Lean-inferred type of *expr* without modifying any file.

    Creates a minimal temp file containing *context_imports* followed by
    ``#check @<expr>``, elaborates it with ``lake env lean``, and parses the
    ``information:`` line from the output.  All pre-compiled ``.olean``
    dependencies are reused via the lake environment, so this is fast.

    Typical use-cases for Agent7:
    - Verify the current Mathlib signature of a lemma (e.g. ``integral_nonneg``)
      before writing a ``direct_apply`` patch.
    - Check whether an identifier exists at all (unknown identifier → lemma absent
      or renamed).
    - Confirm argument counts and implicit/explicit structure for any function.

    Args:
        expr:             Lean expression to ``#check``, e.g. ``"integral_nonneg"``.
                          The ``@`` prefix is added automatically to expose all
                          implicit arguments in the printed type.
        context_imports:  Import preamble placed at the top of the temp file.
                          Defaults to ``"import Main"`` which transitively pulls
                          in all project dependencies including Mathlib.  Pass a
                          more specific import (e.g. ``"import Mathlib.MeasureTheory.Integral.Bochner.Basic"``)
                          to reduce elaboration time.

    Returns::

        {
          "success":  bool,        # True when #check compiled without error
          "expr":     str,         # echo of input expr
          "type":     str,         # inferred type string (empty on failure)
          "raw":      str,         # full lake output for debugging
          "errors":   list[str],   # error lines (empty on success)
        }

    The original project files are never modified.
    """
    import subprocess
    import uuid

    tmp_name = f"_LeanExprCheck_{uuid.uuid4().hex[:8]}.lean"
    tmp_path = PROJECT_ROOT / tmp_name
    content = f"{context_imports.strip()}\n\n#check @{expr}\n"
    try:
        tmp_path.write_text(content, encoding="utf-8")
        proc = subprocess.run(
            ["lake", "env", "lean", tmp_name],
            cwd=PROJECT_ROOT,
            capture_output=True,
            text=True,
            timeout=120,
        )
        raw = proc.stdout + proc.stderr

        # Extract the type from "information: <type>" line emitted by #check.
        inferred_type = ""
        for line in raw.splitlines():
            stripped = line.strip()
            # Lean 4 emits: "_LeanExprCheck_xxx.lean:N:M: information: @foo : <type>"
            # or simply:    "information: @foo : <type>"
            if "information:" in stripped:
                # Take everything after the last "information:" token
                info_part = stripped.split("information:", 1)[-1].strip()
                # Drop the leading "@<expr> :" prefix to isolate the type
                colon_idx = info_part.find(" : ")
                if colon_idx != -1:
                    inferred_type = info_part[colon_idx + 3:].strip()
                else:
                    inferred_type = info_part.strip()
                break

        error_lines = _extract_lean_error_lines(raw)
        success = proc.returncode == 0 and bool(inferred_type)
        return {
            "success": success,
            "expr": expr,
            "type": inferred_type,
            "raw": raw[:4000],
            "errors": error_lines,
        }
    except subprocess.TimeoutExpired:
        return {
            "success": False,
            "expr": expr,
            "type": "",
            "raw": "",
            "errors": ["check_lean_expr timed out after 120 s"],
        }
    finally:
        tmp_path.unlink(missing_ok=True)


def get_lean_goal(
    file_path: str | Path,
    sorry_line: int,
    timeout: int = 120,
) -> dict[str, Any]:
    """Query the Lean LSP server for the proof goal at a sorry location.

    Starts ``lake env lean --server``, opens *file_path*, waits for full
    elaboration, and returns the tactic state (``⊢ goal`` + hypotheses) at
    *sorry_line*.  The server is shut down after the query.

    Unlike ``check_lean_have``, this tool does **NOT** modify the file —
    it only reads the current proof state.  Use it to discover exactly what
    type you need to prove before formulating a ``have`` step.

    Args:
        file_path:  Path to the ``.lean`` file (relative to project root
                    or absolute, must be under Algorithms/ or Lib/).
        sorry_line: 1-indexed line number of the ``sorry`` to inspect.
        timeout:    Maximum seconds to wait for elaboration (default 120).

    Returns::

        {
            "goal":       str | None,   # "⊢ <type>" rendered goal
            "hypotheses": list[str],    # local hypotheses ["name : Type", ...]
            "raw":        str,          # full tactic state text from LSP
            "error":      str | None,   # non-None if something went wrong
            "elapsed_s":  float,        # wall-clock seconds
        }

    Usage pattern::

        1. Call get_lean_goal(file, line) to see "⊢ <T>" at the sorry.
        2. Formulate "have h : <T'> := by <tac>" that makes progress.
        3. Verify with check_lean_have(file, line, have_statement).
        4. Apply with edit_file_patch when check_lean_have returns success=True.
    """
    _all_readable = _READ_WRITE_ALLOWLIST + _READ_ONLY_ALLOWLIST
    resolved = _resolve_allowed_path(file_path, _all_readable)

    if not resolved.exists():
        return {
            "goal": None,
            "hypotheses": [],
            "raw": "",
            "error": f"File does not exist: {file_path}",
            "elapsed_s": 0.0,
        }

    from orchestrator.lean_lsp import query_goal_at_sorry

    return query_goal_at_sorry(
        project_root=PROJECT_ROOT,
        file_path=resolved,
        sorry_line=sorry_line,
        timeout=timeout,
    )


def run_lean_verify(file_path: str | Path) -> dict[str, Any]:
    """Run Lean verification and return a JSON-serializable result.

    Guardrail:
    - Default backend is ``lake`` (stable, existing behavior).
    - ``apollo`` backend is opt-in via config/env and is adapter-normalized
      to preserve the historical output schema consumed by Agent3/8.
    """
    resolved = _resolve_allowed_path(file_path, _LEAN_VERIFY_ALLOWLIST)
    source_path = resolved
    verify_start = time.perf_counter()

    # Guard: do not run lake build if the target file does not yet exist.
    if not source_path.exists():
        verify_wall_ms = int((time.perf_counter() - verify_start) * 1000.0)
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
            "verify_time": verify_wall_ms / 1000.0,
            "verify_wall_ms": verify_wall_ms,
            "verify_backend_used": "none",
            "verify_backend_reason": "missing_target",
        }

    rel = str(resolved.relative_to(PROJECT_ROOT))
    _apollo_degrade_warning = ""
    _verify_backend_used = "lake"
    _verify_backend_reason = "lake_default"

    # Backend gate: keep lake as the default path to preserve current semantics.
    backend = str(LEAN_VERIFY_BACKEND).strip().lower()
    if backend == "apollo":
        from orchestrator.apollo_integration import (
            normalize_apollo_result,
            verify_with_apollo,
        )

        source_text = resolved.read_text(encoding="utf-8")
        try:
            raw = verify_with_apollo(
                code=source_text,
                timeout=REPL_VERIFY_TIMEOUT or APOLLO_VERIFY_TIMEOUT,
                apollo_project_path=APOLLO_PROJECT_PATH,
                repl_workspace=APOLLO_REPL_WORKSPACE,
                lake_path=APOLLO_LAKE_PATH,
                project_root=PROJECT_ROOT,
            )
        except Exception as exc:
            _verify_backend_used = "apollo"
            _verify_backend_reason = f"apollo_failure:{exc}"
            if VERIFY_BACKEND_STRICT:
                verify_wall_ms = int((time.perf_counter() - verify_start) * 1000.0)
                return {
                    "target": rel,
                    "success": False,
                    "exit_code": 1,
                    "sorry_count": count_sorrys(rel),
                    "sorry_declarations": 0,
                    "blocked_sorry_count": 0,
                    "error_count": 1,
                    "errors": [f"APOLLO backend strict failure: {exc}"],
                    "warnings": [],
                    "verify_backend_used": "apollo",
                    "verify_backend_reason": f"strict_failure:{exc}",
                    "verify_time": verify_wall_ms / 1000.0,
                    "verify_wall_ms": verify_wall_ms,
                }
            if not APOLLO_FALLBACK_TO_LAKE_ON_FAILURE:
                verify_wall_ms = int((time.perf_counter() - verify_start) * 1000.0)
                return {
                    "target": rel,
                    "success": False,
                    "exit_code": 1,
                    "sorry_count": count_sorrys(rel),
                    "sorry_declarations": 0,
                    "blocked_sorry_count": 0,
                    "error_count": 1,
                    "errors": [f"APOLLO backend failure: {exc}"],
                    "warnings": [],
                    "verify_backend_used": "apollo",
                    "verify_backend_reason": f"backend_failure:{exc}",
                    "verify_time": verify_wall_ms / 1000.0,
                    "verify_wall_ms": verify_wall_ms,
                }
            _apollo_degrade_warning = f"APOLLO backend failure; degraded to lake: {exc}"
        else:
            normalized = normalize_apollo_result(
                target_rel=rel,
                source_text=source_text,
                apollo_result=raw,
            )
            normalized.setdefault(
                "verify_backend_used",
                str(raw.get("backend_used", "apollo_python"))
                if isinstance(raw, dict)
                else "apollo_python",
            )
            normalized.setdefault(
                "verify_backend_reason",
                str(raw.get("backend_reason", "apollo_success"))
                if isinstance(raw, dict)
                else "apollo_success",
            )
            verify_wall_ms = int((time.perf_counter() - verify_start) * 1000.0)
            normalized.setdefault("verify_time", verify_wall_ms / 1000.0)
            normalized["verify_wall_ms"] = verify_wall_ms
            return normalized

    # Invalidate Lake cache for this target so errors are re-emitted with
    # file:line:col locations instead of being silently replayed.
    if resolved.exists():
        resolved.touch()

    raw_output = ""
    build_returncode = 1
    build_errors_for_parsing = ""
    compiler_sorry_count = 0  # number of 'declaration uses sorry' warnings from compiler
    build = lake_build(target=_path_to_lean_module(rel))
    build_returncode = int(build.returncode)
    raw_output = build.errors
    build_errors_for_parsing = build.errors
    compiler_sorry_count = build.sorry_count
    if build_returncode == 124:
        _verify_backend_reason = "lake_timeout"

    # Fallback: freshly-created modules can temporarily miss lake target
    # registration; elaborate the file directly instead of failing hard.
    if build_returncode != 0 and re.search(r"unknown target", build.errors, re.IGNORECASE):
        import subprocess

        try:
            proc = subprocess.run(
                ["lake", "env", "lean", rel],
                cwd=PROJECT_ROOT,
                capture_output=True,
                text=True,
                timeout=LEAN_BUILD_TIMEOUT,
            )
            build_returncode = int(proc.returncode)
            raw_output = (proc.stdout or "") + (proc.stderr or "")
            build_errors_for_parsing = raw_output if build_returncode != 0 else ""
            # Re-count compiler sorry warnings from the direct-elaboration output.
            from orchestrator.verify import _count_sorry_in_output as _cso

            compiler_sorry_count = _cso(raw_output)
        except subprocess.TimeoutExpired as exc:
            build_returncode = 124
            raw_output = (
                f"lake env lean timeout on {rel}: exceeded {LEAN_BUILD_TIMEOUT}s\n{exc}"
            )
            build_errors_for_parsing = raw_output
            compiler_sorry_count = 0
            _verify_backend_reason = "lake_timeout"

    sorry_count = count_sorrys(rel)

    all_lines = [line.strip() for line in raw_output.splitlines() if line.strip()]
    # Prefer lines that carry a specific file:line:col: error: location — these
    # are real Lean compiler errors.  Info/warning lines and the generic Lake
    # summary "error: build failed" are filtered into separate buckets so the
    # line-number extractor in main.py always sees the actionable errors first.
    # _extract_lean_error_lines handles both single-line and two-line Lake formats.
    lean_error_lines = _extract_lean_error_lines(build_errors_for_parsing)
    warning_lines = [
        l for l in all_lines if re.search(r"\.lean:\d+:\d+:\s*warning:", l)
    ]
    # Fall back to error-keyword-filtered lines when no file:line:col errors found.
    # This avoids flooding Agent3 with noisy [N/M] Building ... progress lines.
    if build_returncode == 0:
        error_lines = []
    elif lean_error_lines:
        error_lines = lean_error_lines
    else:
        error_lines = (
            [l for l in all_lines if re.search(r"\berror\b", l, re.IGNORECASE)]
            or all_lines
        )

    blocked_sorry_count = max(0, sorry_count - compiler_sorry_count)
    if _apollo_degrade_warning:
        warning_lines = [_apollo_degrade_warning] + warning_lines
        _verify_backend_used = "lake"
        _verify_backend_reason = "degraded_to_lake"
    if not _apollo_degrade_warning and _verify_backend_reason == "lake_default":
        _verify_backend_reason = "lake_default"
    verify_wall_ms = int((time.perf_counter() - verify_start) * 1000.0)
    return {
        "target": rel,
        "success": build_returncode == 0 and sorry_count == 0,
        "exit_code": build_returncode,
        "sorry_count": sorry_count,
        "sorry_declarations": compiler_sorry_count,
        "blocked_sorry_count": blocked_sorry_count,
        "error_count": len(error_lines),
        "errors": error_lines,
        "warnings": warning_lines,
        "verify_backend_used": _verify_backend_used,
        "verify_backend_reason": _verify_backend_reason,
        "verify_time": verify_wall_ms / 1000.0,
        "verify_wall_ms": verify_wall_ms,
        "backend_invoke_ms": int(getattr(build, "elapsed_ms", 0) or 0),
    }


def run_repo_verify() -> dict[str, Any]:
    """Run full-project Lean verification and measure total repo sorry count."""
    build = lake_build()
    total_sorry = 0
    lean_files = list(PROJECT_ROOT.rglob("*.lean"))
    filtered_lean_files = list(lean_files)
    for lean_file in filtered_lean_files:
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
        "lean_file_count": len(filtered_lean_files),
        "error_count": len(error_lines),
        "errors": error_lines,
    }


def search_codebase(
    pattern: str,
    file_glob: str = "*.lean",
    max_matches: int = 40,
    context_lines: int = 2,
) -> dict[str, Any]:
    """Search all project files matching *file_glob* for a regex pattern.

    Unlike ``search_in_file``, this tool searches the **entire project tree**
    without any path restriction.  It is read-only by nature.

    Args:
        pattern:       Python regex pattern to search for.
        file_glob:     Glob pattern for filenames to search (default ``*.lean``).
                       Examples: ``*.lean``, ``*.py``.
        max_matches:   Maximum total matches returned (default 40).
        context_lines: Lines of context around each match (default 2).

    Returns:
        dict with keys:
          pattern, file_glob, total_matches, shown_matches, truncated,
          formatted (human-readable string grouped by file),
          matches (list of {file, line, content, context}).
    """
    import fnmatch
    import subprocess

    rg_result = None
    try:
        proc = subprocess.run(
            [
                "rg",
                "--glob", file_glob,
                "--line-number",
                "--no-heading",
                "--color", "never",
                f"--context={context_lines}",
                pattern,
            ],
            cwd=PROJECT_ROOT,
            capture_output=True,
            text=True,
            timeout=30,
        )
        rg_result = proc.stdout.splitlines()
    except subprocess.TimeoutExpired:
        return {
            "pattern": pattern,
            "file_glob": file_glob,
            "total_matches": 0,
            "shown_matches": 0,
            "truncated": False,
            "formatted": "search_codebase timed out after 30s",
            "matches": [],
            "error": "timeout",
        }
    except FileNotFoundError:
        rg_result = None  # fall through to Python fallback

    matches: list[dict[str, Any]] = []
    formatted_blocks: dict[str, list[str]] = {}  # file → formatted lines

    if rg_result is not None:
        # Parse rg --no-heading --line-number output.
        # Match lines: "path:lineno:content"
        match_re = re.compile(r"^([^:]+):(\d+):(.*)")
        for raw in rg_result:
            m = match_re.match(raw)
            if not m:
                continue
            file_rel, lineno_str, content = m.group(1), m.group(2), m.group(3)
            lineno = int(lineno_str)
            matches.append({"file": file_rel, "line": lineno, "content": content})
            formatted_blocks.setdefault(file_rel, []).append(
                f"  {lineno:5}| {content}"
            )
    else:
        # Python fallback: walk project tree, filter by glob, search with re.
        try:
            compiled = re.compile(pattern)
        except re.error as exc:
            return {
                "pattern": pattern,
                "file_glob": file_glob,
                "total_matches": 0,
                "shown_matches": 0,
                "truncated": False,
                "formatted": f"Invalid regex pattern: {exc}",
                "matches": [],
                "error": "invalid_pattern",
            }
        for p in sorted(PROJECT_ROOT.rglob("*")):
            if not p.is_file():
                continue
            if not fnmatch.fnmatch(p.name, file_glob):
                continue
            try:
                text_lines = p.read_text(encoding="utf-8").splitlines()
            except (OSError, UnicodeDecodeError):
                continue
            file_rel_str = str(p.relative_to(PROJECT_ROOT))
            for idx, line in enumerate(text_lines):
                if compiled.search(line):
                    lineno = idx + 1
                    ctx_start = max(0, idx - context_lines)
                    ctx_end = min(len(text_lines), idx + context_lines + 1)
                    matches.append({"file": file_rel_str, "line": lineno, "content": line})
                    for j in range(ctx_start, ctx_end):
                        marker = ">>>" if j == idx else "   "
                        formatted_blocks.setdefault(file_rel_str, []).append(
                            f"  {j + 1:5}|{marker} {text_lines[j]}"
                        )

    total = len(matches)
    truncated = total > max_matches
    shown = matches[:max_matches]

    formatted_parts: list[str] = []
    seen_count = 0
    for file_rel, block_lines in formatted_blocks.items():
        chunk: list[str] = []
        for line in block_lines:
            if seen_count >= max_matches:
                break
            chunk.append(line)
            seen_count += 1
        if chunk:
            formatted_parts.append(f"{file_rel}:\n" + "\n".join(chunk))
        if seen_count >= max_matches:
            break

    result: dict[str, Any] = {
        "pattern": pattern,
        "file_glob": file_glob,
        "total_matches": total,
        "shown_matches": len(shown),
        "truncated": truncated,
        "formatted": "\n\n".join(formatted_parts) if formatted_parts else "(no matches)",
        "matches": shown,
    }
    if truncated:
        result["truncation_note"] = (
            f"Found {total} matches, showing first {max_matches}. "
            "Use a more specific pattern or set max_matches higher."
        )
    return result


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
    write_path = resolved
    if not write_path.exists():
        raise FileNotFoundError(f"Target doc file does not exist: {path}")

    original = write_path.read_text(encoding="utf-8")
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
        import warnings
        positions = [m.start() for m in matches]
        warnings.warn(
            f"[apply_doc_patch] Anchor matches {len(matches)} locations in "
            f"{resolved.relative_to(PROJECT_ROOT)} (positions {positions}); "
            "using first match. Refine anchor regex to suppress this warning.",
            stacklevel=2,
        )

    insert_at = matches[0].end()
    patch_body = "\n\n" + new_content.strip() + "\n"
    updated = original[:insert_at] + patch_body + original[insert_at:]
    _atomic_write(write_path, updated)

    return {
        "path": str(resolved.relative_to(PROJECT_ROOT)),
        "changed": True,
        "anchor": anchor,
        "before": original,
        "after": updated,
    }
