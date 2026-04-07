"""Git / Lakefile utility functions for the orchestration pipeline."""
from __future__ import annotations

import hashlib
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path

from rich.console import Console

from orchestrator.config import PROJECT_ROOT
from orchestrator.file_io import load_file

console = Console()
_GIT_WARNED = False


def _warn_git_unavailable(message: str) -> None:
    """Emit one warning when git metadata is unavailable for this run."""
    global _GIT_WARNED
    if _GIT_WARNED:
        return
    _GIT_WARNED = True
    console.print(f"[yellow][Git] {message} — continuing without git metadata[/yellow]")


def _run_git(args: list[str], *, check: bool = False) -> subprocess.CompletedProcess[str] | None:
    """Run a git command with fail-open behavior for sandbox/CI edge cases."""
    try:
        result = subprocess.run(
            ["git", *args],
            cwd=PROJECT_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
    except FileNotFoundError:
        _warn_git_unavailable("git executable not found")
        if check:
            raise
        return None

    if result.returncode != 0:
        stderr = (result.stderr or "").strip()
        if result.returncode == 128:
            _warn_git_unavailable(
                f"git {' '.join(args)} failed with code 128 ({stderr or 'repository state unavailable'})"
            )
            if check:
                raise subprocess.CalledProcessError(
                    result.returncode,
                    ["git", *args],
                    output=result.stdout,
                    stderr=result.stderr,
                )
            return None
        if check:
            raise subprocess.CalledProcessError(
                result.returncode,
                ["git", *args],
                output=result.stdout,
                stderr=result.stderr,
            )
    return result


def _file_hash(path: str | Path) -> str | None:
    """Return MD5 hex-digest of *path*, or None if the file does not exist."""
    try:
        content = load_file(path)
    except FileNotFoundError:
        return None
    return hashlib.md5(content.encode("utf-8")).hexdigest()


def _git_diff_files() -> set[str]:
    """Return tracked files with unstaged/staged modifications."""
    result = _run_git(["diff", "--name-only"])
    if result is None:
        return set()
    return set(result.stdout.splitlines())


def _git_untracked_files() -> set[str]:
    """Return untracked files in the repository."""
    result = _run_git(["ls-files", "--others", "--exclude-standard"])
    if result is None:
        return set()
    return set(result.stdout.splitlines())


def _capture_lean_baseline() -> tuple[set[str], set[str]]:
    """Capture pre-run Lean file baseline without mutating git state."""
    tracked = {f for f in _git_diff_files() if f.endswith(".lean")}
    untracked = {f for f in _git_untracked_files() if f.endswith(".lean")}
    return tracked, untracked


@dataclass
class GitRunSnapshot:
    """Git snapshot captured at run start for safe rollback."""

    start_sha: str
    pre_run_dirty: bool
    stash_used: bool
    stash_ref: str | None
    # In-memory content snapshot of .md files as they existed on disk at run
    # start (including any uncommitted local edits).  Used by _rollback_to_snapshot
    # to restore exactly the pre-run disk state rather than the last git commit.
    md_snapshots: dict[str, str] | None = None


def _git_head_sha() -> str:
    """Return current HEAD commit SHA."""
    result = _run_git(["rev-parse", "HEAD"])
    if result is None:
        return "unknown"
    return result.stdout.strip() or "unknown"


def _git_is_dirty() -> bool:
    """Return True when tracked or untracked changes are present."""
    result = _run_git(["status", "--porcelain"])
    if result is None:
        return False
    return bool(result.stdout.strip())


def _capture_git_run_snapshot(run_id: str) -> GitRunSnapshot:
    """Capture HEAD SHA and snapshot current on-disk content of all .md files.

    Source files (.lean, .py) and Lib staging-area entries are left completely
    untouched.  The in-memory md_snapshots dict lets _rollback_to_snapshot
    restore the exact pre-run disk state (including any uncommitted local edits)
    rather than falling back to the last git commit.
    """
    _ = run_id
    start_sha = _git_head_sha()

    # Walk docs/ and any other tracked .md files for a pre-run disk snapshot.
    md_snapshots: dict[str, str] = {}
    result = _run_git(["ls-files", "--", "*.md"])
    if result is not None:
        for rel in result.stdout.splitlines():
            p = PROJECT_ROOT / rel
            try:
                md_snapshots[rel] = p.read_text(encoding="utf-8")
            except OSError:
                pass

    return GitRunSnapshot(
        start_sha=start_sha,
        pre_run_dirty=_git_is_dirty(),
        stash_used=False,
        stash_ref=None,
        md_snapshots=md_snapshots,
    )


def _restore_snapshot_on_success(snapshot: GitRunSnapshot) -> None:
    """No-op: source and lib files are intentionally left in their run-end state."""
    _ = snapshot
    return


def _rollback_to_snapshot(snapshot: GitRunSnapshot) -> None:
    """On failure: restore .md docs to their exact pre-run on-disk state.

    Uses the in-memory md_snapshots captured at run start, so uncommitted
    local edits that existed before the run are also preserved correctly.
    .lean files (including Lib/), Python files, and the git staging area are
    left completely untouched.
    """
    snapshots = snapshot.md_snapshots or {}

    # Restore every .md file that is now different from its pre-run content.
    restored: list[str] = []
    for rel, original_content in snapshots.items():
        p = PROJECT_ROOT / rel
        try:
            current = p.read_text(encoding="utf-8")
        except OSError:
            current = None
        if current != original_content:
            p.write_text(original_content, encoding="utf-8")
            restored.append(rel)

    if restored:
        console.print(
            f"[yellow][Git] Rolled back {len(restored)} doc file(s): "
            + ", ".join(restored)
        )

    # Remove any *new* untracked .md files the run created (not in snapshot).
    ls_result = _run_git(["ls-files", "--others", "--exclude-standard"])
    if ls_result is not None:
        for fname in ls_result.stdout.splitlines():
            if fname.endswith(".md") and fname not in snapshots:
                try:
                    (PROJECT_ROOT / fname).unlink()
                    console.print(f"[yellow][Git] Removed new doc file: {fname}")
                except OSError:
                    pass


def _get_modified_lean_files(
    baseline_tracked: set[str],
    baseline_untracked: set[str],
) -> list[str]:
    """Return Lean files changed since run start, excluding pre-existing dirt."""
    tracked_now = {f for f in _git_diff_files() if f.endswith(".lean")}
    untracked_now = {f for f in _git_untracked_files() if f.endswith(".lean")}

    newly_tracked = tracked_now - baseline_tracked
    newly_untracked = untracked_now - baseline_untracked
    baseline_untracked_promoted = tracked_now & baseline_untracked

    return sorted(newly_tracked | newly_untracked | baseline_untracked_promoted)


def _ensure_algorithm_in_lakefile(algorithm: str) -> bool:
    """Ensure Algorithms.<algorithm> is listed in lakefile.lean's SGDAlgorithms roots.

    If the module is already present this is a no-op and returns False.  If it
    is absent it is appended to the end of the roots list so ``lake build
    SGDAlgorithms`` includes the newly-created file and returns True.
    """
    lakefile = PROJECT_ROOT / "lakefile.lean"
    if not lakefile.exists():
        console.print(f"[yellow][lakefile] lakefile.lean not found — skipping auto-update")
        return False

    module_name = f"`Algorithms.{algorithm}"
    content = lakefile.read_text(encoding="utf-8")

    if module_name in content:
        return False  # already registered — no-op

    # Find the closing bracket of the SGDAlgorithms roots list and insert before it.
    # Pattern matches the last backtick-module entry in the roots := #[...] block.
    roots_re = re.compile(
        r"(lean_lib SGDAlgorithms.*?roots\s*:=\s*#\[)(.*?)(\])",
        re.DOTALL,
    )
    m = roots_re.search(content)
    if not m:
        console.print(
            "[yellow][lakefile] Could not find SGDAlgorithms roots list — "
            "please add the module manually."
        )
        return False

    updated = content[: m.start(3)] + f", {module_name}" + content[m.start(3) :]
    lakefile.write_text(updated, encoding="utf-8")
    console.print(f"[green][lakefile] Added {module_name} to SGDAlgorithms roots.")
    return True


def _remove_algorithm_from_lakefile(algorithm: str) -> None:
    """Remove Algorithms.<algorithm> from lakefile.lean SGDAlgorithms roots (rollback).

    Called when a pipeline run fails or is interrupted to undo the temporary
    registration added at the start of Phase 3.
    """
    lakefile = PROJECT_ROOT / "lakefile.lean"
    if not lakefile.exists():
        return

    module_name = f"`Algorithms.{algorithm}"
    content = lakefile.read_text(encoding="utf-8")
    if module_name not in content:
        return

    # Try removing ", `Algorithms.X" (module was appended after existing entries).
    updated = re.sub(r",\s*" + re.escape(module_name), "", content)
    if updated == content:
        # Fallback: module appears first — remove "`Algorithms.X, " or "`Algorithms.X".
        updated = re.sub(re.escape(module_name) + r",?\s*", "", content)

    lakefile.write_text(updated, encoding="utf-8")
    console.print(f"[yellow][lakefile] Removed {module_name} from SGDAlgorithms roots (rollback).")
