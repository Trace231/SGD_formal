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

def _file_hash(path: str | Path) -> str | None:
    """Return MD5 hex-digest of *path*, or None if the file does not exist."""
    try:
        content = load_file(path)
    except FileNotFoundError:
        return None
    return hashlib.md5(content.encode("utf-8")).hexdigest()


def _git_diff_files() -> set[str]:
    """Return tracked files with unstaged/staged modifications."""
    result = subprocess.run(
        ["git", "diff", "--name-only"],
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
    )
    return set(result.stdout.splitlines())


def _git_untracked_files() -> set[str]:
    """Return untracked files in the repository."""
    result = subprocess.run(
        ["git", "ls-files", "--others", "--exclude-standard"],
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
    )
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


def _git_head_sha() -> str:
    """Return current HEAD commit SHA."""
    result = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    return result.stdout.strip()


def _git_is_dirty() -> bool:
    """Return True when tracked or untracked changes are present."""
    result = subprocess.run(
        ["git", "status", "--porcelain"],
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    return bool(result.stdout.strip())


def _capture_git_run_snapshot(run_id: str) -> GitRunSnapshot:
    """Capture HEAD and optionally stash local dirt for rollback safety."""
    start_sha = _git_head_sha()
    pre_run_dirty = _git_is_dirty()
    if not pre_run_dirty:
        return GitRunSnapshot(
            start_sha=start_sha,
            pre_run_dirty=False,
            stash_used=False,
            stash_ref=None,
        )

    # Save all local modifications (tracked + untracked) so run rollback can
    # safely reset and then restore user state.
    stash_msg = f"orchestrator-pre-run-{run_id}"
    subprocess.run(
        ["git", "stash", "push", "-u", "-m", stash_msg],
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    return GitRunSnapshot(
        start_sha=start_sha,
        pre_run_dirty=True,
        stash_used=True,
        stash_ref="stash@{0}",
    )


def _restore_snapshot_on_success(snapshot: GitRunSnapshot) -> None:
    """Restore pre-run user state after successful run."""
    if not snapshot.stash_used:
        return
    subprocess.run(
        ["git", "stash", "pop", "--index", snapshot.stash_ref or "stash@{0}"],
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )


def _rollback_to_snapshot(snapshot: GitRunSnapshot) -> None:
    """Rollback workspace to run-start commit and restore pre-run dirt."""
    subprocess.run(
        ["git", "reset", "--hard", snapshot.start_sha],
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    # Remove untracked files generated during this run.
    subprocess.run(
        ["git", "clean", "-fd"],
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    if snapshot.stash_used:
        subprocess.run(
            ["git", "stash", "pop", "--index", snapshot.stash_ref or "stash@{0}"],
            cwd=PROJECT_ROOT,
            capture_output=True,
            text=True,
            check=True,
        )


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


