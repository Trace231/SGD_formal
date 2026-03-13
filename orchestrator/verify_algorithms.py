"""CLI: verify which Algorithms/*.lean files are build-successful.

An algorithm file is considered "qualified" iff:
  1) `lake env lean <file>` exits with code 0, and
  2) source-level `sorry` count is 0.

Default behavior is non-blocking: the command exits 0 even when some
algorithms are unqualified. Use `--fail-on-unqualified` for CI-style behavior.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from dataclasses import asdict, dataclass
from pathlib import Path

from orchestrator.config import ALGORITHMS_DIR, PROJECT_ROOT
from orchestrator.verify import count_sorrys


@dataclass
class AlgorithmBuildStatus:
    algorithm: str
    file: str
    build_ok: bool
    sorry_count: int
    qualified: bool
    returncode: int
    error_snippet: str


def _discover_algorithm_files() -> list[Path]:
    return sorted(ALGORITHMS_DIR.glob("*.lean"))


def _snippet(text: str, max_lines: int = 8) -> str:
    if not text.strip():
        return ""
    lines = [line for line in text.strip().splitlines() if line.strip()]
    return "\n".join(lines[:max_lines])


def _preflight_lake_config() -> tuple[bool, str]:
    """Fast preflight to fail early on broken lakefile/configuration."""
    result = subprocess.run(
        ["lake", "env", "lean", "--version"],
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
        timeout=60,
    )
    if result.returncode == 0:
        return True, ""
    return False, _snippet(result.stderr or result.stdout)


def _check_file(file_path: Path) -> AlgorithmBuildStatus:
    rel = file_path.relative_to(PROJECT_ROOT).as_posix()
    result = subprocess.run(
        ["lake", "env", "lean", rel],
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
        timeout=300,
    )
    sorry_count = count_sorrys(file_path)
    build_ok = result.returncode == 0
    qualified = build_ok and sorry_count == 0
    err = _snippet((result.stderr or "") + ("\n" + result.stdout if result.stdout else ""))
    return AlgorithmBuildStatus(
        algorithm=file_path.stem,
        file=rel,
        build_ok=build_ok,
        sorry_count=sorry_count,
        qualified=qualified,
        returncode=result.returncode,
        error_snippet=err,
    )


def verify_algorithms() -> tuple[list[AlgorithmBuildStatus], str | None]:
    ok, preflight_err = _preflight_lake_config()
    if not ok:
        return [], preflight_err

    statuses = [_check_file(p) for p in _discover_algorithm_files()]
    return statuses, None


def _print_human(statuses: list[AlgorithmBuildStatus]) -> None:
    total = len(statuses)
    qualified = [s for s in statuses if s.qualified]
    unqualified = [s for s in statuses if not s.qualified]

    print(f"Algorithms scanned: {total}")
    print(f"Qualified (build_ok && sorry=0): {len(qualified)}")
    print(f"Unqualified: {len(unqualified)}")
    print()

    if qualified:
        print("Qualified algorithms:")
        for s in qualified:
            print(f"  - {s.algorithm} ({s.file})")
        print()

    if unqualified:
        print("Unqualified algorithms:")
        for s in unqualified:
            print(
                f"  - {s.algorithm}: build_ok={s.build_ok}, "
                f"sorry_count={s.sorry_count}, returncode={s.returncode}"
            )
            if s.error_snippet:
                print("    error:")
                for line in s.error_snippet.splitlines():
                    print(f"      {line}")


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Verify which Algorithms/*.lean files are build-successful "
            "(build_ok && sorry_count=0)."
        )
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Print machine-readable JSON output.",
    )
    parser.add_argument(
        "--fail-on-unqualified",
        action="store_true",
        help="Exit non-zero if any algorithm is unqualified.",
    )
    args = parser.parse_args()

    statuses, preflight_err = verify_algorithms()
    if preflight_err is not None:
        if args.json:
            print(
                json.dumps(
                    {
                        "preflight_ok": False,
                        "preflight_error": preflight_err,
                        "results": [],
                    },
                    ensure_ascii=False,
                    indent=2,
                )
            )
        else:
            print("Preflight failed: lake configuration is invalid.")
            print(preflight_err)
        sys.exit(2)

    if args.json:
        print(
            json.dumps(
                {
                    "preflight_ok": True,
                    "results": [asdict(s) for s in statuses],
                },
                ensure_ascii=False,
                indent=2,
            )
        )
    else:
        _print_human(statuses)

    any_unqualified = any(not s.qualified for s in statuses)
    if args.fail_on_unqualified and any_unqualified:
        sys.exit(1)
    sys.exit(0)


if __name__ == "__main__":
    main()
