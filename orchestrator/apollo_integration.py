"""APOLLO verifier adapter for orchestrator-compatible verification results."""

from __future__ import annotations

import sys
import traceback
from pathlib import Path
from typing import Any


def _format_apollo_message(msg: dict[str, Any]) -> str:
    """Convert APOLLO Lean message objects to stable single-line diagnostics."""
    pos = msg.get("pos") or {}
    line = int(pos.get("line", 0) or 0)
    col = int(pos.get("column", 0) or 0)
    data = str(msg.get("data", "")).strip()
    if line > 0 and col > 0:
        return f"{line}:{col}: {data}"
    if line > 0:
        return f"{line}: {data}"
    return data


def _count_source_sorrys(source_text: str) -> int:
    """Count sorry/admit placeholders in source code only."""
    import re

    block_comment_re = re.compile(r"/-.*?-/", re.DOTALL)
    sorry_re = re.compile(r"\bsorry\b")
    admit_re = re.compile(r"\badmit\b")
    stripped = block_comment_re.sub("", source_text)
    count = 0
    for line in stripped.splitlines():
        code = line.split("--")[0]
        count += len(sorry_re.findall(code))
        count += len(admit_re.findall(code))
    return count


def normalize_apollo_result(
    *,
    target_rel: str,
    source_text: str,
    apollo_result: dict[str, Any],
) -> dict[str, Any]:
    """Map APOLLO verifier output into the existing run_lean_verify schema."""
    errors_raw = apollo_result.get("errors", []) or []
    warnings_raw = apollo_result.get("warnings", []) or []
    sorries = apollo_result.get("sorries", []) or []

    errors = [
        _format_apollo_message(m) for m in errors_raw if isinstance(m, dict)
    ]
    warnings = [
        _format_apollo_message(m) for m in warnings_raw if isinstance(m, dict)
    ]
    sorry_count = len(sorries)
    # Keep sorry accounting compatible with current consumers:
    # "sorry_declarations" ~= compiler-observed sorry declarations.
    sorry_declarations = sorry_count
    source_sorry_count = _count_source_sorrys(source_text)
    blocked_sorry_count = max(0, source_sorry_count - sorry_declarations)

    passed = bool(apollo_result.get("pass", False))
    complete = bool(apollo_result.get("complete", False))
    exit_code = 0 if passed else 1

    return {
        "target": target_rel,
        "success": complete,
        "exit_code": exit_code,
        "sorry_count": source_sorry_count,
        "sorry_declarations": sorry_declarations,
        "blocked_sorry_count": blocked_sorry_count,
        "error_count": len(errors),
        "errors": errors,
        "warnings": warnings,
        "verify_time": float(apollo_result.get("verify_time", 0.0) or 0.0),
    }


def verify_with_apollo(
    *,
    code: str,
    timeout: int,
    apollo_project_path: Path,
    repl_workspace: Path,
    lake_path: str,
) -> dict[str, Any]:
    """Run APOLLO's verify_lean4_file with explicit environment wiring."""
    apollo_root = Path(apollo_project_path).resolve()
    workspace = Path(repl_workspace).resolve()
    if not apollo_root.exists():
        raise RuntimeError(f"APOLLO project path does not exist: {apollo_root}")
    if not workspace.exists():
        raise RuntimeError(f"APOLLO repl workspace does not exist: {workspace}")

    # Add APOLLO root to sys.path lazily so default lake flow has no import side effects.
    apollo_root_str = str(apollo_root)
    if apollo_root_str not in sys.path:
        sys.path.insert(0, apollo_root_str)

    try:
        from prover.lean.verifier import verify_lean4_file
    except Exception as exc:  # pragma: no cover - import failures are environment-specific
        raise RuntimeError(
            "Failed to import APOLLO verifier. "
            f"APOLLO root: {apollo_root}. Error: {exc}"
        ) from exc

    try:
        return verify_lean4_file(
            code=code,
            timeout=timeout,
            lean_workspace=str(workspace),
            lake_path=lake_path,
        )
    except Exception as exc:
        # Bubble up with traceback in message so callers can surface actionable diagnostics.
        raise RuntimeError(
            "APOLLO verification failed: "
            f"{exc}\n{traceback.format_exc(limit=2)}"
        ) from exc

