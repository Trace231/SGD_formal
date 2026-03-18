"""APOLLO verifier adapter for orchestrator-compatible verification results."""

from __future__ import annotations

import sys
import traceback
from pathlib import Path
from typing import Any

from orchestrator.repl_adapter import verify_with_repl
from orchestrator.config import PROJECT_ROOT


def _format_apollo_message(msg: dict[str, Any], target_rel: str) -> str:
    """Convert APOLLO Lean message objects to stable single-line diagnostics."""
    pos = msg.get("pos") or {}
    line = int(pos.get("line", 0) or 0)
    col = int(pos.get("column", 0) or 0)
    data = str(msg.get("data", "")).strip()
    severity = str(msg.get("severity", "error") or "error").lower()
    level = "warning" if severity == "warning" else "info" if severity == "info" else "error"
    prefix = f"{target_rel}:" if target_rel else ""
    if line > 0 and col > 0:
        return f"{prefix}{line}:{col}: {level}: {data}"
    if line > 0:
        return f"{prefix}{line}: {level}: {data}"
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


def _count_sorry_declarations(warnings_raw: list[Any]) -> int:
    return sum(
        1
        for warning in warnings_raw
        if isinstance(warning, dict)
        and "declaration uses 'sorry'" in str(warning.get("data", ""))
    )


def _validate_repl_binding(*, project_root: Path, repl_workspace: Path) -> None:
    execution_root = Path(project_root).resolve()
    workspace = Path(repl_workspace).resolve()
    if not execution_root.exists():
        raise RuntimeError(f"repl_project_root_missing: {execution_root}")
    if not (
        (execution_root / "lakefile.lean").exists()
        or (execution_root / "lakefile.toml").exists()
    ):
        raise RuntimeError(
            f"repl_project_root_invalid: missing lakefile in {execution_root}"
        )
    if not workspace.exists():
        raise RuntimeError(f"repl_workspace_missing: {workspace}")
    repl_binary = workspace / ".lake" / "build" / "bin" / "repl"
    if not repl_binary.exists():
        raise RuntimeError(
            f"repl_binary_missing: {repl_binary} "
            f"(build the REPL workspace at {workspace})"
        )


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

    if errors_raw and isinstance(errors_raw[0], str):
        errors = [str(m).strip() for m in errors_raw if str(m).strip()]
    else:
        errors = [_format_apollo_message(m, target_rel) for m in errors_raw if isinstance(m, dict)]
    if warnings_raw and isinstance(warnings_raw[0], str):
        warnings = [str(m).strip() for m in warnings_raw if str(m).strip()]
    else:
        warnings = [_format_apollo_message(m, target_rel) for m in warnings_raw if isinstance(m, dict)]
    sorry_count = len(sorries)
    # Keep sorry accounting compatible with current consumers:
    # "sorry_declarations" ~= compiler-observed sorry declarations.
    sorry_declarations = _count_sorry_declarations(warnings_raw)
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
        "verify_backend_used": str(apollo_result.get("backend_used", "apollo_python")),
        "verify_backend_reason": str(apollo_result.get("backend_reason", "apollo_python_success")),
    }


def verify_with_apollo(
    *,
    code: str,
    timeout: int,
    apollo_project_path: Path,
    repl_workspace: Path,
    lake_path: str,
    project_root: Path = PROJECT_ROOT,
) -> dict[str, Any]:
    """Run APOLLO verification with REPL-first routing.

    Route order:
    1) Native REPL adapter (preferred, no APOLLO Python dependency)
    2) APOLLO Python verifier fallback
    """
    apollo_root = Path(apollo_project_path).resolve()
    workspace = Path(repl_workspace).resolve()
    execution_root = Path(project_root).resolve()
    _validate_repl_binding(project_root=execution_root, repl_workspace=workspace)

    # Path A: native REPL adapter
    repl_error: Exception | None = None
    try:
        return verify_with_repl(
            code=code,
            timeout=timeout,
            repl_workspace=workspace,
            project_root=execution_root,
            lake_path=lake_path,
        )
    except Exception as exc:  # noqa: BLE001
        repl_error = exc

    # Path B: APOLLO Python verifier fallback
    if not apollo_root.exists():
        raise RuntimeError(
            "apollo_import_error: APOLLO project path does not exist "
            f"({apollo_root}); prior_repl_error={repl_error}"
        ) from repl_error

    # Add APOLLO root to sys.path lazily so default lake flow has no import side effects.
    apollo_root_str = str(apollo_root)
    if apollo_root_str not in sys.path:
        sys.path.insert(0, apollo_root_str)

    try:
        from prover.lean.verifier import verify_lean4_file
    except Exception as exc:  # pragma: no cover - import failures are environment-specific
        raise RuntimeError(
            "apollo_import_error: failed to import APOLLO verifier. "
            f"APOLLO root: {apollo_root}. Error: {exc}; prior_repl_error={repl_error}"
        ) from exc

    try:
        out = verify_lean4_file(
            code=code,
            timeout=timeout,
            lean_workspace=str(workspace),
            lake_path=lake_path,
            repl_binary_path=str(workspace / ".lake" / "build" / "bin" / "repl"),
            execution_root=str(execution_root),
        )
        if isinstance(out, dict):
            out.setdefault("backend_used", "apollo_python")
            out.setdefault("backend_reason", "apollo_python_success")
        return out
    except Exception as exc:
        # Bubble up with traceback in message so callers can surface actionable diagnostics.
        raise RuntimeError(
            "apollo_runtime_error: APOLLO verification failed: "
            f"{exc}; prior_repl_error={repl_error}\n{traceback.format_exc(limit=2)}"
        ) from exc

