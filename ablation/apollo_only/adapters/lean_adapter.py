"""Lean verification adapter for APOLLO-only ablation on Lean 4.28."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any

from orchestrator.apollo_integration import verify_with_apollo


@dataclass(frozen=True)
class LeanVerifyConfig:
    """Runtime knobs for Lean verification."""

    timeout: int
    apollo_project_path: Path
    repl_workspace: Path
    lake_path: str
    execution_root: Path
    workspace_root: Path | None = None


def _is_within(path: Path, root: Path) -> bool:
    try:
        path.resolve().relative_to(root.resolve())
        return True
    except ValueError:
        return False


def preflight_paths(cfg: LeanVerifyConfig) -> dict[str, Any]:
    """Fail fast with actionable path diagnostics."""
    if not cfg.execution_root.exists():
        raise RuntimeError(f"execution_root_missing: {cfg.execution_root}")
    if not (
        (cfg.execution_root / "lakefile.lean").exists()
        or (cfg.execution_root / "lakefile.toml").exists()
    ):
        raise RuntimeError(
            f"execution_root_invalid: missing lakefile in {cfg.execution_root}"
        )
    if not cfg.repl_workspace.exists():
        raise RuntimeError(f"repl_workspace_missing: {cfg.repl_workspace}")
    repl_bin = cfg.repl_workspace / ".lake" / "build" / "bin" / "repl"
    if not repl_bin.exists():
        raise RuntimeError(
            f"repl_binary_missing: {repl_bin} "
            f"(build REPL workspace first)"
        )
    if not cfg.apollo_project_path.exists():
        raise RuntimeError(f"apollo_project_missing: {cfg.apollo_project_path}")

    boundary_root = cfg.workspace_root.resolve() if cfg.workspace_root is not None else cfg.execution_root.resolve()
    execution_in_workspace = _is_within(cfg.execution_root, boundary_root)
    if not execution_in_workspace:
        raise RuntimeError(
            "execution_root_outside_workspace: "
            f"{cfg.execution_root} not under {boundary_root}"
        )
    return {
        "execution_root": str(cfg.execution_root.resolve()),
        "repl_workspace": str(cfg.repl_workspace.resolve()),
        "apollo_project_path": str(cfg.apollo_project_path.resolve()),
        "workspace_root": str(boundary_root),
        "execution_in_workspace": execution_in_workspace,
    }


def _to_text_messages(messages: Any) -> list[str]:
    out: list[str] = []
    if not isinstance(messages, list):
        return out
    for item in messages:
        if isinstance(item, str):
            text = item.strip()
            if text:
                out.append(text)
            continue
        if isinstance(item, dict):
            data = str(item.get("data", "")).strip()
            pos = item.get("pos") or {}
            line = int(pos.get("line", 0) or 0)
            col = int(pos.get("column", 0) or 0)
            if data and line > 0 and col > 0:
                out.append(f"{line}:{col}: {data}")
            elif data and line > 0:
                out.append(f"{line}: {data}")
            elif data:
                out.append(data)
    return out


def normalize_verify_result(
    raw: dict[str, Any],
    *,
    target_path: str = "",
    execution_root: str = "",
    workspace_root: str = "",
    isolation_check_passed: bool = False,
    preflight: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Normalize APOLLO or REPL verifier output into a single schema."""
    errors_text = raw.get("errors_text")
    warnings_text = raw.get("warnings_text")
    if not isinstance(errors_text, list):
        errors_text = _to_text_messages(raw.get("errors", []))
    if not isinstance(warnings_text, list):
        warnings_text = _to_text_messages(raw.get("warnings", []))

    sorries = raw.get("sorries", [])
    if not isinstance(sorries, list):
        sorries = []

    complete = bool(raw.get("complete", False))
    passed = bool(raw.get("pass", False))
    verify_time = float(raw.get("verify_time", 0.0) or 0.0)
    source_sorry_count = int(raw.get("source_sorry_count", len(sorries)) or len(sorries))

    return {
        "pass": passed,
        "complete": complete,
        "errors": errors_text,
        "warnings": warnings_text,
        "error_count": len(errors_text),
        "warning_count": len(warnings_text),
        "sorry_count": source_sorry_count,
        "sorries": sorries,
        "verify_time": verify_time,
        "verify_backend_used": str(raw.get("backend_used", "apollo_verify")),
        "verify_backend_reason": str(raw.get("backend_reason", "")),
        "blocked_sorry_count": int(raw.get("blocked_sorry_count", 0) or 0),
        "sorry_declarations": int(raw.get("sorry_declarations", 0) or 0),
        "target": target_path,
        "execution_root": execution_root,
        "workspace_root": workspace_root,
        "isolation_check_passed": bool(isolation_check_passed),
        "preflight": preflight or {},
    }


def verify_code(
    code: str,
    cfg: LeanVerifyConfig,
    *,
    target_path: Path | None = None,
) -> dict[str, Any]:
    """Verify Lean code through APOLLO adapter, then normalize output."""
    preflight = preflight_paths(cfg)
    workspace_root = cfg.workspace_root.resolve() if cfg.workspace_root is not None else cfg.execution_root.resolve()
    raw = verify_with_apollo(
        code=code,
        timeout=cfg.timeout,
        apollo_project_path=cfg.apollo_project_path,
        repl_workspace=cfg.repl_workspace,
        lake_path=cfg.lake_path,
        project_root=cfg.execution_root,
    )
    return normalize_verify_result(
        raw,
        target_path=str(target_path.resolve()) if target_path is not None else "",
        execution_root=str(cfg.execution_root.resolve()),
        workspace_root=str(workspace_root),
        isolation_check_passed=bool(preflight.get("execution_in_workspace", False)),
        preflight=preflight,
    )

