"""Compile-health checks and soft recovery loop for Phase 3."""

from __future__ import annotations

import re
from typing import Any

from rich.console import Console

from orchestrator.audit_logger import AuditLogger
from orchestrator.config import COMPILE_HEALTH_ENABLED, COMPILE_HEALTH_MAX_RETRIES

console = Console()

_INFRA_PATTERNS = (
    re.compile(r"object file .* does not exist", re.IGNORECASE),
    re.compile(r"module .* does not exist", re.IGNORECASE),
    re.compile(r"unknown package", re.IGNORECASE),
    re.compile(r"imports? .* not found", re.IGNORECASE),
)


def _coerce_errors_text(errors: Any) -> str:
    if isinstance(errors, list):
        return "\n".join(str(x) for x in errors if str(x).strip())
    if errors is None:
        return ""
    return str(errors)


def _has_infra_error(errors_text: str) -> bool:
    hay = str(errors_text or "")
    return any(p.search(hay) for p in _INFRA_PATTERNS)


def check_compile_health(
    verify_result: dict[str, Any],
    *,
    target_file: str,
) -> dict[str, Any]:
    """Summarize whether the current verify result indicates healthy proof conditions."""
    errors_text = _coerce_errors_text(verify_result.get("errors", ""))
    backend_used = str(verify_result.get("verify_backend_used", ""))
    backend_reason = str(verify_result.get("verify_backend_reason", ""))
    missing_target = backend_reason == "missing_target"
    infra_error = _has_infra_error(errors_text)
    backend_unhealthy = (
        backend_reason.startswith("strict_failure:")
        or backend_reason.startswith("backend_failure:")
        or backend_reason == "missing_target"
    )
    import_resolves = not infra_error and not missing_target
    olean_available = not bool(re.search(r"object file .* does not exist", errors_text, re.IGNORECASE))
    verify_backend_healthy = not backend_unhealthy
    healthy = import_resolves and olean_available and verify_backend_healthy
    summary = {
        "enabled": bool(COMPILE_HEALTH_ENABLED),
        "healthy": healthy,
        "target_file": target_file,
        "import_resolves": import_resolves,
        "olean_available": olean_available,
        "verify_backend_healthy": verify_backend_healthy,
        "verify_backend_used": backend_used,
        "verify_backend_reason": backend_reason,
        "infra_error": infra_error,
        "missing_target": missing_target,
        "errors_text": errors_text[:4000],
    }
    AuditLogger.get().log_event("compile_health_check", **summary)
    return summary


def recover_compile_health(
    target_file: str,
    *,
    registry,
    verify_result: dict[str, Any],
    max_retries: int | None = None,
) -> dict[str, Any]:
    """Try repo-level recovery steps before theorem-level repair continues."""
    retries = max(1, int(max_retries or COMPILE_HEALTH_MAX_RETRIES))
    health = check_compile_health(verify_result, target_file=target_file)
    latest_verify = dict(verify_result)
    attempts: list[dict[str, Any]] = []
    if not COMPILE_HEALTH_ENABLED or health["healthy"]:
        return {
            "healthy_after": bool(health["healthy"]),
            "attempts": attempts,
            "verify_result": latest_verify,
            "health": health,
        }

    console.print(
        "[yellow][CompileHealth] Infra/backend issue detected. "
        "Running soft recovery before theorem repair.[/yellow]"
    )

    for attempt in range(1, retries + 1):
        repo_result = dict(registry.call("run_repo_verify"))
        latest_verify = dict(registry.call("run_lean_verify", target_file))
        health = check_compile_health(latest_verify, target_file=target_file)
        rec = {
            "attempt": attempt,
            "repo_exit_code": int(repo_result.get("exit_code", 1)),
            "file_exit_code": int(latest_verify.get("exit_code", 1)),
            "healthy_after": bool(health["healthy"]),
            "verify_backend_used": str(latest_verify.get("verify_backend_used", "")),
            "verify_backend_reason": str(latest_verify.get("verify_backend_reason", "")),
            "errors_text": _coerce_errors_text(latest_verify.get("errors", ""))[:2000],
        }
        attempts.append(rec)
        AuditLogger.get().log_event("compile_health_recovery", **rec)
        if health["healthy"]:
            console.print(
                f"[green][CompileHealth] Recovery succeeded on attempt {attempt}.[/green]"
            )
            break

    return {
        "healthy_after": bool(health["healthy"]),
        "attempts": attempts,
        "verify_result": latest_verify,
        "health": health,
    }


__all__ = ["check_compile_health", "recover_compile_health"]
