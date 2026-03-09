"""Structured audit logging for orchestrator runs.

Records agent calls, tool invocations, prompt hashes, and run outcomes
to JSON audit files for monitoring and debugging.
"""

from __future__ import annotations

import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from orchestrator.config import AUDIT_DIR, AUDIT_ENABLED, DOCS_DIR, PROJECT_ROOT


def _compute_prompt_hashes() -> dict[str, str]:
    """Compute SHA256 hashes of prompts.py and META_PROMPTS.md."""
    hashes: dict[str, str] = {}
    prompts_py = PROJECT_ROOT / "orchestrator" / "prompts.py"
    meta_prompts = DOCS_DIR / "META_PROMPTS.md"
    for name, path in [("prompts_py", prompts_py), ("meta_prompts_md", meta_prompts)]:
        if path.exists():
            content = path.read_text(encoding="utf-8")
            digest = hashlib.sha256(content.encode("utf-8")).hexdigest()
            hashes[name] = f"sha256:{digest[:16]}..."
        else:
            hashes[name] = "missing"
    return hashes


class AuditLogger:
    """Singleton audit logger for a single orchestrator run."""

    _instance: AuditLogger | None = None

    def __init__(self) -> None:
        self.enabled = AUDIT_ENABLED
        self.audit_dir = Path(AUDIT_DIR)
        self.run_id: str = ""
        self.algorithm: str = ""
        self.started_at: str = ""
        self.prompt_hashes: dict[str, str] = {}
        self.events: list[dict[str, Any]] = []
        self._current_phase: int = 0
        self._phase3_execution_history: list[dict[str, Any]] = []
        self._phase3_attempt_failures: list[dict[str, Any]] = []
        self._phase4_patch_ops_summary: list[dict[str, Any]] = []

    @classmethod
    def get(cls) -> AuditLogger:
        if cls._instance is None:
            cls._instance = cls()
        return cls._instance

    @classmethod
    def reset(cls) -> None:
        """Reset for a new run (called by start_run)."""
        cls._instance = cls()

    def set_phase(self, phase: int) -> None:
        """Set current phase for subsequent events (1-5)."""
        self._current_phase = phase

    def start_run(self, algorithm: str) -> str:
        """Begin a new run, compute prompt hashes, return run_id."""
        AuditLogger.reset()
        self.enabled = AUDIT_ENABLED
        self.audit_dir = Path(AUDIT_DIR)
        self.algorithm = algorithm
        self.started_at = datetime.now(timezone.utc).isoformat(timespec="seconds")
        ts = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
        self.run_id = f"{ts}_{algorithm}"
        self.prompt_hashes = _compute_prompt_hashes()
        self.events = []
        self._current_phase = 0
        self._phase3_execution_history = []
        self._phase3_attempt_failures = []
        self._phase4_patch_ops_summary = []

        if self.enabled:
            self.events.append({
                "type": "run_start",
                "algorithm": algorithm,
                "prompt_hashes": self.prompt_hashes,
                "ts": self.started_at,
            })
        return self.run_id

    def log_agent_call(
        self,
        role: str,
        user_msg: str,
        reply: str,
    ) -> None:
        """Log an agent call (prompt + reply metadata)."""
        if not self.enabled:
            return
        preview_len = 200
        self.events.append({
            "type": "agent_call",
            "phase": self._current_phase,
            "role": role,
            "prompt_len": len(user_msg),
            "prompt_preview": user_msg[:preview_len] + ("..." if len(user_msg) > preview_len else ""),
            "reply_len": len(reply),
            "ts": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        })

    def log_tool_call(
        self,
        tool_name: str,
        arguments: dict[str, Any],
        result: Any,
    ) -> None:
        """Log a tool invocation with path and changed/created from result."""
        if not self.enabled:
            return
        path = arguments.get("path") or arguments.get("file_path") or "?"
        changed: bool | None = None
        created: bool | None = None
        if isinstance(result, dict):
            changed = result.get("changed")
            created = result.get("created")
        evt: dict[str, Any] = {
            "type": "tool_call",
            "phase": self._current_phase,
            "tool": tool_name,
            "path": str(path),
            "ts": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        }
        if changed is not None:
            evt["changed"] = changed
        if created is not None:
            evt["created"] = created
        self.events.append(evt)

    def add_phase3_data(
        self,
        execution_history: list[dict[str, Any]],
        attempt_failures: list[dict[str, Any]] | None = None,
    ) -> None:
        """Append Phase 3 execution history and attempt failures (Lean errors)."""
        self._phase3_execution_history = execution_history
        self._phase3_attempt_failures = attempt_failures or []

    def add_phase4_data(self, patch_ops_summary: list[dict[str, Any]]) -> None:
        """Append Phase 4 patch ops summary."""
        self._phase4_patch_ops_summary = patch_ops_summary

    def finish_run(
        self,
        success: bool,
        files_modified: list[str],
    ) -> None:
        """Write full audit JSON and optionally reset."""
        if not self.enabled:
            return
        finished_at = datetime.now(timezone.utc).isoformat(timespec="seconds")
        self.events.append({
            "type": "run_end",
            "success": success,
            "ts": finished_at,
        })

        payload: dict[str, Any] = {
            "run_id": self.run_id,
            "algorithm": self.algorithm,
            "started_at": self.started_at,
            "finished_at": finished_at,
            "success": success,
            "prompt_hashes": self.prompt_hashes,
            "events": self.events,
            "phase3_execution_history": self._phase3_execution_history,
            "phase3_attempt_failures": self._phase3_attempt_failures,
            "phase4_patch_ops_summary": self._phase4_patch_ops_summary,
            "files_modified": files_modified,
        }

        self.audit_dir.mkdir(parents=True, exist_ok=True)
        audit_path = self.audit_dir / f"audit_{self.run_id}.json"
        audit_path.write_text(
            json.dumps(payload, indent=2, ensure_ascii=False),
            encoding="utf-8",
        )
