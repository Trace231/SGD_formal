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

from orchestrator.config import (
    AUDIT_CODE_PATCH_ENABLED,
    AUDIT_DIR,
    AUDIT_ENABLED,
    AUDIT_FULL_PROMPTS_ENABLED,
    DOCS_DIR,
    PROJECT_ROOT,
)


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
        self.full_prompts_enabled = AUDIT_FULL_PROMPTS_ENABLED
        self.code_patch_enabled = AUDIT_CODE_PATCH_ENABLED
        self.audit_dir = Path(AUDIT_DIR)
        self.run_id: str = ""
        self.algorithm: str = ""
        self.started_at: str = ""
        self.prompt_hashes: dict[str, str] = {}
        self.events: list[dict[str, Any]] = []
        self._next_event_id: int = 1
        self._current_phase: int = 0
        self._phase3_execution_history: list[dict[str, Any]] = []
        self._phase3_attempt_failures: list[dict[str, Any]] = []
        self._phase3_extra: dict[str, Any] = {}
        self._phase4_patch_ops_summary: list[dict[str, Any]] = []
        self._phase1_detail: dict[str, Any] | None = None
        self._phase2_rounds: list[dict[str, Any]] = []

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
        self.enabled = AUDIT_ENABLED
        self.audit_dir = Path(AUDIT_DIR)
        self.algorithm = algorithm
        self.started_at = datetime.now(timezone.utc).isoformat(timespec="seconds")
        ts = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
        self.run_id = f"{ts}_{algorithm}"
        self.prompt_hashes = _compute_prompt_hashes()
        self.events = []
        self._next_event_id = 1
        self._current_phase = 0
        self._phase3_execution_history = []
        self._phase3_attempt_failures = []
        self._phase3_extra = {}
        self._phase4_patch_ops_summary = []
        self._phase1_detail = None
        self._phase2_rounds = []

        if self.enabled:
            self.events.append({
                "id": self._next_event_id,
                "type": "run_start",
                "algorithm": algorithm,
                "prompt_hashes": self.prompt_hashes,
                "ts": self.started_at,
            })
            self._next_event_id += 1
        return self.run_id

    def log_agent_call(
        self,
        role: str,
        user_msg: str,
        reply: str,
        prompt_full: str | None = None,
        reply_full: str | None = None,
    ) -> None:
        """Log an agent call (prompt + reply metadata)."""
        if not self.enabled:
            return
        preview_len = 200
        event: dict[str, Any] = {
            "id": self._next_event_id,
            "type": "agent_call",
            "phase": self._current_phase,
            "role": role,
            "prompt_len": len(user_msg),
            "prompt_preview": user_msg[:preview_len] + ("..." if len(user_msg) > preview_len else ""),
            "reply_len": len(reply),
            "ts": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        }

        if self.full_prompts_enabled:
            # Guard against unbounded growth; mark when truncated.
            max_chars = 50000
            if prompt_full is not None:
                if len(prompt_full) > max_chars:
                    event["prompt_full"] = prompt_full[:max_chars]
                    event.setdefault("truncated", {})["prompt_full"] = True
                else:
                    event["prompt_full"] = prompt_full
            if reply_full is not None:
                if len(reply_full) > max_chars:
                    event["reply_full"] = reply_full[:max_chars]
                    event.setdefault("truncated", {})["reply_full"] = True
                else:
                    event["reply_full"] = reply_full

        self.events.append(event)
        self._next_event_id += 1

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
        before: str | None = None
        after: str | None = None
        if isinstance(result, dict):
            changed = result.get("changed")
            created = result.get("created")
            before = result.get("before")
            after = result.get("after")
        evt: dict[str, Any] = {
            "id": self._next_event_id,
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
        if self.code_patch_enabled and (before is not None or after is not None):
            # Store snapshots with length guards to avoid pathological growth.
            max_chars = 100000
            if before is not None:
                if len(before) > max_chars:
                    evt["before"] = before[:max_chars]
                    evt.setdefault("truncated", {})["before"] = True
                else:
                    evt["before"] = before
            if after is not None:
                if len(after) > max_chars:
                    evt["after"] = after[:max_chars]
                    evt.setdefault("truncated", {})["after"] = True
                else:
                    evt["after"] = after
        self.events.append(evt)
        self._next_event_id += 1

    def log_phase1_detail(self, prompt_full: str, reply_full: str) -> None:
        """Log Phase 1 full prompt and generated Prover prompt."""
        if not self.enabled:
            return
        self._phase1_detail = {
            "prompt_full": prompt_full,
            "reply_full": reply_full,
            "ts": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        }

    def log_phase2_round(
        self,
        round_num: int,
        agent2_plan: str,
        agent1_prompt: str,
        agent1_review: str,
        decision: str,
        feedback: str,
    ) -> None:
        """Log one Phase 2 review round: Agent2 plan, Agent1 prompt and review."""
        if not self.enabled:
            return
        self._phase2_rounds.append({
            "round": round_num,
            "agent2_plan": agent2_plan,
            "agent1_prompt": agent1_prompt,
            "agent1_review": agent1_review,
            "decision": decision,
            "feedback": feedback,
            "ts": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        })

    def add_phase3_data(
        self,
        execution_history: list[dict[str, Any]],
        attempt_failures: list[dict[str, Any]] | None = None,
        extra: dict[str, Any] | None = None,
    ) -> None:
        """Append Phase 3 execution history and attempt failures (Lean errors)."""
        self._phase3_execution_history = execution_history
        self._phase3_attempt_failures = attempt_failures or []
        self._phase3_extra = extra or {}

    def add_phase4_data(self, patch_ops_summary: list[dict[str, Any]]) -> None:
        """Append Phase 4 patch ops summary."""
        self._phase4_patch_ops_summary = patch_ops_summary

    def finish_run(
        self,
        success: bool,
        files_modified: list[str],
        extra_files_to_snapshot: list[str] | None = None,
    ) -> None:
        """Write full audit JSON and optionally reset.

        When success is False and files_modified is empty, extra_files_to_snapshot
        (e.g. target algorithm file) is still snapshotted for auditability.
        """
        if not self.enabled:
            return
        finished_at = datetime.now(timezone.utc).isoformat(timespec="seconds")
        self.events.append({
            "id": self._next_event_id,
            "type": "run_end",
            "success": success,
            "ts": finished_at,
        })
        self._next_event_id += 1

        final_files: dict[str, dict[str, Any]] = {}
        paths_to_snapshot = list(files_modified) if files_modified else []
        if not paths_to_snapshot and extra_files_to_snapshot:
            paths_to_snapshot = list(extra_files_to_snapshot)
        if self.code_patch_enabled and paths_to_snapshot:
            # Capture final Lean file snapshots with hashes for strong auditability.
            for rel_path in paths_to_snapshot:
                try:
                    absolute = PROJECT_ROOT / rel_path
                    if not absolute.exists():
                        continue
                    content = absolute.read_text(encoding="utf-8")
                    digest = hashlib.sha256(content.encode("utf-8")).hexdigest()
                    final_files[rel_path] = {
                        "hash": f"sha256:{digest}",
                        "size_bytes": len(content.encode("utf-8")),
                        "content": content,
                    }
                except OSError:
                    # Snapshot is best-effort; missing entries do not fail the run.
                    continue

        payload: dict[str, Any] = {
            "run_id": self.run_id,
            "algorithm": self.algorithm,
            "started_at": self.started_at,
            "finished_at": finished_at,
            "success": success,
            "prompt_hashes": self.prompt_hashes,
            "events": self.events,
            "phase1_detail": self._phase1_detail,
            "phase2_rounds": self._phase2_rounds,
            "phase3_execution_history": self._phase3_execution_history,
            "phase3_attempt_failures": self._phase3_attempt_failures,
            "phase4_patch_ops_summary": self._phase4_patch_ops_summary,
            "files_modified": files_modified,
        }
        if self._phase3_extra:
            payload.update(self._phase3_extra)
        if final_files:
            payload["final_files"] = final_files

        self.audit_dir.mkdir(parents=True, exist_ok=True)
        audit_path = self.audit_dir / f"audit_{self.run_id}.json"
        audit_path.write_text(
            json.dumps(payload, indent=2, ensure_ascii=False),
            encoding="utf-8",
        )
