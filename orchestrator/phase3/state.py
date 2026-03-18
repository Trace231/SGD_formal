"""State objects for Phase3 proof orchestration.

These dataclasses are a structure-only refactor: they consolidate runtime and
attempt-level state previously spread across many local variables.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any

from orchestrator.agents import Agent, ToolRegistry


@dataclass
class Phase3Progress:
    """Optional rich-progress wiring used by phase3_prove."""

    rich_progress: Any | None = None
    rich_task: Any | None = None

    def update(self, desc: str) -> None:
        if self.rich_progress is not None and self.rich_task is not None:
            self.rich_progress.update(self.rich_task, description=desc)

    def advance(self) -> None:
        if self.rich_progress is not None and self.rich_task is not None:
            self.rich_progress.advance(self.rich_task)


@dataclass
class Phase3Runtime:
    """Long-lived runtime objects for phase3 orchestration."""

    agent2: Agent
    agent3: Agent
    agent6: Agent
    agent7: Agent
    registry: ToolRegistry
    readonly_registry: ToolRegistry
    escalation_registry: ToolRegistry
    agent6_registry: ToolRegistry
    agent7_registry: ToolRegistry
    progress: Phase3Progress = field(default_factory=Phase3Progress)


@dataclass
class Phase3State:
    """Aggregated mutable state used across attempts and routing loops."""

    last_errors: str = ""
    last_sorry_count: int = 0
    attempts: int = 0
    execution_history: list[Any] = field(default_factory=list)
    decision_history: list[dict] = field(default_factory=list)
    attempt_failures: list[dict] = field(default_factory=list)
    agent3_turns: list[dict] = field(default_factory=list)
    blocker_reports: list[dict] = field(default_factory=list)
    diag_log: list[str] = field(default_factory=list)

    # Agent7 telemetry
    agent7_invocations: list[dict] = field(default_factory=list)
    agent7_step_execution_log: list[dict] = field(default_factory=list)
    agent7_plan_revisions: list[dict] = field(default_factory=list)
    agent7_blocked_actions: list[dict] = field(default_factory=list)
    agent7_forced_trigger_count: int = 0
    agent7_force_gate_entries: list[dict] = field(default_factory=list)
    agent7_force_gate_rejections: list[dict] = field(default_factory=list)
    agent7_force_gate_reason_samples: list[str] = field(default_factory=list)
    pending_agent7_plan: dict | None = None

    # Retry / error trackers
    last_error_sig: str | None = None
    consecutive_repeat_count: int = 0
    dep_error_streak: int = 0
    last_dep_error_sig: str | None = None
    assumption_patch_tried: set[str] = field(default_factory=set)
    failed_approaches: list[dict] = field(default_factory=list)
    failure_ledger: list[dict] = field(default_factory=list)
    goal_cache: dict[tuple[str, int, str], dict] = field(default_factory=dict)

    # File/checkpoint state
    initial_hash: str | None = None
    file_changed: bool = False
    initial_sorry_for_ckpt: int = 999
    best_checkpoint: dict = field(
        default_factory=lambda: {"sorry_count": 999, "content": None}
    )

    # misc
    token_char_budget: int = 0
    last_audit_flush_time: float = 0.0
    last_printed_err_sig: str | None = None

