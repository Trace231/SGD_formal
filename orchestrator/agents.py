"""Agent abstraction and shared utilities for orchestration."""

from __future__ import annotations

from typing import Any, Callable

from rich.console import Console
from rich.panel import Panel

from orchestrator.config import (
    AGENT_CONFIGS,
    MAX_TOKENS,
)
from orchestrator.file_io import load_files
from orchestrator.prompts import AGENT_FILES, SYSTEM_PROMPTS
from orchestrator.providers import call_llm

console = Console()


# ---------------------------------------------------------------------------
# Tool registry — controlled mapping for agent tool calls
# ---------------------------------------------------------------------------

class ToolRegistry:
    """Registry for orchestrator tool callables.

    This keeps tool exposure explicit and centralized.
    """

    def __init__(self) -> None:
        self._tools: dict[str, Callable[..., Any]] = {}

    def register(self, name: str, fn: Callable[..., Any]) -> None:
        """Register a tool callable under *name*."""
        if not name.strip():
            raise ValueError("Tool name must be non-empty")
        self._tools[name] = fn

    def register_default_tools(self) -> None:
        """Register built-in controlled tools."""
        from orchestrator.tools import (
            apply_doc_patch,
            edit_file_patch,
            overwrite_file,
            read_file,
            run_lean_verify,
            run_repo_verify,
            search_in_file,
            write_new_file,
        )

        self.register("read_file", read_file)
        self.register("search_in_file", search_in_file)
        self.register("write_new_file", write_new_file)
        self.register("overwrite_file", overwrite_file)
        self.register("edit_file_patch", edit_file_patch)
        self.register("run_lean_verify", run_lean_verify)
        self.register("run_repo_verify", run_repo_verify)
        self.register("apply_doc_patch", apply_doc_patch)

    def call(self, name: str, *args: Any, **kwargs: Any) -> Any:
        """Invoke a registered tool by name."""
        if name not in self._tools:
            known = ", ".join(sorted(self._tools)) or "<none>"
            raise KeyError(f"Unknown tool: {name}. Registered: {known}")
        result = self._tools[name](*args, **kwargs)
        try:
            from orchestrator.audit_logger import AuditLogger
            AuditLogger.get().log_tool_call(name, kwargs, result)
        except Exception:  # noqa: BLE001
            pass  # audit must not break tool execution
        return result

    def list_tools(self) -> list[str]:
        """Return all registered tool names."""
        return sorted(self._tools.keys())


# ---------------------------------------------------------------------------
# Agent class — wraps a role, provider config, and conversation history
# ---------------------------------------------------------------------------

class Agent:
    """A stateful LLM agent with a fixed role and multi-turn memory."""

    def __init__(self, role: str, extra_files: list[str] | None = None):
        cfg = AGENT_CONFIGS[role]
        self.role = role
        self.provider = cfg["provider"]
        self.model = cfg["model"]
        self.max_tokens: int = cfg.get("max_tokens", MAX_TOKENS)
        self.system = SYSTEM_PROMPTS[role]
        self.messages: list[dict[str, str]] = []

        files = list(AGENT_FILES.get(role, []))
        if extra_files:
            files.extend(extra_files)
        self._file_context = load_files(files) if files else ""

    def call(self, user_msg: str) -> str:
        """Send *user_msg* (prepended with file context on the first call)
        and return the assistant reply.  Conversation history is accumulated.
        """
        if not self.messages and self._file_context:
            full_msg = f"{self._file_context}\n\n{user_msg}"
        else:
            full_msg = user_msg

        self.messages.append({"role": "user", "content": full_msg})

        reply = call_llm(
            provider=self.provider,
            model=self.model,
            system=self.system,
            messages=self.messages,
            max_tokens=self.max_tokens,
        )
        self.messages.append({"role": "assistant", "content": reply})
        try:
            from orchestrator.audit_logger import AuditLogger
            AuditLogger.get().log_agent_call(
                self.role,
                full_msg,
                reply,
                prompt_full=full_msg,
                reply_full=reply,
            )
        except Exception:  # noqa: BLE001
            pass  # audit must not break agent execution
        return reply

    def reset(self) -> None:
        """Clear conversation history (keeps system prompt and files)."""
        self.messages.clear()


# ---------------------------------------------------------------------------
# Pattern 3: Escalation (Agent5 → Human → Agent2)
# ---------------------------------------------------------------------------

def escalate(
    agent5: Agent,
    sorry_context: str,
    build_errors: str,
    plan_text: str,
) -> str:
    """Agent5 diagnoses the failure; human decides the next action.

    Returns one of: ``"replan"``, ``"fix_assumptions"``, ``"abort"``.
    """
    diagnosis = agent5.call(
        f"Diagnose why these sorry's cannot be closed.\n\n"
        f"## Remaining sorry context\n{sorry_context}\n\n"
        f"## Build errors\n```\n{build_errors[:3000]}\n```\n\n"
        f"## Planner guidance that was used\n{plan_text[:2000]}"
    )

    console.print(Panel(diagnosis, title="[red bold]Agent5 — Diagnosis"))
    console.print()

    while True:
        action = console.input(
            "[bold]Action?[/bold]  "
            "[r]e-plan  /  [f]ix assumptions  /  [a]bort : "
        ).strip().lower()
        if action in ("r", "replan", "re-plan"):
            return "replan"
        if action in ("f", "fix", "fix_assumptions"):
            return "fix_assumptions"
        if action in ("a", "abort"):
            return "abort"
        console.print("[red]Invalid choice.  Enter r, f, or a.")
