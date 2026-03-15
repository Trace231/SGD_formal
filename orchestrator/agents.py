"""Agent abstraction and shared utilities for orchestration."""

from __future__ import annotations

from typing import Any, Callable

from rich.console import Console
from rich.panel import Panel

from orchestrator.config import (
    AGENT_CONFIGS,
    MAX_TOKENS,
    RETRY_LIMITS,
)
from orchestrator.file_io import generate_project_manifest, load_files
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
            check_lean_have,
            edit_file_patch,
            get_lean_goal,
            overwrite_file,
            read_file,
            read_file_readonly,
            run_lean_verify,
            run_repo_verify,
            search_codebase,
            search_in_file,
            search_in_file_readonly,
            write_new_file,
        )

        self.register("read_file", read_file)
        self.register("read_file_readonly", read_file_readonly)
        self.register("search_in_file", search_in_file)
        self.register("search_in_file_readonly", search_in_file_readonly)
        self.register("search_codebase", search_codebase)
        self.register("write_new_file", write_new_file)
        self.register("overwrite_file", overwrite_file)
        self.register("edit_file_patch", edit_file_patch)
        self.register("check_lean_have", check_lean_have)
        self.register("get_lean_goal", get_lean_goal)
        self.register("run_lean_verify", run_lean_verify)
        self.register("run_repo_verify", run_repo_verify)
        self.register("apply_doc_patch", apply_doc_patch)

    def register_readonly_tools(self) -> None:
        """Register read-only tools for agents that may only inspect files."""
        from orchestrator.tools import (
            read_file,
            read_file_readonly,
            search_codebase,
            search_in_file,
            search_in_file_readonly,
        )

        self.register("read_file", read_file)
        self.register("read_file_readonly", read_file_readonly)
        self.register("search_in_file", search_in_file)
        self.register("search_in_file_readonly", search_in_file_readonly)
        self.register("search_codebase", search_codebase)

    def register_investigation_tools(self) -> None:
        """Read-only tools + run_lean_verify for Agent8 investigation phase.

        Intentionally excludes all write tools and check_lean_have to prevent
        side-effects during the decision phase.
        """
        from orchestrator.tools import run_lean_verify

        self.register_readonly_tools()
        self.register("run_lean_verify", run_lean_verify)

    def register_scaffold_tools(self) -> None:
        """Full write access for Agent2 Phase 3a scaffold writing.

        Includes write_new_file, edit_file_patch, run_lean_verify,
        plus all read-only tools.  Agent2 uses this to create the complete Lean file
        (all theorem statements + sorry placeholders) and verify it compiles.
        """
        from orchestrator.tools import (
            edit_file_patch,
            run_lean_verify,
            write_new_file,
        )

        self.register_readonly_tools()
        self.register("write_new_file", write_new_file)
        self.register("edit_file_patch", edit_file_patch)
        self.register("run_lean_verify", run_lean_verify)

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
        use_manifest: bool = cfg.get("use_manifest", False)
        if use_manifest:
            # Manifest mode: shared context files are indexed compactly so the
            # agent uses read_file / search_in_file to fetch actual signatures.
            # The target algorithm file (extra_files) is always loaded in full.
            self._file_context = generate_project_manifest(files)
            if extra_files:
                self._file_context += "\n\n" + load_files(extra_files)
        else:
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

        # Token budget trimming: drop oldest exchange pairs (assistant + next user)
        # keeping messages[0] (file context) intact.
        # Estimate: total characters / 3 ≈ tokens (conservative for code/mixed content).
        # qwen3-max: max input 252K, max output 32K → safe message budget ~200K tokens.
        while len(self.messages) > 3:
            estimated = sum(len(m["content"]) for m in self.messages) // 3
            if estimated + self.max_tokens <= 200_000:
                break
            del self.messages[1:3]  # remove oldest (assistant, user) pair

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
# Pattern 3: Escalation (Agent5 → Auto-Repair → Human fallback)
# ---------------------------------------------------------------------------

_DIAG_PROMPT_TEMPLATE = (
    "Diagnose why these sorry's cannot be closed.\n\n"
    "## Remaining sorry context\n{sorry_context}\n\n"
    "## Build errors\n```\n{build_errors}\n```\n\n"
    "## Planner guidance that was used\n{plan_text}"
)


def diagnose(
    agent5: Agent,
    sorry_context: str,
    build_errors: str,
    plan_text: str,
) -> tuple[str, dict]:
    """Call Agent5 and return (raw_text, structured_dict).

    The structured dict is parsed from the JSON block that Agent5 appends
    to every response (see diagnostician system prompt).  Falls back to
    ``{"auto_repairable": False}`` when no valid JSON block is present.
    """
    from orchestrator.assumption_repair import parse_diagnosis_json

    _a5_err_chars = RETRY_LIMITS.get("AGENT5_ERRORS_CHARS", 3000)
    _a5_plan_chars = RETRY_LIMITS.get("AGENT5_PLAN_CHARS", 2000)
    raw = agent5.call(
        _DIAG_PROMPT_TEMPLATE.format(
            sorry_context=sorry_context,
            build_errors=build_errors[:_a5_err_chars],
            plan_text=plan_text[:_a5_plan_chars],
        )
    )
    structured = parse_diagnosis_json(raw)
    return raw, structured


def escalate(
    agent5: Agent,
    sorry_context: str,
    build_errors: str,
    plan_text: str,
) -> str:
    """Agent5 diagnoses the failure; human decides the next action.

    Returns one of: ``"replan"``, ``"fix_assumptions"``, ``"abort"``.
    """
    raw, _ = diagnose(agent5, sorry_context, build_errors, plan_text)
    console.print(Panel(raw, title="[red bold]Agent5 — Diagnosis"))
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


def auto_repair_loop(
    agent5: Agent,
    target_file: str,
    build_errors: str,
    plan_text: str,
    sorry_context: str,
    *,
    max_repair_rounds: int = 3,
) -> str:
    """Attempt automatic repair before asking the human.

    Rounds:
      1. Agent5 produces a structured diagnosis.
      2. If ``auto_repairable`` and classification is ASSUMPTIONS_WRONG →
         patch the target file signatures and re-verify.
      3. If verification passes → return ``"fixed"``.
      4. Otherwise loop with updated errors up to *max_repair_rounds* times.
      5. If still failing → fall back to the human ``escalate()`` prompt.

    Returns one of: ``"fixed"``, ``"replan"``, ``"fix_assumptions"``,
    ``"abort"``.
    """
    from orchestrator.assumption_repair import apply_assumption_patches
    from orchestrator.tools import run_lean_verify

    current_errors = build_errors

    for repair_round in range(1, max_repair_rounds + 1):
        console.print(
            f"[cyan][Agent5] Auto-repair round {repair_round}/{max_repair_rounds}…"
        )

        raw, structured = diagnose(agent5, sorry_context, current_errors, plan_text)
        console.print(Panel(raw, title=f"[yellow]Agent5 — Diagnosis (round {repair_round})"))

        if not structured.get("auto_repairable", False):
            console.print("[yellow][Agent5] Not auto-repairable — falling back to human.")
            break

        classification = structured.get("classification", "")
        patched = 0

        if classification == "ASSUMPTIONS_WRONG":
            assumptions = structured.get("assumptions_to_add", [])
            if assumptions:
                patched = apply_assumption_patches(target_file, assumptions)
                console.print(
                    f"[green][Agent5] Patched {patched} assumption(s) into {target_file}"
                )
        else:
            console.print(
                f"[yellow][Agent5] Classification '{classification}' — "
                "no auto-repair action available."
            )
            break

        if patched == 0:
            console.print("[yellow][Agent5] No patches applied — stopping auto-repair.")
            break

        # Re-verify after patching
        result = run_lean_verify(target_file)
        exit_code = int(result.get("exit_code", 1))
        sorry_count = int(result.get("sorry_count", -1))

        console.print(
            f"[cyan][Agent5] Post-repair verify: exit={exit_code}, sorry={sorry_count}"
        )

        if exit_code == 0 and sorry_count == 0:
            console.print("[green bold][Agent5] Auto-repair succeeded — build clean!")
            return "fixed"

        if exit_code == 0 and sorry_count > 0:
            console.print(
                f"[yellow][Agent5] Build clean but {sorry_count} sorry(s) remain — "
                "not a success under strict criterion."
            )
            current_errors = (
                f"STRICT_SUCCESS_NOT_MET: build succeeded but sorry_count={sorry_count} > 0"
            )
            continue

        # Update errors for the next diagnosis round
        current_errors = result.get("errors", current_errors)

    # Auto-repair exhausted or not applicable — ask the human
    return escalate(agent5, sorry_context, current_errors, plan_text)
