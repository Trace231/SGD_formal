"""Agent abstraction and shared utilities for orchestration."""

from __future__ import annotations

from typing import Any, Callable

from rich.console import Console
from rich.panel import Panel

from orchestrator.config import (
    AGENT_CONFIGS,
    MAX_TOKENS,
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

    def register_staging_tools(self, target_algo: str = "") -> None:
        """Read-only tools + write_staging_lemma.  Used by Agent2 during mid-proof escalation."""
        import functools

        from orchestrator.tools import write_staging_lemma

        self.register_readonly_tools()
        if target_algo:
            self.register(
                "write_staging_lemma",
                functools.partial(write_staging_lemma, target_algo=target_algo),
            )
        else:
            self.register("write_staging_lemma", write_staging_lemma)

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

    raw = agent5.call(
        _DIAG_PROMPT_TEMPLATE.format(
            sorry_context=sorry_context,
            build_errors=build_errors[:3000],
            plan_text=plan_text[:2000],
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
    staging_file: str | None,
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
      3. If classification is STAGING_FIX → apply rule-based staging fixes
         and re-verify.
      4. If verification passes → return ``"fixed"``.
      5. Otherwise loop with updated errors up to *max_repair_rounds* times.
      6. If still failing → fall back to the human ``escalate()`` prompt.

    Returns one of: ``"fixed"``, ``"replan"``, ``"fix_assumptions"``,
    ``"abort"``.
    """
    from pathlib import Path
    from orchestrator.assumption_repair import (
        apply_assumption_patches,
        apply_staging_rules,
    )
    from orchestrator.tools import run_lean_verify
    from orchestrator.config import PROJECT_ROOT

    _staging_path = Path(staging_file) if staging_file else None
    _target_path = (
        Path(target_file) if Path(target_file).is_absolute()
        else PROJECT_ROOT / target_file
    )

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

        elif classification == "STAGING_FIX" and _staging_path:
            patched = apply_staging_rules(_staging_path, current_errors)
            console.print(
                f"[green][Agent5] Applied {patched} staging fix(es) to {_staging_path.name}"
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
                f"[green][Agent5] Build clean with {sorry_count} sorry(s) remaining — "
                "returning to Phase 3."
            )
            return "fixed"

        # Update errors for the next diagnosis round
        current_errors = result.get("errors", current_errors)

    # Auto-repair exhausted or not applicable — ask the human
    return escalate(agent5, sorry_context, current_errors, plan_text)
