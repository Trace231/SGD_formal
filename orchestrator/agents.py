"""Agent abstraction and shared utilities for orchestration."""

from __future__ import annotations

import time
from typing import Any, Callable

from rich.console import Console
from rich.panel import Panel

from orchestrator.config import (
    AGENT3_MINIMAL_CONTEXT,
    AGENT9_MINIMAL_CONTEXT,
    AGENT_CONFIGS,
    MAX_TOKENS,
    RETRY_LIMITS,
    should_use_codex_backend,
)
from orchestrator.file_io import generate_project_manifest, load_files
from orchestrator.prompts import AGENT_FILES, SYSTEM_PROMPTS
from orchestrator.providers import call_llm, call_llm_qwen_sdk_with_retry, call_llm_sdk_with_retry

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
            check_lean_expr,
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
        self.register("check_lean_expr", check_lean_expr)
        self.register("get_lean_goal", get_lean_goal)
        self.register("run_lean_verify", run_lean_verify)
        self.register("run_repo_verify", run_repo_verify)
        self.register("apply_doc_patch", apply_doc_patch)

    def register_readonly_tools(self) -> None:
        """Register read-only tools for agents that may only inspect files."""
        from orchestrator.tools import (
            check_lean_expr,
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
        self.register("check_lean_expr", check_lean_expr)

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
        start = time.perf_counter()
        result = self._tools[name](*args, **kwargs)
        elapsed_ms = int((time.perf_counter() - start) * 1000.0)
        try:
            from orchestrator.audit_logger import AuditLogger
            AuditLogger.get().log_tool_call(
                name,
                kwargs,
                result,
                elapsed_ms=elapsed_ms,
            )
        except Exception:  # noqa: BLE001
            pass  # audit must not break tool execution
        return result

    def list_tools(self) -> list[str]:
        """Return all registered tool names."""
        return sorted(self._tools.keys())


# ---------------------------------------------------------------------------
# Agent backends
# ---------------------------------------------------------------------------


class AgentBackend:
    """Backend strategy used by Agent.call()."""

    name = "base"

    def call(self, agent: "Agent", *, system: str, messages: list[dict[str, str]], max_tokens: int) -> str:
        raise NotImplementedError


class HttpAgentBackend(AgentBackend):
    """Existing HTTP-style provider backend."""

    name = "http"

    def call(self, agent: "Agent", *, system: str, messages: list[dict[str, str]], max_tokens: int) -> str:
        agent.llm_transport = "api"
        agent.sdk_model = ""
        return call_llm(
            provider=agent.provider,
            model=agent.model,
            system=system,
            messages=messages,
            max_tokens=max_tokens,
        )


class CodexAgentBackend(HttpAgentBackend):
    """Codex-oriented backend shim (provider-compatible, stateful messages)."""

    name = "codex"

    _CODEX_HINT = (
        "[CODEX RUNTIME MODE]\n"
        "Use concise reasoning, prefer tool-based verification loops, and return strictly "
        "structured outputs when schema is requested.\n\n"
    )

    def call(self, agent: "Agent", *, system: str, messages: list[dict[str, str]], max_tokens: int) -> str:
        from orchestrator import config as runtime_config

        codex_system = self._CODEX_HINT + system
        transport = str(getattr(runtime_config, "CODEX_TRANSPORT", "sdk")).strip().lower()
        sdk_key = str(runtime_config.API_KEYS.get("openai", "")).strip()

        # Explicitly requested legacy API transport.
        if transport == "api":
            return super().call(agent, system=codex_system, messages=messages, max_tokens=max_tokens)

        # Qwen provider uses SDK chat-completions transport (no OPENAI_API_KEY required).
        if str(agent.provider).strip().lower() == "qwen":
            try:
                reply = call_llm_qwen_sdk_with_retry(
                    model=agent.model,
                    system=codex_system,
                    messages=messages,
                    max_tokens=max_tokens,
                    timeout=getattr(runtime_config, "CODEX_SDK_TIMEOUT", 120),
                )
                agent.llm_transport = "sdk-chat"
                agent.sdk_model = agent.model
                agent.degraded_to_api = False
                agent.degrade_reason = ""
                return reply
            except Exception as exc:
                agent.degraded_to_api = True
                cause = getattr(exc, "__cause__", None)
                if cause is not None:
                    agent.degrade_reason = (
                        f"sdk_qwen_error:{type(exc).__name__}:{exc};cause={type(cause).__name__}:{cause}"
                    )
                else:
                    agent.degrade_reason = f"sdk_qwen_error:{type(exc).__name__}:{exc}"
                if not getattr(runtime_config, "CODEX_SDK_FALLBACK_TO_API", True):
                    raise
                return super().call(agent, system=codex_system, messages=messages, max_tokens=max_tokens)

        # Non-Qwen SDK path requires OPENAI_API_KEY.
        if not sdk_key:
            agent.degraded_to_api = True
            agent.degrade_reason = "missing_openai_api_key"
            if not getattr(runtime_config, "CODEX_SDK_FALLBACK_TO_API", True):
                raise RuntimeError("OPENAI_API_KEY missing and fallback disabled")
            return super().call(agent, system=codex_system, messages=messages, max_tokens=max_tokens)

        sdk_model = str(getattr(runtime_config, "CODEX_SDK_MODEL", "gpt-5-codex") or "gpt-5-codex")
        try:
            reply = call_llm_sdk_with_retry(
                model=sdk_model,
                system=codex_system,
                messages=messages,
                max_tokens=max_tokens,
                timeout=getattr(runtime_config, "CODEX_SDK_TIMEOUT", 120),
            )
            agent.llm_transport = "sdk"
            agent.sdk_model = sdk_model
            agent.degraded_to_api = False
            agent.degrade_reason = ""
            return reply
        except Exception as exc:
            agent.degraded_to_api = True
            cause = getattr(exc, "__cause__", None)
            if cause is not None:
                agent.degrade_reason = (
                    f"sdk_error:{type(exc).__name__}:{exc};cause={type(cause).__name__}:{cause}"
                )
            else:
                agent.degrade_reason = f"sdk_error:{type(exc).__name__}:{exc}"
            if not getattr(runtime_config, "CODEX_SDK_FALLBACK_TO_API", True):
                raise
            return super().call(agent, system=codex_system, messages=messages, max_tokens=max_tokens)


def _resolve_runtime(role: str, runtime_hint: str | None) -> str:
    if runtime_hint:
        hint = str(runtime_hint).strip().lower()
        if hint in {"http", "codex"}:
            return hint
    return "codex" if should_use_codex_backend(role) else "http"


def _build_backend(runtime: str) -> AgentBackend:
    if runtime == "codex":
        return CodexAgentBackend()
    return HttpAgentBackend()


def _role_prefers_minimal_context(role: str) -> bool:
    if role == "sorry_closer":
        return bool(AGENT3_MINIMAL_CONTEXT)
    if role == "strategy_planner":
        return bool(AGENT9_MINIMAL_CONTEXT)
    return False


def _build_extra_file_context(role: str, extra_files: list[str] | None) -> tuple[str, str]:
    if not extra_files:
        return "", "full"
    if not _role_prefers_minimal_context(role):
        return load_files(extra_files), "full"

    from orchestrator.context_builders import _build_escalation_file_context

    blocks: list[str] = []
    for path in extra_files:
        try:
            snippet = _build_escalation_file_context(str(path), None)
        except Exception:
            snippet = "(file missing or unreadable)"
        blocks.append(f'<file path="{path}">\n{snippet}\n</file>')
    return "\n\n".join(blocks), "minimal"


# ---------------------------------------------------------------------------
# Agent class — wraps a role, provider config, and conversation history
# ---------------------------------------------------------------------------

class Agent:
    """A stateful LLM agent with a fixed role and multi-turn memory."""

    def __init__(self, role: str, extra_files: list[str] | None = None, runtime_hint: str | None = None):
        cfg = AGENT_CONFIGS[role]
        self.role = role
        self.provider = cfg["provider"]
        self.model = cfg["model"]
        self.max_tokens: int = cfg.get("max_tokens", MAX_TOKENS)
        self.system = SYSTEM_PROMPTS[role]
        self.messages: list[dict[str, str]] = []
        self.runtime = _resolve_runtime(role, runtime_hint)
        self._backend = _build_backend(self.runtime)
        self.backend_name = self._backend.name
        self.llm_transport = "api"
        self.sdk_model = ""
        self.degraded_to_api = False
        self.degrade_reason = ""
        self.extra_files = list(extra_files or [])
        self.active_target_file = self.extra_files[0] if self.extra_files else ""
        self.context_mode = "full"

        files = list(AGENT_FILES.get(role, []))
        use_manifest: bool = cfg.get("use_manifest", False)
        context_mode = "full"
        if use_manifest:
            # Manifest mode: shared context files are indexed compactly so the
            # agent uses read_file / search_in_file to fetch actual signatures.
            # The target algorithm file (extra_files) is always loaded in full.
            self._file_context = generate_project_manifest(files)
            extra_ctx, extra_mode = _build_extra_file_context(role, extra_files)
            if "[FILE NOT FOUND]" in self._file_context:
                context_mode = "minimal"
            if extra_ctx:
                self._file_context += "\n\n" + extra_ctx
                context_mode = extra_mode if extra_mode == "minimal" else context_mode
        else:
            if extra_files:
                files.extend(extra_files)
            self._file_context = load_files(files) if files else ""
        self.context_mode = context_mode
        try:
            from orchestrator.audit_logger import AuditLogger

            AuditLogger.get().log_event(
                "context_mode",
                role=role,
                context_mode=context_mode,
                manifest_enabled=bool(use_manifest),
            )
        except Exception:  # noqa: BLE001
            pass

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

        self.llm_transport = "api"
        self.sdk_model = ""
        self.degraded_to_api = False
        self.degrade_reason = ""

        start = time.perf_counter()
        reply = self._backend.call(
            self,
            system=self.system,
            messages=self.messages,
            max_tokens=self.max_tokens,
        )
        elapsed_ms = int((time.perf_counter() - start) * 1000.0)
        self.messages.append({"role": "assistant", "content": reply})
        try:
            from orchestrator.audit_logger import AuditLogger
            AuditLogger.get().log_agent_call(
                self.role,
                full_msg,
                reply,
                prompt_full=full_msg,
                reply_full=reply,
                elapsed_ms=elapsed_ms,
                backend=self.backend_name,
                llm_transport=self.llm_transport,
                sdk_model=self.sdk_model,
                degraded_to_api=self.degraded_to_api,
                degrade_reason=self.degrade_reason,
                target_file=self.active_target_file,
                context_mode=self.context_mode,
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
    When AGENT5_DEFAULT_ACTION is set (default "a"), skips prompt and returns that action.
    """
    from orchestrator.config import AGENT5_DEFAULT_ACTION

    raw, _ = diagnose(agent5, sorry_context, build_errors, plan_text)
    console.print(Panel(raw, title="[red bold]Agent5 — Diagnosis"))
    console.print()

    default_action = AGENT5_DEFAULT_ACTION
    if default_action:
        action = str(default_action).strip().lower()
        if action in ("a", "abort"):
            console.print("[yellow][Agent5] Default action: abort (AGENT5_DEFAULT_ACTION=a)[/yellow]")
            return "abort"
        if action in ("r", "replan", "re-plan"):
            console.print("[yellow][Agent5] Default action: replan (AGENT5_DEFAULT_ACTION=r)[/yellow]")
            return "replan"
        if action in ("f", "fix", "fix_assumptions"):
            console.print("[yellow][Agent5] Default action: fix_assumptions (AGENT5_DEFAULT_ACTION=f)[/yellow]")
            return "fix_assumptions"

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
