"""Agent abstraction with multi-turn conversation state and interaction
loop helpers (approval loop, proving loop, escalation)."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable

from rich.console import Console
from rich.panel import Panel

from orchestrator.config import (
    AGENT_CONFIGS,
    MAX_APPROVAL_ROUNDS,
    MAX_PROVE_RETRIES,
    MAX_TOKENS,
)
from orchestrator.file_io import load_files, write_lean_file, extract_full_file
from orchestrator.prompts import AGENT_FILES, SYSTEM_PROMPTS
from orchestrator.providers import call_llm
from orchestrator.verify import verify_lean

console = Console()


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
        return reply

    def reset(self) -> None:
        """Clear conversation history (keeps system prompt and files)."""
        self.messages.clear()


# ---------------------------------------------------------------------------
# Proof result
# ---------------------------------------------------------------------------

@dataclass
class ProofResult:
    success: bool
    attempts: int
    final_sorry_count: int = 0
    errors: str = ""


# ---------------------------------------------------------------------------
# Pattern 1: Approval Loop (Agent1 ↔ Agent2)
# ---------------------------------------------------------------------------

def approval_loop(
    agent1: Agent,
    agent2: Agent,
    initial_prompt: str,
    *,
    max_rounds: int = MAX_APPROVAL_ROUNDS,
    on_round: Callable[[int, str], None] | None = None,
) -> str:
    """Agent2 proposes a plan; Agent1 reviews.  Repeats until APPROVED.

    *on_round* is called after each round with ``(round_number, review_text)``.

    Returns the approved plan text.

    Raises ``RuntimeError`` if *max_rounds* is exhausted.
    """
    plan = agent2.call(initial_prompt)
    console.print(Panel(plan[:500] + "..." if len(plan) > 500 else plan,
                        title="[cyan]Agent2 — Initial Plan"))

    for round_num in range(1, max_rounds + 1):
        review = agent1.call(
            f"Review this plan from Agent2.  Reply APPROVED on its own line "
            f"if the plan is acceptable, otherwise explain what must change.\n\n"
            f"{plan}"
        )

        if on_round:
            on_round(round_num, review)

        if "APPROVED" in review.upper():
            console.print(
                f"[green]\\[Agent1 ↔ Agent2] Plan APPROVED after {round_num} round(s)."
            )
            return plan

        console.print(Panel(
            review[:400] + "..." if len(review) > 400 else review,
            title=f"[yellow]Agent1 — Feedback (round {round_num})",
        ))
        plan = agent2.call(f"Revise your plan based on this feedback:\n\n{review}")
        console.print(Panel(
            plan[:500] + "..." if len(plan) > 500 else plan,
            title=f"[cyan]Agent2 — Revised Plan (round {round_num})",
        ))

    raise RuntimeError(
        f"Agent1 did not approve after {max_rounds} rounds.  "
        f"Last review:\n{review}"
    )


# ---------------------------------------------------------------------------
# Pattern 2: Proving Loop (Agent2 ↔ Agent3)
# ---------------------------------------------------------------------------

def proving_loop(
    agent2: Agent,
    agent3: Agent,
    target_file: str,
    *,
    max_retries: int = MAX_PROVE_RETRIES,
    on_attempt: Callable[[int, bool, int], None] | None = None,
) -> ProofResult:
    """Agent2 guides, Agent3 fills sorry's, lake build verifies.

    *on_attempt* is called with ``(attempt, build_ok, sorry_count)``.

    Returns a ``ProofResult``.
    """
    guidance = agent2.call(
        "Provide initial proving guidance for Agent3.  Specify which sorry "
        "to tackle first and the recommended proof strategy (Mathlib lemma, "
        "glue pattern letter, etc.)."
    )
    console.print(Panel(
        guidance[:400] + "..." if len(guidance) > 400 else guidance,
        title="[cyan]Agent2 — Initial Guidance",
    ))

    for attempt in range(1, max_retries + 1):
        code_reply = agent3.call(
            f"Fill the sorry placeholders following this guidance:\n\n{guidance}"
        )

        new_code = extract_full_file(code_reply, target_file)
        if new_code:
            write_lean_file(target_file, new_code)

        build_ok, errors, sorry_count = verify_lean(target_file)

        if on_attempt:
            on_attempt(attempt, build_ok, sorry_count)

        if build_ok and sorry_count == 0:
            console.print(
                f"[green]\\[Agent3] Success on attempt {attempt} — "
                f"lake build passed, 0 sorry."
            )
            return ProofResult(
                success=True, attempts=attempt, final_sorry_count=0
            )

        console.print(
            f"[yellow]\\[Agent3] Attempt {attempt}/{max_retries} — "
            f"build={'OK' if build_ok else 'FAIL'}, sorry={sorry_count}"
        )

        guidance = agent2.call(
            f"Attempt {attempt} failed.\n"
            f"Build exit code: {'0' if build_ok else 'nonzero'}\n"
            f"Sorry count: {sorry_count}\n"
            f"Errors:\n```\n{errors[:2000]}\n```\n"
            f"Adjust your guidance for Agent3."
        )
        console.print(Panel(
            guidance[:400] + "..." if len(guidance) > 400 else guidance,
            title=f"[cyan]Agent2 — Revised Guidance (attempt {attempt})",
        ))

    return ProofResult(
        success=False,
        attempts=max_retries,
        final_sorry_count=sorry_count,
        errors=errors,
    )


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
