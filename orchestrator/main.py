"""CLI entry point: five-phase orchestration with rich progress display
and human checkpoints.

Usage::

    python -m orchestrator.main \\
      --algorithm "SVRG" \\
      --update-rule "w_{t+1} = w_t - η·(∇f_i(w_t) - ∇f_i(w^s) + ∇f(w^s))" \\
      --proof-sketch "Variance reduction via control variate, O(1/T) rate" \\
      --archetype B

Or interactive mode::

    python -m orchestrator.main --interactive
"""

from __future__ import annotations

import argparse
import subprocess
import sys

from rich.console import Console
from rich.panel import Panel
from rich.progress import BarColumn, Progress, SpinnerColumn, TextColumn

from orchestrator.agents import (
    Agent,
    approval_loop,
    escalate,
    proving_loop,
)
from orchestrator.config import MAX_PROVE_RETRIES, PROJECT_ROOT
from orchestrator.file_io import (
    load_file,
    parse_code_blocks,
    snapshot_file,
    write_lean_file,
    write_text_file,
)
from orchestrator.metrics import MetricsStore, count_glue_tricks_sections
from orchestrator.prompts import (
    build_algorithm_card,
    load_meta_prompt_a,
    load_meta_prompt_b,
)
from orchestrator.verify import (
    check_glue_tricks_gate,
    check_leverage_gate,
    check_used_in_tags,
)

console = Console()

_GLUE_TRICKS_PATH = "docs/GLUE_TRICKS.md"
_CATALOG_PATH = "docs/CATALOG.md"
_METHODOLOGY_PATH = "docs/METHODOLOGY.md"


# ---------------------------------------------------------------------------
# Git safety helpers
# ---------------------------------------------------------------------------

def _git_stash_push() -> bool:
    """Stash uncommitted changes.  Returns True if something was stashed."""
    result = subprocess.run(
        ["git", "stash", "push", "-m", "orchestrator-auto-stash"],
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
    )
    return "No local changes" not in result.stdout


def _git_stash_pop() -> None:
    subprocess.run(
        ["git", "stash", "pop"],
        cwd=PROJECT_ROOT,
        capture_output=True,
    )


def _get_modified_lean_files() -> list[str]:
    """Return all .lean files changed or created since the pipeline started.

    Relies on the git baseline established by _git_stash_push() at run start.
    Includes both tracked modified files and untracked new files.
    """
    modified = subprocess.run(
        ["git", "diff", "--name-only"],
        cwd=PROJECT_ROOT, capture_output=True, text=True,
    ).stdout.splitlines()

    untracked = subprocess.run(
        ["git", "ls-files", "--others", "--exclude-standard"],
        cwd=PROJECT_ROOT, capture_output=True, text=True,
    ).stdout.splitlines()

    return [f for f in modified + untracked if f.endswith(".lean")]


# ---------------------------------------------------------------------------
# Phase implementations
# ---------------------------------------------------------------------------

def phase1_generate_prompt(
    algorithm: str,
    update_rule: str,
    proof_sketch: str,
    archetype: str,
) -> str:
    """Phase 1: Agent1 generates the Prover prompt via Meta-Prompt A."""
    console.rule("[bold cyan]Phase 1/5 — Generate Prover Prompt")

    agent1 = Agent("orchestrator")
    meta_a = load_meta_prompt_a()
    card = build_algorithm_card(algorithm, update_rule, proof_sketch, archetype)

    prompt_text = agent1.call(
        f"Generate a complete Prover prompt by instantiating the Meta-Prompt A "
        f"template below with the algorithm card.\n\n"
        f"## Meta-Prompt A Template\n{meta_a}\n\n"
        f"## Algorithm Card\n{card}"
    )
    console.print(
        f"[green]\\[Agent1] Prover prompt generated "
        f"({len(prompt_text)} chars)."
    )
    return prompt_text


def phase2_plan_and_approve(
    prover_prompt: str,
    force_low_leverage: bool = False,
) -> tuple[str, Agent, Agent]:
    """Phase 2: Agent1 ↔ Agent2 approval loop + leverage gate.

    Returns (approved_plan, agent1, agent2) so they can be reused.
    """
    console.rule("[bold cyan]Phase 2/5 — Plan & Approve")

    agent1 = Agent("orchestrator")
    agent2 = Agent("planner")

    plan = approval_loop(agent1, agent2, prover_prompt)

    passed, leverage = check_leverage_gate(plan)
    console.print(
        f"[{'green' if passed else 'red'}]"
        f"\\[Gate 1] Leverage = {leverage:.1%} "
        f"({'PASS' if passed else 'BLOCKED'})"
    )
    if not passed and not force_low_leverage:
        console.print(
            "[red bold]Leverage below 50%.  Use --force-low-leverage to override."
        )
        sys.exit(1)

    return plan, agent1, agent2


def phase3_prove(
    agent2: Agent,
    target_file: str,
    plan: str,
    *,
    max_retries: int = MAX_PROVE_RETRIES,
) -> tuple[bool, int, str]:
    """Phase 3: Agent2 ↔ Agent3 proving loop + Agent5 escalation.

    Returns (success, attempts, errors_or_empty).
    """
    console.rule("[bold cyan]Phase 3/5 — Prove (fill sorry)")

    agent3 = Agent("sorry_closer", extra_files=[target_file])

    def on_attempt(attempt: int, ok: bool, sorry: int) -> None:
        status = "OK" if ok else "FAIL"
        console.print(
            f"  [Agent3] attempt {attempt}/{max_retries} — "
            f"build={status}, sorry={sorry}"
        )

    result = proving_loop(
        agent2, agent3, target_file,
        max_retries=max_retries, on_attempt=on_attempt,
    )

    if result.success:
        return True, result.attempts, ""

    console.print("[red bold]Max retries exhausted — escalating to Agent5.")
    agent5 = Agent("diagnostician", extra_files=[target_file])
    sorry_context = load_file(target_file)
    action = escalate(agent5, sorry_context, result.errors, plan)

    if action == "abort":
        console.print("[red]Aborted by user.")
        sys.exit(1)
    elif action == "fix_assumptions":
        console.print(
            "[yellow]Human: fix assumptions in the theorem signature, then "
            "re-run the orchestrator."
        )
        sys.exit(1)
    elif action == "replan":
        console.print("[yellow]Re-planning requested — restarting Phase 2.")
        return False, result.attempts, result.errors

    return False, result.attempts, result.errors


def phase4_persist(
    algorithm: str,
    target_file: str,
    plan: str,
) -> tuple[int, int]:
    """Phase 4: Agent4 persists documentation (Glue + Layer 1).

    Returns (new_tricks_added, missing_used_in_count).
    """
    console.rule("[bold cyan]Phase 4/5 — Persist Documentation")

    tricks_before = snapshot_file("docs/GLUE_TRICKS.md")
    tricks_sections_before = count_glue_tricks_sections()

    modified_lean_files = _get_modified_lean_files()
    console.print(
        f"[cyan]\\[Phase 4] Modified Lean files detected: "
        f"{modified_lean_files or [target_file]}"
    )

    meta_b = load_meta_prompt_b()
    agent4 = Agent("persister", extra_files=modified_lean_files or [target_file])

    persistence_output = agent4.call(
        f"Persist the completed proof for algorithm '{algorithm}' using "
        f"Meta-Prompt B below.\n\n## Meta-Prompt B\n{meta_b}\n\n"
        f"## Approved proof plan (use this as [PROOF INPUT] for Meta-Prompt B)\n{plan}\n\n"
        f"## Modified Lean files\n"
        + "\n".join(f"- {f}" for f in (modified_lean_files or [target_file]))
    )
    console.print(
        f"[green]\\[Agent4] Persistence output generated "
        f"({len(persistence_output)} chars)."
    )

    # Write every file block Agent4 produced to disk.
    blocks = parse_code_blocks(persistence_output)
    for block in blocks:
        block_path = block.get("path")
        block_content = block["code"]
        if not block_path:
            continue  # skip untagged blocks
        block_path_lower = block_path.lower()
        if block_path.endswith(".lean"):
            write_lean_file(block_path, block_content)
            console.print(f"[green]\\[Agent4] Wrote Lean file: {block_path}")
        elif _GLUE_TRICKS_PATH in block_path_lower or block_path.endswith("GLUE_TRICKS.md"):
            write_text_file(_GLUE_TRICKS_PATH, block_content, append=True)
            console.print("[green]\\[Agent4] Appended to GLUE_TRICKS.md")
        elif _CATALOG_PATH in block_path_lower or block_path.endswith("CATALOG.md"):
            write_text_file(_CATALOG_PATH, block_content, append=True)
            console.print("[green]\\[Agent4] Appended to CATALOG.md")
        elif _METHODOLOGY_PATH in block_path_lower or block_path.endswith("METHODOLOGY.md"):
            write_text_file(_METHODOLOGY_PATH, block_content, append=False)
            console.print("[green]\\[Agent4] Replaced METHODOLOGY.md")
        else:
            write_text_file(block_path, block_content, append=False)
            console.print(f"[green]\\[Agent4] Wrote file: {block_path}")

    tricks_after = snapshot_file("docs/GLUE_TRICKS.md")
    tricks_sections_after = count_glue_tricks_sections()
    new_tricks = tricks_sections_after - tricks_sections_before

    # Gate 3: GLUE_TRICKS validation
    if tricks_before != tricks_after or new_tricks > 0:
        console.print(
            f"[green]\\[Gate 3] GLUE_TRICKS.md updated — "
            f"{new_tricks} new pattern(s)."
        )
    else:
        console.print("[green]\\[Gate 3] No new patterns — GLUE_TRICKS.md unchanged.")

    # Gate 4: Used-in tag check — covers all modified Lean files, not just target
    modified = modified_lean_files or [target_file]
    missing = check_used_in_tags(modified)
    if missing:
        console.print(
            f"[red]\\[Gate 4] Missing Used-in tags: {missing}"
        )
    else:
        console.print("[green]\\[Gate 4] All Used-in tags present.")

    return new_tricks, len(missing)


def phase5_finalize(
    algorithm: str,
    sorry_attempts: int,
    final_sorry: int,
    glue_hit_rate: float,
    new_tricks: int,
) -> None:
    """Phase 5: Persist metrics and print summary."""
    console.rule("[bold cyan]Phase 5/5 — Finalize Metrics")

    store = MetricsStore()
    record = store.build_record(
        algorithm=algorithm,
        glue_hit_rate=glue_hit_rate,
        new_tricks_added=new_tricks,
        sorry_close_attempts=sorry_attempts,
        final_sorry_count=final_sorry,
    )
    store.append(record)

    console.print(Panel(
        f"Algorithm:          {algorithm}\n"
        f"Glue hit rate:      {glue_hit_rate:.1%}\n"
        f"Total glue lemmas:  {record.total_glue_lemmas}\n"
        f"Total L1 lemmas:    {record.total_layer1_lemmas}\n"
        f"New tricks added:   {new_tricks}\n"
        f"Sorry attempts:     {sorry_attempts}\n"
        f"Final sorry count:  {final_sorry}\n",
        title="[bold green]Run Complete",
    ))


# ---------------------------------------------------------------------------
# Main orchestration
# ---------------------------------------------------------------------------

def run(
    algorithm: str,
    update_rule: str,
    proof_sketch: str,
    archetype: str,
    target_file: str | None = None,
    max_retries: int = MAX_PROVE_RETRIES,
    force_low_leverage: bool = False,
) -> None:
    """Execute the full 5-phase pipeline."""

    if target_file is None:
        target_file = f"Algorithms/{algorithm}.lean"

    stashed = _git_stash_push()

    try:
        with Progress(
            SpinnerColumn(),
            TextColumn("{task.description}"),
            BarColumn(),
            transient=True,
        ) as progress:
            task = progress.add_task("Orchestrating...", total=5)

            # Phase 1
            progress.update(task, description="Phase 1/5: Generating prover prompt...")
            prover_prompt = phase1_generate_prompt(
                algorithm, update_rule, proof_sketch, archetype
            )
            progress.advance(task)

            # Phase 2 (may loop on re-plan)
            success = False
            total_attempts = 0
            while not success:
                progress.update(task, description="Phase 2/5: Planning & approval...")
                plan, agent1, agent2 = phase2_plan_and_approve(
                    prover_prompt, force_low_leverage
                )
                progress.advance(task)

                # Phase 3
                progress.update(task, description="Phase 3/5: Proving (fill sorry)...")
                success, attempts, _ = phase3_prove(
                    agent2, target_file, plan, max_retries=max_retries
                )
                total_attempts += attempts
                if not success:
                    progress.reset(task)
                    progress.advance(task)  # re-enter at phase 2

            progress.advance(task)

            # Phase 4
            progress.update(task, description="Phase 4/5: Persisting docs...")
            _, leverage = check_leverage_gate(plan)
            new_tricks, _ = phase4_persist(algorithm, target_file, plan)
            progress.advance(task)

            # Phase 5
            progress.update(task, description="Phase 5/5: Finalizing metrics...")
            phase5_finalize(
                algorithm,
                sorry_attempts=total_attempts,
                final_sorry=0,
                glue_hit_rate=leverage,
                new_tricks=new_tricks,
            )
            progress.advance(task)

    except BaseException:
        if stashed:
            console.print("[yellow]Restoring git stash after failure...")
            _git_stash_pop()
        raise


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _interactive_input() -> dict[str, str]:
    """Prompt the user for algorithm card fields interactively."""
    console.print("[bold]Interactive mode — enter algorithm details.\n")
    return {
        "algorithm": console.input("[bold]Algorithm name:[/bold] ").strip(),
        "update_rule": console.input("[bold]Update rule:[/bold] ").strip(),
        "proof_sketch": console.input("[bold]Proof sketch:[/bold] ").strip(),
        "archetype": console.input("[bold]Archetype (A/B):[/bold] ").strip().upper(),
    }


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Multi-agent orchestrator for StochOptLib proof automation."
    )
    parser.add_argument("--algorithm", type=str, help="Algorithm name")
    parser.add_argument("--update-rule", type=str, help="Mathematical update formula")
    parser.add_argument("--proof-sketch", type=str, help="Natural-language proof sketch")
    parser.add_argument("--archetype", type=str, choices=["A", "B"], help="A or B")
    parser.add_argument("--target-file", type=str, default=None,
                        help="Target .lean file (default: Algorithms/<algorithm>.lean)")
    parser.add_argument("--max-retries", type=int, default=MAX_PROVE_RETRIES,
                        help="Max sorry-closing retries (default: 5)")
    parser.add_argument("--force-low-leverage", action="store_true",
                        help="Override the ≥50%% leverage gate")
    parser.add_argument("--interactive", action="store_true",
                        help="Prompt for algorithm card interactively")

    args = parser.parse_args()

    if args.interactive:
        fields = _interactive_input()
    else:
        if not all([args.algorithm, args.update_rule, args.proof_sketch, args.archetype]):
            parser.error(
                "Provide --algorithm, --update-rule, --proof-sketch, and "
                "--archetype, or use --interactive."
            )
        fields = {
            "algorithm": args.algorithm,
            "update_rule": args.update_rule,
            "proof_sketch": args.proof_sketch,
            "archetype": args.archetype,
        }

    run(
        algorithm=fields["algorithm"],
        update_rule=fields["update_rule"],
        proof_sketch=fields["proof_sketch"],
        archetype=fields["archetype"],
        target_file=args.target_file,
        max_retries=args.max_retries,
        force_low_leverage=args.force_low_leverage,
    )


if __name__ == "__main__":
    main()
