"""Phase 5 orchestration: finalize metrics and print audit report."""
from __future__ import annotations

from rich.console import Console
from rich.panel import Panel

from orchestrator.metrics import MetricsStore, capture_physical_metrics

console = Console()

def phase5_finalize(
    algorithm: str,
    new_tricks: int,
    phase3_audit: dict,
    total_attempts: int,
) -> None:
    """Phase 5: Persist physical metrics and print audit report."""
    console.rule("[bold cyan]Phase 7/7 — Finalize Metrics")

    store = MetricsStore()
    record = capture_physical_metrics(
        algorithm=algorithm,
        new_tricks_added=new_tricks,
        phase3_execution_history=phase3_audit.get("execution_history", []),
        phase3_attempts=total_attempts,
        estimated_token_consumption=int(
            phase3_audit.get("estimated_token_consumption", 0)
        ),
    )
    store.append(record)

    console.print(Panel(
        f"Algorithm:          {algorithm}\n"
        f"Build exit code:    {record.physical_exit_code}\n"
        f"Repo sorry count:   {record.total_repo_sorry_count}\n"
        f"\n"
        f"── Leverage Metrics ────────────────────────────────────\n"
        f"New Lib decls:      {record.new_lib_declarations}\n"
        f"Algo call hits:     {record.algorithm_calls_to_new_lib_declarations}\n"
        f"Physical leverage:  {record.physical_leverage_rate:.1%}  "
        f"[calls/(calls+decls)]\n"
        f"L_coverage:         {record.lib_coverage_rate:.1%}  "
        f"[used decls / total new decls]\n"
        f"L_density:          {record.lib_density_rate:.2f}  "
        f"[total calls / used decls]\n"
        f"\n"
        f"── Phase 3 Cost ────────────────────────────────────────\n"
        f"P3 retries:         {record.phase3_retry_count}\n"
        f"Sorry attempts:     {total_attempts}\n"
        f"Est. token usage:   {record.estimated_token_consumption}\n"
        f"\n"
        f"── Documentation ───────────────────────────────────────\n"
        f"Total glue lemmas:  {record.total_glue_lemmas}\n"
        f"Total L1 lemmas:    {record.total_layer1_lemmas}\n"
        f"New tricks added:   {new_tricks}\n"
        f"Final sorry count:  {record.final_sorry_count}\n"
        f"Doc-code aligned:   {'YES' if record.doc_code_alignment_ok else 'NO'}\n",
        title="[bold green]Run Complete (Physical Audit)",
    ))
    if not record.doc_code_alignment_ok:
        console.print(Panel(
            "\n".join(record.doc_code_alignment_missing or []),
            title="[red]Audit Mismatch: Doc-Code Alignment",
        ))


# ---------------------------------------------------------------------------
# Main orchestration
# ---------------------------------------------------------------------------

