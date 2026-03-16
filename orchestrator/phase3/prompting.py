"""Prompt builders used by Phase3 orchestration."""

from __future__ import annotations

from orchestrator.context_builders import (
    _build_escalation_file_context,
    _prequery_dependency_signatures,
)
from orchestrator.error_classifier import _extract_first_error_line

def _build_preemptive_agent7_prompt(
    hint: str,
    target_file: str,
    last_verify_text: str,
    _agent7_registry: "object | None" = None,
) -> str:
    """Build the Agent7 prompt for a preemptive (Agent2-routed) invocation."""
    snippet = _build_escalation_file_context(
        target_file, _extract_first_error_line(last_verify_text)
    )
    dep_sigs = _prequery_dependency_signatures(last_verify_text, target_file)
    return (
        "Produce a strict interface-audit protocol JSON for Agent3.\n"
        f"Target file: {target_file}\n"
        "[Preemptive invocation — triggered by Agent2 routing decision]\n\n"
        f"Agent2 diagnosis:\n{hint[:1200]}\n\n"
        f"Latest build errors:\n```\n{last_verify_text[:2000]}\n```\n\n"
        f"Current file (full when ≤500 lines):\n```lean\n{snippet[:20000]}\n```\n\n"
        f"Dependency signatures:\n```lean\n{dep_sigs[:4000]}\n```\n\n"
        "Return strict JSON only as specified in your system prompt."
    )

