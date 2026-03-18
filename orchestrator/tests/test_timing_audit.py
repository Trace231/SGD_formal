from __future__ import annotations

from orchestrator.audit_logger import AuditLogger
from orchestrator.verify import BuildResult


def test_audit_logger_records_elapsed_fields():
    audit = AuditLogger()
    audit.enabled = True
    audit.set_phase(3)

    audit.log_agent_call(
        "decision_hub",
        "prompt",
        "reply",
        elapsed_ms=123,
    )
    audit.log_tool_call(
        "run_lean_verify",
        {"path": "Algorithms/Foo.lean"},
        {"exit_code": 1},
        elapsed_ms=45,
    )

    assert audit.events[0]["elapsed_ms"] == 123
    assert audit.events[1]["elapsed_ms"] == 45


def test_build_result_carries_elapsed_ms():
    result = BuildResult(
        success=False,
        errors="boom",
        sorry_count=0,
        returncode=1,
        elapsed_ms=77,
    )
    assert result.elapsed_ms == 77
