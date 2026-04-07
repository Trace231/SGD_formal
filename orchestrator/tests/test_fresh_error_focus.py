"""Regression tests for fresh-error focus hardening."""

from __future__ import annotations

import json

import orchestrator.phase3_agent8 as a8
from orchestrator.agent_callers import _call_agent7_with_tools
from orchestrator.context_builders import (
    _build_stale_error_hint,
    _check_patch_symbols,
    _infer_definition_file_from_registry,
)
from orchestrator.phase3_agent8 import (
    _build_agent8_tick_context,
    _canonical_error_signature,
    run_agent8_midcheck,
)


class _RecordingRegistry:
    def __init__(self, result: str = "hit") -> None:
        self.calls: list[tuple[str, dict]] = []
        self._result = result

    def call(self, tool_name: str, **kwargs):
        self.calls.append((tool_name, kwargs))
        return self._result

    def register_readonly_tools(self) -> None:
        return None

    def register_investigation_tools(self) -> None:
        return None


class _FakeAgent:
    def __init__(self, replies: list[str]) -> None:
        self.replies = list(replies)
        self.messages: list[str] = []

    def call(self, message: str) -> str:
        self.messages.append(message)
        if self.replies:
            return self.replies.pop(0)
        return self.messages[-1]


def test_symbol_evidence_checks_use_pattern_kwarg():
    registry = _RecordingRegistry(result="Mathlib/Foo.lean:10: theorem foo : True")
    msg = _check_patch_symbols({"new_str": "by exact Foo.bar_baz"}, registry)
    assert msg is None
    assert registry.calls[0][0] == "search_codebase"
    assert registry.calls[0][1] == {"pattern": "Foo.bar_baz"}


def test_infer_definition_file_uses_pattern_kwarg():
    registry = _RecordingRegistry(result="Lib/Foo.lean:12: theorem foo : True")
    found = _infer_definition_file_from_registry(registry, "foo", "Algorithms/Target.lean")
    assert found == "Lib/Foo.lean"
    assert registry.calls[0][1] == {"pattern": "foo"}


def test_agent7_protocol_requires_runtime_lookup_evidence():
    final_json = json.dumps(
        {
            "root_cause": "signature drift",
            "mismatch_table": [{"symbol": "integral_nonneg"}],
            "ordered_steps": [{"step_id": "S1", "purpose": "fix", "tool": "read_file", "required_args": {}, "acceptance": "ok"}],
            "step_acceptance": [{"step_id": "S1", "expected_effect": "specific_error_removed"}],
            "forbidden_patterns": [],
            "fallback_trigger": {"on_no_progress_steps": 2, "on_sorry_regression": True},
        }
    )
    agent = _FakeAgent([final_json, final_json, final_json, final_json])
    obj, reply = _call_agent7_with_tools(agent, _RecordingRegistry(), "audit", max_tool_rounds=1)
    assert obj is None
    assert "fallback_trigger" in reply
    assert any("Runtime validation failed" in m for m in agent.messages[1:])


def test_agent7_protocol_accepts_check_lean_expr_evidence():
    lookup = json.dumps(
        {
            "type": "lookup",
            "tool_calls": [{"tool": "check_lean_expr", "arguments": {"expr": "integral_nonneg"}}],
        }
    )
    final_json = json.dumps(
        {
            "root_cause": "signature drift",
            "mismatch_table": [{"symbol": "integral_nonneg"}],
            "ordered_steps": [{"step_id": "S1", "purpose": "fix", "tool": "read_file", "required_args": {}, "acceptance": "ok"}],
            "step_acceptance": [{"step_id": "S1", "expected_effect": "specific_error_removed"}],
            "forbidden_patterns": [],
            "fallback_trigger": {"on_no_progress_steps": 2, "on_sorry_regression": True},
        }
    )
    agent = _FakeAgent([lookup, final_json])
    obj, _ = _call_agent7_with_tools(
        agent,
        _RecordingRegistry(result={"expr": "integral_nonneg", "type": "..." }),
        "audit",
        max_tool_rounds=2,
    )
    assert obj is not None
    assert obj["root_cause"] == "signature drift"


def test_canonical_error_signature_prefers_verifier_primary_line():
    errors = (
        "Algorithms/Foo.lean:42:7: error: Application type mismatch\n"
        "Algorithms/Foo.lean:48:2: error: unsolved goals"
    )
    assert _canonical_error_signature(errors) == "Foo.lean:42:application type mismatch"


def test_build_agent8_tick_context_includes_canonical_and_stale_blocks(tmp_path):
    target = tmp_path / "Algo.lean"
    target.write_text("import Mathlib\n\ntheorem t : True := by\n  trivial\n", encoding="utf-8")
    ctx = _build_agent8_tick_context(
        str(target),
        "Algo.lean:4:2: error: unsolved goals",
        "plan",
        [],
        baseline_errors="Algo.lean:4:2: error: unsolved goals",
        canonical_error_signature="Algo.lean:4:unsolved goals",
        stale_error_hint="## STALE ERROR GUARD\nread current declaration",
        reset_hypothesis_bias=True,
    )
    assert "Canonical Current Error" in ctx
    assert "STALE ERROR GUARD" in ctx
    assert "Hypothesis Reset" in ctx


def test_midcheck_overrides_stale_error_signature_with_fresh_verify(monkeypatch, tmp_path):
    target = tmp_path / "Algo.lean"
    target.write_text("import Mathlib\n\ntheorem t : True := by\n  trivial\n", encoding="utf-8")

    class _DummyAgent:
        def __init__(self, *_args, **_kwargs) -> None:
            pass

    monkeypatch.setattr("orchestrator.tools.run_lean_verify", lambda _path: {
        "errors": "Algo.lean:4:2: error: unsolved goals",
        "exit_code": 1,
        "sorry_count": 0,
    })
    monkeypatch.setattr(a8, "Agent", _DummyAgent)
    monkeypatch.setattr(a8, "ToolRegistry", _RecordingRegistry)
    monkeypatch.setattr(
        a8,
        "_safe_llm_call",
        lambda *_args, **_kwargs: json.dumps(
            {
                "action": "agent3_tactical",
                "priority_level": "P4",
                "reason": "fresh verifier says tactical",
                "targeted_prompt": "",
                "error_signature": "stale old signature",
                "hypothesis": "fix current goal",
                "evidence": [
                    {"source": "lean_verify", "snippet": "unsolved goals"},
                    {"source": "history", "snippet": "fresh verify"},
                ],
                "confidence": 0.7,
                "counterfactual": "agent7 is unnecessary",
            }
        ),
    )

    decision = run_agent8_midcheck(
        str(target),
        "plan",
        "OLD.lean:1:1: error: unknown identifier foo",
        decision_history=[],
        turns_elapsed=3,
    )
    assert decision["error_signature"] == "Algo.lean:4:unsolved goals"


def test_build_stale_error_hint_suggests_pattern_lookup():
    registry = _RecordingRegistry(result="Lib/Foo.lean:10: theorem foo : True")
    hint = _build_stale_error_hint(
        registry,
        "Algorithms/Target.lean",
        "Algorithms/Target.lean:10:2: error: unknown identifier `foo`",
        10,
        3,
    )
    assert "Suggested next action" in hint
    assert '"query"' not in hint
