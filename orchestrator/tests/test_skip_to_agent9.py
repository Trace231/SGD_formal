"""Regression tests for strict `--skip-to-agent9` control flow."""

from __future__ import annotations

import json
from pathlib import Path
from types import SimpleNamespace

import pytest

from orchestrator import main as main_mod
import orchestrator.phase3_agent3 as phase3_mod
import orchestrator.phase3_agent8 as phase3_agent8
import orchestrator.phase3a_agent9 as phase3_agent9


def _empty_phase3_audit() -> dict:
    return {
        "execution_history": [],
        "attempt_failures": [],
        "agent7_invocations": [],
        "agent7_step_execution_log": [],
        "agent7_plan_revisions": [],
        "agent7_blocked_actions": [],
        "agent7_forced_trigger_count": 0,
        "agent7_force_gate_entries": [],
        "agent7_force_gate_rejections": [],
        "agent7_force_gate_reason_samples": [],
        "estimated_token_consumption": 0,
        "retry_count": 0,
    }


class _FakeAudit:
    def start_run(self, _algorithm: str) -> str:
        return "test-run"

    def set_phase(self, _phase: int) -> None:
        pass

    def add_phase3_data(self, *_args, **_kwargs) -> None:
        pass

    def finish_run(self, *_args, **_kwargs) -> None:
        pass


def test_main_cli_propagates_skip_to_agent9(monkeypatch):
    captured = {}

    def _fake_run(**kwargs):
        captured.update(kwargs)

    argv = [
        "orchestrator.main",
        "--algorithm", "FooAlgo",
        "--update-rule", "w_{t+1} = w_t - g_t",
        "--proof-sketch", "Use a direct descent argument",
        "--archetype", "B",
        "--target-file", "Algorithms/FooAlgo.lean",
        "--skip-to-agent9",
    ]
    monkeypatch.setattr(main_mod, "run", _fake_run)
    monkeypatch.setattr("sys.argv", argv)

    main_mod.main()

    assert captured["skip_to_agent9"] is True
    assert captured["target_file"] == "Algorithms/FooAlgo.lean"


def test_run_skip_to_agent9_skips_phase1_and_phase2(monkeypatch, tmp_path):
    target_file = tmp_path / "Existing.lean"
    target_file.write_text("theorem t : True := by\n  trivial\n", encoding="utf-8")
    captured: dict[str, object] = {}

    monkeypatch.setattr(main_mod.AuditLogger, "get", classmethod(lambda cls: _FakeAudit()))
    monkeypatch.setattr(main_mod, "_capture_lean_baseline", lambda: (set(), set()))
    monkeypatch.setattr(
        main_mod,
        "_capture_git_run_snapshot",
        lambda _run_id: SimpleNamespace(start_sha="abc", pre_run_dirty=False, stash_used=False),
    )
    monkeypatch.setattr(main_mod, "_restore_snapshot_on_success", lambda _snapshot: None)
    monkeypatch.setattr(main_mod, "_rollback_to_snapshot", lambda _snapshot: None)
    monkeypatch.setattr(main_mod, "_ensure_algorithm_in_lakefile", lambda _name: False)
    monkeypatch.setattr(main_mod, "_remove_algorithm_from_lakefile", lambda _name: None)
    monkeypatch.setattr(main_mod, "_get_modified_lean_files", lambda *_args: [])
    monkeypatch.setattr(main_mod, "_git_diff_files", lambda: [])
    monkeypatch.setattr(main_mod, "phase4_persist", lambda *_args, **_kwargs: [])
    monkeypatch.setattr(main_mod, "phase5_finalize", lambda *_args, **_kwargs: None)
    monkeypatch.setattr(
        main_mod,
        "phase1_generate_prompt",
        lambda *_args, **_kwargs: pytest.fail("Phase 1 must be skipped"),
    )
    monkeypatch.setattr(
        main_mod,
        "phase1_generate_prompt_from_spec",
        lambda *_args, **_kwargs: pytest.fail("Spec Phase 1 must be skipped"),
    )
    monkeypatch.setattr(
        main_mod,
        "phase2_plan_and_approve",
        lambda *_args, **_kwargs: pytest.fail("Phase 2 must be skipped"),
    )

    def _fake_phase3(agent2, target_file_arg, plan, **kwargs):
        captured["agent2"] = agent2
        captured["target_file"] = target_file_arg
        captured["plan"] = plan
        captured["skip_to_agent9"] = kwargs["skip_to_agent9"]
        return True, 0, "", _empty_phase3_audit()

    monkeypatch.setattr(main_mod, "phase3_prove", _fake_phase3)

    main_mod.run(
        algorithm="FooAlgo",
        update_rule="w_{t+1} = w_t - g_t",
        proof_sketch="Close the proof from the existing scaffold",
        archetype="B",
        target_file=str(target_file),
        skip_to_agent9=True,
    )

    assert captured["agent2"] is None
    assert captured["target_file"] == str(target_file)
    assert captured["skip_to_agent9"] is True
    assert "[STRICT SKIP-TO-AGENT9 GUIDANCE]" in str(captured["plan"])


def test_run_skip_to_agent9_uses_structured_spec_guidance(monkeypatch, tmp_path):
    target_file = tmp_path / "Existing.lean"
    target_file.write_text("theorem t : True := by\n  trivial\n", encoding="utf-8")
    spec_file = tmp_path / "spec.json"
    spec_file.write_text(
        json.dumps(
            {
                "algorithm": "SpecAlgo",
                "archetype": "B",
                "sections": {
                    "2_algorithm": {
                        "update_rule": {"math": "w_{t+1} = w_t - η g_t"}
                    }
                },
            }
        ),
        encoding="utf-8",
    )
    captured = {}

    monkeypatch.setattr(main_mod.AuditLogger, "get", classmethod(lambda cls: _FakeAudit()))
    monkeypatch.setattr(main_mod, "_capture_lean_baseline", lambda: (set(), set()))
    monkeypatch.setattr(
        main_mod,
        "_capture_git_run_snapshot",
        lambda _run_id: SimpleNamespace(start_sha="abc", pre_run_dirty=False, stash_used=False),
    )
    monkeypatch.setattr(main_mod, "_restore_snapshot_on_success", lambda _snapshot: None)
    monkeypatch.setattr(main_mod, "_rollback_to_snapshot", lambda _snapshot: None)
    monkeypatch.setattr(main_mod, "_ensure_algorithm_in_lakefile", lambda _name: False)
    monkeypatch.setattr(main_mod, "_remove_algorithm_from_lakefile", lambda _name: None)
    monkeypatch.setattr(main_mod, "_get_modified_lean_files", lambda *_args: [])
    monkeypatch.setattr(main_mod, "_git_diff_files", lambda: [])
    monkeypatch.setattr(main_mod, "phase4_persist", lambda *_args, **_kwargs: [])
    monkeypatch.setattr(main_mod, "phase5_finalize", lambda *_args, **_kwargs: None)
    monkeypatch.setattr(
        main_mod,
        "phase3_prove",
        lambda _agent2, _target_file, plan, **_kwargs: (
            captured.setdefault("plan", plan) and True,
            0,
            "",
            _empty_phase3_audit(),
        ),
    )

    main_mod.run(
        algorithm="SpecAlgo",
        update_rule="see spec",
        proof_sketch=f"See structured spec: {spec_file}",
        archetype="B",
        target_file=str(target_file),
        skip_to_agent9=True,
        spec_file=str(spec_file),
    )

    assert "\"algorithm\": \"SpecAlgo\"" in captured["plan"]
    assert f"See structured spec: {spec_file}" not in captured["plan"]


def test_run_skip_to_agent9_requires_existing_target(tmp_path):
    missing_target = tmp_path / "Missing.lean"

    with pytest.raises(FileNotFoundError, match="requires an existing target file"):
        main_mod.run(
            algorithm="FooAlgo",
            update_rule="w_{t+1} = w_t - g_t",
            proof_sketch="Use the existing scaffold",
            archetype="B",
            target_file=str(missing_target),
            skip_to_agent9=True,
        )


def test_phase3_skip_to_agent9_avoids_agent2_guidance_and_runs_agent9(monkeypatch, tmp_path):
    target_file = tmp_path / "Existing.lean"
    target_file.write_text("theorem t : True := by\n  sorry\n", encoding="utf-8")
    observed: dict[str, object] = {}

    class _DummyAgent:
        def __init__(self, role: str, extra_files=None):
            self.role = role
            self.extra_files = extra_files or []
            self.messages: list[dict] = []
            self._file_context = ""

        def call(self, _prompt: str) -> str:
            return "{}"

    class _FakeRegistry:
        def __init__(self):
            self._tools = {}

        def register_default_tools(self) -> None:
            pass

        def register_readonly_tools(self) -> None:
            pass

        def call(self, tool_name: str, *args, **kwargs):
            if tool_name == "run_lean_verify":
                return {"exit_code": 0, "sorry_count": 0, "errors": []}
            if tool_name == "run_repo_verify":
                return {"exit_code": 0}
            if tool_name == "overwrite_file":
                return {"changed": True}
            raise AssertionError(f"Unexpected tool call: {tool_name}")

    monkeypatch.setattr(phase3_mod, "Agent", _DummyAgent)
    monkeypatch.setattr(phase3_mod, "ToolRegistry", _FakeRegistry)
    monkeypatch.setattr(
        phase3_mod,
        "_call_agent2_with_tools",
        lambda *_args, **_kwargs: pytest.fail("skip_to_agent9 must not call Agent2 before Agent9"),
    )
    monkeypatch.setattr(phase3_mod, "_extract_imported_algo_sigs", lambda _target: "")
    monkeypatch.setattr(phase3_mod, "_file_hash", lambda _target: "hash")

    def _fake_agent9(target_file_arg, guidance, algo_name, *, verify_state=None):
        observed["agent9_target"] = target_file_arg
        observed["guidance"] = guidance
        observed["algo_name"] = algo_name
        observed["verify_state"] = verify_state
        return {"theorems": [{"name": "t"}], "recommended_order": ["t"]}

    def _fake_agent8(agent2, target_file_arg, guidance, last_errors, **kwargs):
        observed["agent8_agent2_role"] = agent2.role
        observed["agent8_target"] = target_file_arg
        observed["agent8_guidance"] = guidance
        observed["agent8_last_errors"] = last_errors
        observed["agent8_plan"] = kwargs.get("agent9_plan")
        return True, guidance, last_errors

    monkeypatch.setattr(phase3_agent9, "run_agent9_plan", _fake_agent9)
    monkeypatch.setattr(phase3_agent8, "run_agent8_loop", _fake_agent8)

    success, attempts, errors, audit = phase3_mod.phase3_prove(
        None,
        str(target_file),
        "[STRICT SKIP-TO-AGENT9 GUIDANCE]\nUse the existing file.",
        skip_to_agent9=True,
        max_retries=1,
    )

    assert success is True
    assert attempts == 0
    assert errors == ""
    assert observed["agent9_target"] == str(target_file)
    assert observed["algo_name"] == target_file.stem
    assert observed["agent8_agent2_role"] == "planner"
    assert observed["agent8_target"] == str(target_file)
    assert observed["agent8_plan"] == {"theorems": [{"name": "t"}], "recommended_order": ["t"]}
    assert observed["verify_state"] == {"exit_code": 0, "sorry_count": 0, "errors": []}
    assert isinstance(audit["execution_history"], list)
