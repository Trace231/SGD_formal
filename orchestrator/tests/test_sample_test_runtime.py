from __future__ import annotations

import json
from pathlib import Path
from types import SimpleNamespace

from orchestrator import main as main_mod
from orchestrator.audit_logger import AuditLogger
from orchestrator.sample_test_cleanup import apply_sample_test_cleanup
from orchestrator.sample_test_watch import (
    build_analysis_markdown,
    classify_labels,
    parse_agent8_decision,
    parse_agent9_status,
)
from orchestrator.tools import search_codebase


class _FakeAudit:
    def start_run(self, _algorithm: str) -> str:
        return "test-run"

    def set_phase(self, _phase: int) -> None:
        pass

    def add_phase3_data(self, *_args, **_kwargs) -> None:
        pass

    def finish_run(self, *_args, **_kwargs) -> None:
        pass

    def log_event(self, *_args, **_kwargs) -> None:
        pass


def test_audit_logger_writes_context_journal(tmp_path):
    AuditLogger.reset()
    audit = AuditLogger.get()
    audit.context_journal_enabled = True
    audit.context_journal_dir = tmp_path
    run_id = audit.start_run("sorry")
    audit.log_agent_call(
        "strategy_planner",
        "prompt body",
        "reply body",
        prompt_full="prompt body",
        reply_full="reply body",
        backend="codex",
        llm_transport="sdk",
        sdk_model="qwen3-max-2026-01-23",
        target_file="Algorithms/sorry.lean",
        context_mode="minimal",
    )
    journal = tmp_path / run_id / "strategy_planner.jsonl"
    payload = json.loads(journal.read_text(encoding="utf-8").splitlines()[0])
    assert payload["entry_type"] == "agent_call"
    assert payload["target_file"] == "Algorithms/sorry.lean"
    assert payload["context_mode"] == "minimal"
    assert payload["prompt_full"] == "prompt body"


def test_apply_sample_test_cleanup_rewrites_and_deletes(tmp_path):
    (tmp_path / "docs").mkdir()
    (tmp_path / "Algorithms").mkdir()
    (tmp_path / "orchestrator" / "sample_test" / "templates").mkdir(parents=True)
    (tmp_path / "docs" / "CATALOG.md").write_text("old catalog", encoding="utf-8")
    (tmp_path / "docs" / "APOLLO_ABLATION_GUIDE.md").write_text(
        "subgradient_single.jsonl\nAlgorithms/SubgradientMethod_scaffold.lean\n",
        encoding="utf-8",
    )
    (tmp_path / "Algorithms" / "test.lean").write_text("theorem t : True := by trivial\n", encoding="utf-8")
    (tmp_path / "orchestrator" / "sample_test" / "templates" / "CATALOG.md").write_text("new catalog", encoding="utf-8")
    spec = {
        "rewrite_files": [{"path": "docs/CATALOG.md", "template": "orchestrator/sample_test/templates/CATALOG.md"}],
        "regex_replacements": [
            {
                "path": "docs/APOLLO_ABLATION_GUIDE.md",
                "pattern": "subgradient_single\\.jsonl",
                "replacement": "sample_single.jsonl",
            }
        ],
        "delete_globs": ["Algorithms/test.lean"],
    }
    spec_path = tmp_path / "orchestrator" / "sample_test" / "cleanup_spec.json"
    spec_path.write_text(json.dumps(spec), encoding="utf-8")

    summary = apply_sample_test_cleanup(spec_path, project_root=tmp_path)
    assert (tmp_path / "docs" / "CATALOG.md").read_text(encoding="utf-8") == "new catalog"
    assert "sample_single.jsonl" in (tmp_path / "docs" / "APOLLO_ABLATION_GUIDE.md").read_text(encoding="utf-8")
    assert not (tmp_path / "Algorithms" / "test.lean").exists()
    assert summary["rewrite_files"] == ["docs/CATALOG.md"]


def test_search_codebase_excludes_runtime_artifacts(monkeypatch, tmp_path):
    (tmp_path / "src").mkdir()
    (tmp_path / "orchestrator" / "watch_logs").mkdir(parents=True)
    (tmp_path / "src" / "Keep.lean").write_text("theorem target_keep : True := by trivial\n", encoding="utf-8")
    (tmp_path / "orchestrator" / "watch_logs" / "Leak.lean").write_text("theorem target_leak : True := by trivial\n", encoding="utf-8")

    import orchestrator.tools as tools_mod

    monkeypatch.setattr(tools_mod, "PROJECT_ROOT", tmp_path)
    monkeypatch.setattr(tools_mod, "RUNTIME_ARTIFACT_EXCLUDE_GLOBS", ("orchestrator/watch_logs/**",))
    result = search_codebase("target_", file_glob="*.lean")
    files = {m["file"] for m in result["matches"]}
    assert "src/Keep.lean" in files
    assert "orchestrator/watch_logs/Leak.lean" not in files


def test_watch_helpers_parse_and_analyze():
    captured = """
    [Agent9] Parse attempt 1/3 failed (json) — retrying.
    [Agent9] Plan ready: 3 theorem(s), order: ['a', 'b']
    [Agent8] tick=4 action=agent7_signature subtype=declaration_api_mismatch repair_unit=local_patch sig=Foo.lean:10
    [Agent8] reason: declaration-zone issues belong to Agent7
    """
    a8 = parse_agent8_decision(captured)
    a9 = parse_agent9_status(captured)
    samples = [
        {
            "latest_agent8_decision": a8,
            "latest_agent9_status": a9,
            "latest_compile_health": {"healthy": False},
            "sorry_header_integrity": True,
            "latest_journal_entries": {
                "strategy_planner": {"prompt_len": 100},
                "decision_hub": {"canonical_error_signature": "Foo.lean:10:boom"},
            },
        }
        for _ in range(10)
    ]
    labels = classify_labels(samples)
    report = build_analysis_markdown("run1", samples)
    assert a8["action"] == "agent7_signature"
    assert a9["state"] == "plan_ready"
    assert "infra_block" in labels
    assert "Main bottleneck" in report


def test_main_skips_phase4_when_disabled(monkeypatch, tmp_path):
    target_file = tmp_path / "Existing.lean"
    target_file.write_text("theorem t : True := by\n  trivial\n", encoding="utf-8")
    captured = {"phase4_called": False, "phase5_new_tricks": None}

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
    monkeypatch.setattr(main_mod, "phase1_generate_prompt", lambda *_args, **_kwargs: "prompt")
    monkeypatch.setattr(
        main_mod,
        "phase2_plan_and_approve",
        lambda *_args, **_kwargs: ("plan", SimpleNamespace(messages=[]), SimpleNamespace(messages=[])),
    )
    monkeypatch.setattr(main_mod, "phase3_prove", lambda *_args, **_kwargs: (True, 0, "", {"execution_history": [], "attempt_failures": [], "estimated_token_consumption": 0, "retry_count": 0}))
    monkeypatch.setattr(main_mod, "phase4_persist", lambda *_args, **_kwargs: captured.__setitem__("phase4_called", True))
    monkeypatch.setattr(
        main_mod,
        "phase5_finalize",
        lambda _algorithm, new_tricks, **_kwargs: captured.__setitem__("phase5_new_tricks", new_tricks),
    )
    monkeypatch.setattr(main_mod, "DISABLE_PHASE4_PERSISTENCE", True)

    main_mod.run(
        algorithm="FooAlgo",
        update_rule="w_{t+1} = w_t - g_t",
        proof_sketch="Use the scaffold",
        archetype="B",
        target_file=str(target_file),
        skip_to_agent9=False,
    )

    assert captured["phase4_called"] is False
    assert captured["phase5_new_tricks"] == 0
