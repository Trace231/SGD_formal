"""Tests for Agent3 APOLLO-style search kernel."""

from __future__ import annotations

from pathlib import Path

from orchestrator import phase3_agent3 as a3


def _mk_target(tmp_path: Path) -> str:
    p = tmp_path / "SubgradientMethod.lean"
    p.write_text("import Main\ntheorem t : True := by\n  trivial\n", encoding="utf-8")
    return str(p)


def test_build_apollo_verify_callable_falls_back_from_session(monkeypatch):
    import orchestrator.apollo_sorrify as sor

    class _BadSession:
        def verify(self, _code, *, env=None):  # noqa: ARG002
            raise RuntimeError("session desync")

    monkeypatch.setattr(
        sor,
        "verify_with_apollo",
        lambda **_: {"pass": True, "complete": True, "errors": [], "warnings": []},
    )

    verifier = sor.build_apollo_verify_callable(session=_BadSession(), header_env_id=7)
    out = verifier("theorem t : True := by\n  trivial\n")
    assert out["pass"] is True
    assert out["complete"] is True


def test_search_kernel_early_stops_on_clean_candidate(monkeypatch, tmp_path):
    target = _mk_target(tmp_path)
    monkeypatch.setattr(a3, "AGENT3_SEARCH_ENABLED", True)
    monkeypatch.setattr(a3, "AGENT3_CANDIDATE_COUNT", 3)
    monkeypatch.setattr(a3, "AGENT3_RECURSION_DEPTH", 0)
    monkeypatch.setattr(a3, "AGENT3_NO_IMPROVEMENT_WINDOW", 2)

    import orchestrator.tools as tools_mod
    import orchestrator.apollo_sorrify as sor
    import orchestrator.repl_adapter as repl_mod

    monkeypatch.setattr(
        tools_mod,
        "run_lean_verify",
        lambda _path: {"exit_code": 1, "sorry_count": 1, "error_count": 3, "errors": ["e"]},
    )
    monkeypatch.setattr(sor, "build_apollo_verify_callable", lambda: (lambda _code: {"pass": False, "complete": False, "errors": []}))
    monkeypatch.setattr(sor, "apply_syntax_correction", lambda code: (code, {"ok": True, "changed": False}))
    monkeypatch.setattr(sor, "apply_sorrify", lambda code, _v: (code, {"ok": True, "changed": False}))
    monkeypatch.setattr(sor, "apply_hint_repair", lambda code, _v: (code, {"ok": True, "changed": False}))
    
    class _SessFail:
        def __init__(self, **_kwargs):
            raise RuntimeError("session unavailable")

    monkeypatch.setattr(repl_mod, "ReplSession", _SessFail)

    calls: list[int] = []

    def _fake_single(*_args, **kwargs):
        idx = int(kwargs["candidate_index"])
        calls.append(idx)
        if idx == 2:
            return {"exit_code": 0, "sorry_count": 0, "errors": "", "verify_time": 0.02}
        return {"exit_code": 1, "sorry_count": 2, "errors": "err", "verify_time": 0.01}

    out = a3.run_agent3_search_kernel(
        target,
        "plan",
        "prompt",
        None,
        run_single_candidate=_fake_single,
    )
    assert out["exit_code"] == 0
    assert out["sorry_count"] == 0
    assert out["best_candidate_reason"] == "clean_candidate_early_stop"
    assert "search_timing" in out
    assert "candidate_timings" in out
    # Parallel mode schedules all candidate workers in the round.
    assert sorted(calls) == [1, 2, 3]


def test_search_kernel_recursion_returns_failure_contract(monkeypatch, tmp_path):
    target = _mk_target(tmp_path)
    monkeypatch.setattr(a3, "AGENT3_SEARCH_ENABLED", True)
    monkeypatch.setattr(a3, "AGENT3_CANDIDATE_COUNT", 1)
    monkeypatch.setattr(a3, "AGENT3_RECURSION_DEPTH", 1)
    monkeypatch.setattr(a3, "AGENT3_NO_IMPROVEMENT_WINDOW", 1)

    import orchestrator.tools as tools_mod
    import orchestrator.apollo_sorrify as sor
    import orchestrator.apollo_repair as rep
    import orchestrator.repl_adapter as repl_mod

    monkeypatch.setattr(
        tools_mod,
        "run_lean_verify",
        lambda _path: {"exit_code": 1, "sorry_count": 3, "error_count": 3, "errors": ["unknown identifier foo"]},
    )
    monkeypatch.setattr(sor, "build_apollo_verify_callable", lambda: (lambda _code: {"pass": False, "complete": False, "errors": []}))
    monkeypatch.setattr(sor, "apply_syntax_correction", lambda code: (code, {"ok": True, "changed": False}))
    monkeypatch.setattr(sor, "apply_sorrify", lambda code, _v: (code, {"ok": True, "changed": False}))
    monkeypatch.setattr(sor, "apply_hint_repair", lambda code, _v: (code, {"ok": True, "changed": False}))
    monkeypatch.setattr(
        sor,
        "extract_sublemmas",
        lambda _code, _v: (
            ["lemma t_sub1 : True := by sorry"],
            {"ok": True, "count": 1, "statements": ["lemma t_sub1 : True := by sorry"]},
        ),
    )
    monkeypatch.setattr(
        rep,
        "build_subproblem_graph",
        lambda **kwargs: [{
            "id": "sp-01-interface",
            "kind": "interface_signature",
            "target": f"decl:{len(kwargs.get('sublemma_statements', []))}",
            "evidence": "unknown identifier",
        }],
    )
    monkeypatch.setattr(
        rep,
        "classify_failure_kind",
        lambda _errors: ("interface_failure", "reason", "snippet"),
    )

    class _SessFail:
        def __init__(self, **_kwargs):
            raise RuntimeError("session unavailable")

    monkeypatch.setattr(repl_mod, "ReplSession", _SessFail)

    def _fake_single(*_args, **_kwargs):
        return {"exit_code": 1, "sorry_count": 3, "errors": "unknown identifier foo", "verify_time": 0.03}

    out = a3.run_agent3_search_kernel(
        target,
        "plan",
        "prompt",
        None,
        run_single_candidate=_fake_single,
        error_subtype="declaration_api_mismatch",
    )
    assert out["exit_code"] == 1
    assert out["failure_kind"] == "interface_failure"
    assert "best_failed_candidate_summary" in out
    assert out["best_failed_candidate_summary"]["extracted_sublemmas"] == [
        "lemma t_sub1 : True := by sorry"
    ]
    assert isinstance(out.get("budget_remaining", {}), dict)
    assert out["blocked_state"]["failure_kind"] == "interface_failure"
    assert "candidate_budget_total" in out["blocked_state"]


def test_tactic_probe_early_stops_clean(monkeypatch, tmp_path):
    target = _mk_target(tmp_path)
    monkeypatch.setattr(a3, "AGENT3_SEARCH_ENABLED", True)
    monkeypatch.setattr(a3, "AGENT3_CANDIDATE_COUNT", 3)
    monkeypatch.setattr(a3, "AGENT3_RECURSION_DEPTH", 0)
    monkeypatch.setattr(a3, "AGENT3_NO_IMPROVEMENT_WINDOW", 2)
    monkeypatch.setattr(a3, "AGENT3_TACTIC_PROBE_ENABLED", True)
    monkeypatch.setattr(a3, "AGENT3_TACTIC_PROBE_STR", "try trivial")

    import orchestrator.tools as tools_mod
    import orchestrator.apollo_sorrify as sor
    import orchestrator.repl_adapter as repl_mod

    monkeypatch.setattr(
        tools_mod,
        "run_lean_verify",
        lambda _path: {"exit_code": 1, "sorry_count": 1, "error_count": 1, "errors": ["e"]},
    )
    monkeypatch.setattr(
        sor,
        "build_apollo_verify_callable",
        lambda **_: (lambda _code: {"pass": False, "complete": False, "errors": []}),
    )
    monkeypatch.setattr(sor, "apply_syntax_correction", lambda code: (code, {"ok": True, "changed": False}))
    monkeypatch.setattr(sor, "apply_sorrify", lambda code, _v: (code, {"ok": True, "changed": False}))
    monkeypatch.setattr(sor, "apply_hint_repair", lambda code, _v: (code, {"ok": True, "changed": False}))
    monkeypatch.setattr(repl_mod, "_extract_header_lines", lambda _code: "import Main")

    class _Sess:
        def __init__(self, **_kwargs):
            pass

        def prime_header(self, _header):
            return 11

        def verify(self, _code, *, env=None):
            assert env == 11
            return {
                "pass": True,
                "complete": True,
                "errors": [],
                "warnings": [],
                "errors_text": [],
                "warnings_text": [],
                "verify_time": 0.01,
                "source_sorry_count": 0,
                "sorry_declarations": 0,
                "blocked_sorry_count": 0,
            }

        def close(self):
            return None

    monkeypatch.setattr(repl_mod, "ReplSession", _Sess)

    llm_calls = {"n": 0}

    def _fake_single(*_args, **_kwargs):
        llm_calls["n"] += 1
        return {"exit_code": 1, "sorry_count": 3, "errors": "err", "verify_time": 0.01}

    out = a3.run_agent3_search_kernel(
        target,
        "plan",
        "prompt",
        None,
        run_single_candidate=_fake_single,
    )
    assert out["best_candidate_reason"] == "tactic_probe_clean"
    assert out["candidate_id"].endswith("probe")
    assert out["search_timing"]["probe_ms"] >= 0
    assert llm_calls["n"] == 0


def test_tactic_probe_does_not_early_stop_when_incomplete(monkeypatch, tmp_path):
    target = _mk_target(tmp_path)
    monkeypatch.setattr(a3, "AGENT3_SEARCH_ENABLED", True)
    monkeypatch.setattr(a3, "AGENT3_CANDIDATE_COUNT", 2)
    monkeypatch.setattr(a3, "AGENT3_RECURSION_DEPTH", 0)
    monkeypatch.setattr(a3, "AGENT3_NO_IMPROVEMENT_WINDOW", 1)
    monkeypatch.setattr(a3, "AGENT3_TACTIC_PROBE_ENABLED", True)
    monkeypatch.setattr(a3, "AGENT3_TACTIC_PROBE_STR", "try trivial")

    import orchestrator.tools as tools_mod
    import orchestrator.apollo_sorrify as sor
    import orchestrator.repl_adapter as repl_mod

    monkeypatch.setattr(
        tools_mod,
        "run_lean_verify",
        lambda _path: {"exit_code": 1, "sorry_count": 1, "error_count": 1, "errors": ["e"]},
    )
    monkeypatch.setattr(
        sor,
        "build_apollo_verify_callable",
        lambda **_: (lambda _code: {"pass": False, "complete": False, "errors": []}),
    )
    monkeypatch.setattr(sor, "apply_syntax_correction", lambda code: (code, {"ok": True, "changed": False}))
    monkeypatch.setattr(sor, "apply_sorrify", lambda code, _v: (code, {"ok": True, "changed": False}))
    monkeypatch.setattr(sor, "apply_hint_repair", lambda code, _v: (code, {"ok": True, "changed": False}))
    monkeypatch.setattr(repl_mod, "_extract_header_lines", lambda _code: "import Main")

    class _Sess:
        def __init__(self, **_kwargs):
            pass

        def prime_header(self, _header):
            return 11

        def verify(self, _code, *, env=None):
            assert env == 11
            return {
                "pass": True,
                "complete": False,
                "errors": [],
                "warnings": [{"severity": "warning", "data": "failed probe quality gate"}],
                "errors_text": [],
                "warnings_text": ["probe: warning: failed probe quality gate"],
                "verify_time": 0.01,
                "source_sorry_count": 0,
                "sorry_declarations": 0,
                "blocked_sorry_count": 0,
            }

        def close(self):
            return None

    monkeypatch.setattr(repl_mod, "ReplSession", _Sess)

    llm_calls = {"n": 0}

    def _fake_single(*_args, **_kwargs):
        llm_calls["n"] += 1
        return {"exit_code": 1, "sorry_count": 2, "errors": "err", "verify_time": 0.01}

    out = a3.run_agent3_search_kernel(
        target,
        "plan",
        "prompt",
        None,
        run_single_candidate=_fake_single,
    )
    assert out["best_candidate_reason"] != "tactic_probe_clean"
    assert llm_calls["n"] > 0


def test_strategy_injection_varies_by_index(monkeypatch, tmp_path):
    target = _mk_target(tmp_path)
    monkeypatch.setattr(a3, "AGENT3_SEARCH_ENABLED", True)
    monkeypatch.setattr(a3, "AGENT3_CANDIDATE_COUNT", 3)
    monkeypatch.setattr(a3, "AGENT3_RECURSION_DEPTH", 0)
    monkeypatch.setattr(a3, "AGENT3_NO_IMPROVEMENT_WINDOW", 2)
    monkeypatch.setattr(a3, "AGENT3_TACTIC_PROBE_ENABLED", False)
    monkeypatch.setattr(a3, "AGENT3_TACTIC_STRATEGIES", ["s1", "s2", "s3"])

    import orchestrator.tools as tools_mod
    import orchestrator.apollo_sorrify as sor
    import orchestrator.repl_adapter as repl_mod

    monkeypatch.setattr(
        tools_mod,
        "run_lean_verify",
        lambda _path: {"exit_code": 1, "sorry_count": 3, "error_count": 3, "errors": ["e"]},
    )
    monkeypatch.setattr(
        sor,
        "build_apollo_verify_callable",
        lambda **_: (lambda _code: {"pass": False, "complete": False, "errors": []}),
    )
    monkeypatch.setattr(sor, "apply_syntax_correction", lambda code: (code, {"ok": True, "changed": False}))
    monkeypatch.setattr(sor, "apply_sorrify", lambda code, _v: (code, {"ok": True, "changed": False}))
    monkeypatch.setattr(sor, "apply_hint_repair", lambda code, _v: (code, {"ok": True, "changed": False}))

    class _SessFail:
        def __init__(self, **_kwargs):
            raise RuntimeError("session unavailable")

    monkeypatch.setattr(repl_mod, "ReplSession", _SessFail)

    seen_prompts: dict[int, str] = {}

    def _fake_single(*args, **kwargs):
        idx = int(kwargs["candidate_index"])
        seen_prompts[idx] = str(args[2])
        return {"exit_code": 1, "sorry_count": 2, "errors": "err", "verify_time": 0.01}

    out = a3.run_agent3_search_kernel(
        target,
        "plan",
        "prompt",
        None,
        run_single_candidate=_fake_single,
    )
    assert out["exit_code"] == 1
    assert "preferred_strategy: s1" in seen_prompts[1]
    assert "preferred_strategy: s2" in seen_prompts[2]
    assert "preferred_strategy: s3" in seen_prompts[3]


def test_patch_guard_mode_keeps_transactional_api_shape_to_single_candidate(monkeypatch, tmp_path):
    target = _mk_target(tmp_path)
    monkeypatch.setattr(a3, "AGENT3_SEARCH_ENABLED", True)
    monkeypatch.setattr(a3, "AGENT3_CANDIDATE_COUNT", 3)
    monkeypatch.setattr(a3, "AGENT3_RECURSION_DEPTH", 0)
    monkeypatch.setattr(a3, "AGENT3_NO_IMPROVEMENT_WINDOW", 1)
    monkeypatch.setattr(a3, "AGENT3_TACTIC_PROBE_ENABLED", False)

    import orchestrator.tools as tools_mod
    import orchestrator.apollo_sorrify as sor
    import orchestrator.repl_adapter as repl_mod

    monkeypatch.setattr(
        tools_mod,
        "run_lean_verify",
        lambda _path: {"exit_code": 1, "sorry_count": 2, "error_count": 2, "errors": ["e"]},
    )
    monkeypatch.setattr(
        sor,
        "build_apollo_verify_callable",
        lambda **_: (lambda _code: {"pass": False, "complete": False, "errors": []}),
    )
    monkeypatch.setattr(sor, "apply_syntax_correction", lambda code: (code, {"ok": True, "changed": False}))
    monkeypatch.setattr(sor, "apply_sorrify", lambda code, _v: (code, {"ok": True, "changed": False}))
    monkeypatch.setattr(sor, "apply_hint_repair", lambda code, _v: (code, {"ok": True, "changed": False}))

    class _SessFail:
        def __init__(self, **_kwargs):
            raise RuntimeError("session unavailable")

    monkeypatch.setattr(repl_mod, "ReplSession", _SessFail)

    calls: list[int] = []

    def _fake_single(*_args, **kwargs):
        calls.append(int(kwargs["candidate_index"]))
        return {"exit_code": 1, "sorry_count": 2, "errors": "err", "verify_time": 0.01}

    out = a3.run_agent3_search_kernel(
        target,
        "plan",
        "prompt",
        None,
        patch_guard_mode=True,
        search_allowed=True,
        run_single_candidate=_fake_single,
        error_subtype="proof_api_mismatch",
    )
    assert out["exit_code"] == 1
    assert out["execution_profile"] == "api_shape"
    assert sorted(calls) == [1]


def test_search_kernel_records_candidate_metrics(monkeypatch, tmp_path):
    target = _mk_target(tmp_path)
    monkeypatch.setattr(a3, "AGENT3_SEARCH_ENABLED", True)
    monkeypatch.setattr(a3, "AGENT3_CANDIDATE_COUNT", 1)
    monkeypatch.setattr(a3, "AGENT3_RECURSION_DEPTH", 0)
    monkeypatch.setattr(a3, "AGENT3_NO_IMPROVEMENT_WINDOW", 1)
    monkeypatch.setattr(a3, "AGENT3_TACTIC_PROBE_ENABLED", False)

    import orchestrator.tools as tools_mod
    import orchestrator.apollo_sorrify as sor
    import orchestrator.repl_adapter as repl_mod

    monkeypatch.setattr(
        tools_mod,
        "run_lean_verify",
        lambda _path: {
            "exit_code": 1,
            "sorry_count": 2,
            "error_count": 2,
            "errors": ["e"],
            "verify_wall_ms": 12,
        },
    )
    monkeypatch.setattr(
        sor,
        "build_apollo_verify_callable",
        lambda **_: (lambda _code: {"pass": False, "complete": False, "errors": []}),
    )
    monkeypatch.setattr(sor, "apply_syntax_correction", lambda code: (code, {"ok": True, "changed": False}))
    monkeypatch.setattr(sor, "apply_sorrify", lambda code, _v: (code, {"ok": True, "changed": False}))
    monkeypatch.setattr(sor, "apply_hint_repair", lambda code, _v: (code, {"ok": True, "changed": False}))

    class _SessFail:
        def __init__(self, **_kwargs):
            raise RuntimeError("session unavailable")

    monkeypatch.setattr(repl_mod, "ReplSession", _SessFail)

    def _fake_single(*_args, **_kwargs):
        return {
            "exit_code": 1,
            "sorry_count": 2,
            "errors": "err",
            "verify_time": 0.01,
            "candidate_metrics": {
                "llm_ms": 5,
                "tool_ms": 7,
                "verify_ms": 11,
                "candidate_total_ms": 30,
            },
        }

    out = a3.run_agent3_search_kernel(
        target,
        "plan",
        "prompt",
        None,
        run_single_candidate=_fake_single,
        repair_unit="block_restructure",
        error_subtype="proof_tactic_failure",
    )
    assert out["candidate_timings"]
    assert out["candidate_timings"][0]["candidate_total_ms"] == 30
    assert out["search_timing"]["candidate_batch_ms"] >= 0


def test_parallel_candidates_receive_distinct_subproblem_focus(monkeypatch, tmp_path):
    target = _mk_target(tmp_path)
    monkeypatch.setattr(a3, "AGENT3_SEARCH_ENABLED", True)
    monkeypatch.setattr(a3, "AGENT3_CANDIDATE_COUNT", 2)
    monkeypatch.setattr(a3, "AGENT3_RECURSION_DEPTH", 0)
    monkeypatch.setattr(a3, "AGENT3_NO_IMPROVEMENT_WINDOW", 1)
    monkeypatch.setattr(a3, "AGENT3_TACTIC_PROBE_ENABLED", False)
    monkeypatch.setattr(a3, "AGENT3_TACTIC_STRATEGIES", ["s1", "s2"])

    import orchestrator.tools as tools_mod
    import orchestrator.apollo_sorrify as sor
    import orchestrator.apollo_repair as rep
    import orchestrator.repl_adapter as repl_mod

    monkeypatch.setattr(
        tools_mod,
        "run_lean_verify",
        lambda _path: {"exit_code": 1, "sorry_count": 2, "error_count": 2, "errors": ["calc failed"]},
    )
    monkeypatch.setattr(
        sor,
        "build_apollo_verify_callable",
        lambda **_: (lambda _code: {"pass": False, "complete": False, "errors": []}),
    )
    monkeypatch.setattr(sor, "apply_syntax_correction", lambda code: (code, {"ok": True, "changed": False}))
    monkeypatch.setattr(sor, "apply_sorrify", lambda code, _v: (code, {"ok": True, "changed": False}))
    monkeypatch.setattr(sor, "apply_hint_repair", lambda code, _v: (code, {"ok": True, "changed": False}))
    monkeypatch.setattr(
        sor,
        "extract_sublemmas",
        lambda _code, _v: (
            ["lemma sub1 : True := by sorry", "lemma sub2 : True := by sorry"],
            {"ok": True, "count": 2, "statements": ["lemma sub1 : True := by sorry", "lemma sub2 : True := by sorry"]},
        ),
    )
    monkeypatch.setattr(
        rep,
        "build_subproblem_graph",
        lambda **_kwargs: [
            {"id": "sp-01", "kind": "proof_state_sublemma", "target": "sublemma_1", "evidence": "lemma sub1"},
            {"id": "sp-02", "kind": "proof_state_sublemma", "target": "sublemma_2", "evidence": "lemma sub2"},
        ],
    )

    class _SessFail:
        def __init__(self, **_kwargs):
            raise RuntimeError("session unavailable")

    monkeypatch.setattr(repl_mod, "ReplSession", _SessFail)

    seen_prompts: dict[int, str] = {}

    def _fake_single(*args, **kwargs):
        seen_prompts[int(kwargs["candidate_index"])] = str(args[2])
        return {"exit_code": 1, "sorry_count": 2, "errors": "err", "verify_time": 0.01}

    out = a3.run_agent3_search_kernel(
        target,
        "plan",
        "prompt",
        None,
        run_single_candidate=_fake_single,
        repair_unit="block_restructure",
        error_subtype="proof_tactic_failure",
    )
    assert out["exit_code"] == 1
    assert "[Bounded Subproblem Focus]" in seen_prompts[1]
    assert "sublemma_1" in seen_prompts[1]
    assert "sublemma_2" in seen_prompts[2]


def test_execution_profile_uses_single_candidate_for_transactional_api_shape(monkeypatch):
    monkeypatch.setitem(a3.RETRY_LIMITS, "AGENT8_AGENT3_SAMPLE_CANDIDATES", 4)
    profile = a3._build_agent3_execution_profile(
        base_candidate_count=3,
        patch_guard_mode=True,
        search_allowed=True,
        error_subtype="proof_api_mismatch",
        repair_unit="local_patch",
        compile_first_mode=True,
    )
    assert profile.name == "api_shape"
    assert profile.candidate_count == 1


def test_execution_profile_widens_candidates_for_block_restructure(monkeypatch):
    monkeypatch.setitem(a3.RETRY_LIMITS, "AGENT8_AGENT3_SAMPLE_CANDIDATES", 4)
    monkeypatch.setitem(a3.RETRY_LIMITS, "AGENT8_AGENT3_SAMPLE_MAX_CANDIDATES", 4)
    profile = a3._build_agent3_execution_profile(
        base_candidate_count=2,
        patch_guard_mode=False,
        search_allowed=True,
        error_subtype="proof_api_mismatch",
        repair_unit="block_restructure",
        compile_first_mode=True,
    )
    assert profile.name == "block_restructure"
    assert profile.candidate_count == 4


def test_midcheck_handoff_triggers_for_sampled_search_mode():
    assert a3._midcheck_should_handoff_to_search(
        {
            "action": "agent3_tactical",
            "repair_unit": "block_restructure",
            "agent3_execution_mode": "sampled_search",
        }
    )
    assert not a3._midcheck_should_handoff_to_search(
        {
            "action": "agent3_tactical",
            "repair_unit": "local_patch",
            "agent3_execution_mode": "transactional_local_patch",
        }
    )
