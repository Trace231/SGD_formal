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

    monkeypatch.setattr(
        tools_mod,
        "run_lean_verify",
        lambda _path: {"exit_code": 1, "sorry_count": 1, "error_count": 3, "errors": ["e"]},
    )
    monkeypatch.setattr(sor, "build_apollo_verify_callable", lambda: (lambda _code: {"pass": False, "complete": False, "errors": []}))
    monkeypatch.setattr(sor, "apply_syntax_correction", lambda code: (code, {"ok": True, "changed": False}))
    monkeypatch.setattr(sor, "apply_sorrify", lambda code, _v: (code, {"ok": True, "changed": False}))
    monkeypatch.setattr(sor, "apply_hint_repair", lambda code, _v: (code, {"ok": True, "changed": False}))

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
    assert llm_calls["n"] == 0


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
