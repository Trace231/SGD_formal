"""Regression checks for the deterministic Agent8 router."""

from orchestrator.phase3_agent8 import (
    _REPAIR_UNIT_BLOCK_RESTRUCTURE,
    _REPAIR_UNIT_LOCAL_PATCH,
    _REPAIR_UNIT_STATEMENT_GAP,
    _SUBTYPE_DECLARATION_API_MISMATCH,
    _SUBTYPE_DECLARATION_SYNTAX_FAILURE,
    _SUBTYPE_PROOF_API_MISMATCH,
    _SUBTYPE_PROOF_TACTIC_FAILURE,
    _SUBTYPE_STRATEGY_MISMATCH,
    _build_agent9_theorem_context,
    _canonical_error_signature,
    _classify_error_subtype,
    _coerce_errors_text,
    _error_count_from_verify,
    _is_structural_error,
    _prefer_agent3_search_owner,
    _resolve_decision_prompt,
    _route_for_subtype,
    run_agent8_loop,
)


def test_structural_vs_tactical_classification_regression():
    assert _is_structural_error("Application type mismatch in declaration zone", "")
    assert _is_structural_error("unknown identifier `integral_nonneg`", "")
    assert not _is_structural_error("tactic 'linarith' failed", "no goals solved by linarith")
    assert not _is_structural_error(
        "Application type mismatch",
        "have h : _ := by\n  exact ?_\napplication type mismatch",
    )


def test_classify_integral_api_in_proof_body():
    errors = (
        "Algorithms/Foo.lean:42:3: error: type mismatch\n"
        "  integral_nonneg applied to 3 arguments but expects 2\n"
        "  tactic exact failed"
    )
    assert _classify_error_subtype(errors) == _SUBTYPE_PROOF_API_MISMATCH


def test_classify_unknown_identifier_is_declaration():
    errors = "Foo.lean:10:0: error: unknown identifier 'myLemma'"
    assert _classify_error_subtype(errors) == _SUBTYPE_DECLARATION_API_MISMATCH


def test_classify_unexpected_token_is_declaration_syntax_failure():
    errors = "Foo.lean:7:18: error: unexpected token '*'; expected '}'"
    assert _classify_error_subtype(errors) == _SUBTYPE_DECLARATION_SYNTAX_FAILURE


def test_classify_tactic_failure_no_api():
    errors = "Baz.lean:55:6: error: tactic 'linarith' failed\n  no goals solved"
    assert _classify_error_subtype(errors) == _SUBTYPE_PROOF_TACTIC_FAILURE


def test_classify_strategy_mismatch_from_history():
    history = [
        {"sorry_before": 1, "sorry_after": 1, "canonical_error_signature": "Foo.lean:10:unsolved goals"},
        {"sorry_before": 1, "sorry_after": 1, "canonical_error_signature": "Foo.lean:10:unsolved goals"},
        {"sorry_before": 1, "sorry_after": 1, "canonical_error_signature": "Foo.lean:10:unsolved goals"},
    ]
    result = _classify_error_subtype(
        "Foo.lean:10:2: error: tactic 'ring' failed\n  unsolved goals",
        decision_history=history,
    )
    assert result == _SUBTYPE_STRATEGY_MISMATCH


def test_route_for_declaration_prefers_agent7_first():
    action, repair_unit, reason = _route_for_subtype(
        _SUBTYPE_DECLARATION_API_MISMATCH,
        [],
        "Foo.lean:10:unknown identifier foo",
    )
    assert action == "agent7_signature"
    assert repair_unit == _REPAIR_UNIT_LOCAL_PATCH
    assert "Agent7" in reason


def test_route_for_stalled_proof_promotes_block_restructure():
    history = [
        {
            "action": "agent3_tactical",
            "canonical_error_signature": "Foo.lean:20:rewrite failed",
            "sorry_before": 1,
            "sorry_after": 1,
            "main_error_signature_changed": False,
        },
        {
            "action": "agent3_tactical",
            "canonical_error_signature": "Foo.lean:20:rewrite failed",
            "sorry_before": 1,
            "sorry_after": 1,
            "main_error_signature_changed": False,
        },
    ]
    action, repair_unit, reason = _route_for_subtype(
        _SUBTYPE_PROOF_TACTIC_FAILURE,
        history,
        "Foo.lean:20:rewrite failed",
    )
    assert action == "agent3_tactical"
    assert repair_unit == _REPAIR_UNIT_BLOCK_RESTRUCTURE
    assert "widen Agent3 search" in reason


def test_route_for_strategy_mismatch_replans_then_humans():
    action1, repair_unit1, _ = _route_for_subtype(
        _SUBTYPE_STRATEGY_MISMATCH,
        [],
        "Foo.lean:30:unsolved goals",
    )
    assert action1 == "agent9_replan"
    assert repair_unit1 == _REPAIR_UNIT_STATEMENT_GAP

    action2, repair_unit2, _ = _route_for_subtype(
        _SUBTYPE_STRATEGY_MISMATCH,
        [{"action": "agent9_replan"}],
        "Foo.lean:30:unsolved goals",
    )
    assert action2 == "human_missing_assumption"
    assert repair_unit2 == _REPAIR_UNIT_STATEMENT_GAP


def test_agent9_theorem_context_supports_legacy_fields():
    legacy_plan = {
        "theorems": [
            {
                "name": "process_succ",
                "line_number": 81,
                "depends_on": ["process_zero"],
                "difficulty": "medium",
                "proof_strategy": "rw [process]; simp",
                "key_lib_lemmas": ["by_cases"],
                "missing_glue_lemmas": [],
            }
        ]
    }
    ctx = _build_agent9_theorem_context(legacy_plan, "process_succ")
    assert "lean_statement_line: 81" in ctx
    assert "estimated_difficulty: medium" in ctx
    assert "depends_on: ['process_zero']" in ctx


def test_prefer_agent3_search_owner_promotes_restructure_after_stall():
    repair_unit, reason = _prefer_agent3_search_owner(
        _SUBTYPE_PROOF_API_MISMATCH,
        no_progress_streak=2,
    )
    assert repair_unit == _REPAIR_UNIT_BLOCK_RESTRUCTURE
    assert "sampled search" in reason


def test_prompt_resolution_and_error_helpers_are_none_safe():
    decision = {"agent7_targeted_prompt": None}
    assert _resolve_decision_prompt(decision, "agent7_targeted_prompt", "fallback") == "fallback"
    text = _coerce_errors_text(["Foo.lean:1:1: error: boom", {"data": "bang"}, ""])
    assert "boom" in text
    assert "bang" in text

    verify = {"error_count": 5, "errors": ["a", "b"]}
    assert _error_count_from_verify(verify, "x\ny") == 5


def test_canonical_error_signature_prefers_primary_line():
    errors = (
        "Algorithms/Foo.lean:42:7: error: Application type mismatch\n"
        "Algorithms/Foo.lean:48:2: error: unsolved goals"
    )
    assert _canonical_error_signature(errors) == "Foo.lean:42:application type mismatch"


def test_run_agent8_loop_requires_repo_verify_for_initial_clean(monkeypatch):
    import orchestrator.tools as tools_mod
    import orchestrator.phase3_agent8 as a8

    monkeypatch.setattr(
        tools_mod,
        "run_lean_verify",
        lambda _path: {"exit_code": 0, "sorry_count": 0, "errors": ""},
    )
    monkeypatch.setattr(
        tools_mod,
        "run_repo_verify",
        lambda: {"exit_code": 1, "errors": ["Algorithms/Foo.lean:1:1: error: repo failed"]},
    )
    monkeypatch.setattr(
        a8,
        "_dispatch_agent9",
        lambda *_args, **_kwargs: {"theorems": []},
    )
    monkeypatch.setattr(
        a8,
        "_agent8_run_agent3",
        lambda *_args, **_kwargs: {"exit_code": 1, "sorry_count": 1, "errors": "repo failed"},
    )
    monkeypatch.setitem(a8.RETRY_LIMITS, "AGENT8_MAX_STEPS", 1)

    success, _plan, errors = run_agent8_loop(None, "Algorithms/Foo.lean", "plan", "old errors")
    assert success is False
    assert "repo failed" in errors


def test_run_agent8_loop_requires_repo_verify_after_agent3_clean(monkeypatch):
    import orchestrator.tools as tools_mod
    import orchestrator.phase3_agent8 as a8

    verify_calls = {"n": 0}

    def _verify(_path):
        verify_calls["n"] += 1
        if verify_calls["n"] == 1:
            return {"exit_code": 1, "sorry_count": 1, "errors": "Foo.lean:10: error: rewrite failed"}
        return {"exit_code": 0, "sorry_count": 0, "errors": ""}

    monkeypatch.setattr(tools_mod, "run_lean_verify", _verify)
    monkeypatch.setattr(
        tools_mod,
        "run_repo_verify",
        lambda: {"exit_code": 1, "errors": ["Algorithms/Foo.lean:2:3: error: build failed"]},
    )
    monkeypatch.setattr(
        a8,
        "_agent8_run_agent3",
        lambda *_args, **_kwargs: {"exit_code": 0, "sorry_count": 0, "errors": ""},
    )
    monkeypatch.setitem(a8.RETRY_LIMITS, "AGENT8_MAX_STEPS", 1)

    success, _plan, errors = run_agent8_loop(None, "Algorithms/Foo.lean", "plan", "old errors")
    assert success is False
    assert "build failed" in errors
