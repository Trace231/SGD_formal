"""Regression checks for Agent8 evidence/replan policy upgrades,
including API-mismatch precision (subtype classifier, route downweight)."""

import orchestrator.phase3_agent8 as a8

from orchestrator.phase3_agent8 import (
    _apply_delta_force_fallback,
    _SUBTYPE_DECLARATION_API_MISMATCH,
    _SUBTYPE_PROOF_API_MISMATCH,
    _SUBTYPE_PROOF_TACTIC_FAILURE,
    _SUBTYPE_STRATEGY_MISMATCH,
    _apply_hard_route_gate,
    _apollo_fallback_from_failure_kind,
    _build_agent9_theorem_context,
    _build_api_shape_contract,
    _check_anti_loop,
    _check_route_downweight,
    _classify_error_subtype,
    _coerce_errors_text,
    _error_count_from_verify,
    _is_structural_error,
    _is_network_error,
    _should_prefer_apollo_decompose,
    _signature_changed,
    _validate_agent8_decision_schema,
)


def test_decision_schema_requires_evidence_protocol():
    bad = {
        "action": "agent7_signature",
        "priority_level": "P0",
        "reason": "missing evidence",
        "targeted_prompt": "fix signature",
        "error_signature": "unknown identifier",
        "hypothesis": "identifier not imported",
        "evidence": [{"source": "run_lean_verify", "snippet": "unknown identifier foo"}],
        "confidence": 0.8,
        "counterfactual": "agent3_tactical cannot fix missing declarations",
    }
    ok, _ = _validate_agent8_decision_schema(bad)
    assert not ok

    good = dict(bad)
    good["evidence"] = [
        {"source": "run_lean_verify", "snippet": "unknown identifier foo"},
        {"source": "search_in_file", "snippet": "foo not defined in target file"},
    ]
    ok2, _ = _validate_agent8_decision_schema(good)
    assert ok2


def test_decision_schema_accepts_apollo_decompose_action():
    good = {
        "action": "apollo_decompose_repair",
        "priority_level": "P1b",
        "reason": "signature unchanged for 2 ticks",
        "targeted_prompt": "run decomposition pipeline",
        "error_signature": "application type mismatch",
        "hypothesis": "local tactical route is stalled",
        "evidence": [
            {"source": "decision_history", "snippet": "same signature for 2 ticks"},
            {"source": "run_lean_verify", "snippet": "blocked_sorry_count=2"},
        ],
        "confidence": 0.78,
        "counterfactual": "agent3_tactical repeated with zero progress",
    }
    ok, msg = _validate_agent8_decision_schema(good)
    assert ok, msg


def test_structural_vs_tactical_classification_regression():
    assert _is_structural_error(
        "Application type mismatch in declaration zone",
        "",
    )
    assert _is_structural_error(
        "unknown identifier `integral_nonneg`",
        "",
    )
    assert not _is_structural_error(
        "tactic 'linarith' failed",
        "no goals solved by linarith",
    )


def test_antiloop_same_hypothesis_forces_replan():
    decision = {
        "action": "agent3_tactical",
        "error_signature": "Application type mismatch",
        "hypothesis": "wrong explicit setup argument in declaration zone",
    }
    history = [
        {
            "action": "agent3_tactical",
            "error_signature": "Application type mismatch",
            "hypothesis": "wrong explicit setup argument in declaration zone",
            "outcome": "failed",
            "top_error_count_before": 3,
            "top_error_count_after": 3,
        },
        {
            "action": "agent7_signature",
            "error_signature": "Application type mismatch",
            "hypothesis": "wrong explicit setup argument in declaration zone",
            "outcome": "failed",
            "top_error_count_before": 3,
            "top_error_count_after": 3,
        },
    ]
    action, reason = _check_anti_loop(decision, history)
    assert action == "agent9_replan"
    assert "same error_signature + same hypothesis" in reason


# ---------------------------------------------------------------------------
# Subtype classifier regression cases
# ---------------------------------------------------------------------------

def test_classify_integral_api_in_proof_body():
    """integral_nonneg with proof-body tactic context → proof_api_mismatch."""
    errors = (
        "Algorithms/Foo.lean:42:3: error: type mismatch\n"
        "  integral_nonneg applied to 3 arguments but expects 2\n"
        "  tactic exact failed"
    )
    result = _classify_error_subtype(errors)
    assert result == _SUBTYPE_PROOF_API_MISMATCH, f"got {result!r}"


def test_classify_sum_range_api_in_proof_body():
    """Finset.sum error with tactic context → proof_api_mismatch."""
    errors = (
        "Bar.lean:80:5: error: application type mismatch\n"
        "  sum_range_succ has type ... but is applied to ...\n"
        "  have h : ... := by exact ..."
    )
    result = _classify_error_subtype(errors)
    assert result == _SUBTYPE_PROOF_API_MISMATCH, f"got {result!r}"


def test_classify_unknown_identifier_is_declaration():
    """unknown identifier outside proof body → declaration_api_mismatch."""
    errors = "Foo.lean:10:0: error: unknown identifier 'myLemma'"
    result = _classify_error_subtype(errors)
    assert result == _SUBTYPE_DECLARATION_API_MISMATCH, f"got {result!r}"


def test_classify_tactic_failure_no_api():
    """linarith failure → proof_tactic_failure (not api mismatch)."""
    errors = (
        "Baz.lean:55:6: error: tactic 'linarith' failed\n"
        "  no goals solved"
    )
    result = _classify_error_subtype(errors)
    assert result == _SUBTYPE_PROOF_TACTIC_FAILURE, f"got {result!r}"


def test_classify_strategy_mismatch_from_history():
    """Three consecutive zero-progress entries → strategy_mismatch."""
    history = [
        {"action": "agent3_tactical", "top_error_count_before": 4, "top_error_count_after": 4, "outcome": "failed"},
        {"action": "agent7_signature", "top_error_count_before": 4, "top_error_count_after": 4, "outcome": "failed"},
        {"action": "agent3_tactical",  "top_error_count_before": 4, "top_error_count_after": 4, "outcome": "failed"},
    ]
    result = _classify_error_subtype("tactic 'ring' failed\n  unsolved goals", decision_history=history)
    assert result == _SUBTYPE_STRATEGY_MISMATCH, f"got {result!r}"


# ---------------------------------------------------------------------------
# API-shape contract injection
# ---------------------------------------------------------------------------

def test_api_shape_contract_emitted_for_proof_api_mismatch():
    errors = "integral_nonneg applied to wrong number of arguments\ntactic exact failed"
    contract = _build_api_shape_contract(_SUBTYPE_PROOF_API_MISMATCH, errors)
    assert "API-SHAPE REPAIR CONTRACT" in contract
    assert "integral_nonneg" in contract
    assert "search_in_file" in contract
    assert "transaction_report" in contract


def test_api_shape_contract_empty_for_other_subtypes():
    for subtype in (_SUBTYPE_DECLARATION_API_MISMATCH, _SUBTYPE_PROOF_TACTIC_FAILURE, _SUBTYPE_STRATEGY_MISMATCH):
        assert _build_api_shape_contract(subtype, "some error") == ""


# ---------------------------------------------------------------------------
# Route downweight regression
# ---------------------------------------------------------------------------

def test_route_downweight_triggers_after_window():
    """3 consecutive route_effective=False entries → downweight."""
    history = [
        {"action": "agent3_tactical", "error_subtype": _SUBTYPE_PROOF_API_MISMATCH, "route_effective": False},
        {"action": "agent3_tactical", "error_subtype": _SUBTYPE_PROOF_API_MISMATCH, "route_effective": False},
        {"action": "agent3_tactical", "error_subtype": _SUBTYPE_PROOF_API_MISMATCH, "route_effective": False},
    ]
    new_action, reason = _check_route_downweight("agent3_tactical", _SUBTYPE_PROOF_API_MISMATCH, history)
    assert new_action != "agent3_tactical", f"expected downweight but got {new_action!r}"
    assert reason


def test_route_downweight_not_triggered_below_window():
    """Only 2 entries — downweight should NOT fire."""
    history = [
        {"action": "agent3_tactical", "error_subtype": _SUBTYPE_PROOF_API_MISMATCH, "route_effective": False},
        {"action": "agent3_tactical", "error_subtype": _SUBTYPE_PROOF_API_MISMATCH, "route_effective": False},
    ]
    new_action, reason = _check_route_downweight("agent3_tactical", _SUBTYPE_PROOF_API_MISMATCH, history)
    assert new_action == "agent3_tactical"
    assert not reason


def test_route_downweight_not_triggered_mixed_effective():
    """Mix of effective and ineffective — should not downweight."""
    history = [
        {"action": "agent3_tactical", "error_subtype": _SUBTYPE_PROOF_API_MISMATCH, "route_effective": True},
        {"action": "agent3_tactical", "error_subtype": _SUBTYPE_PROOF_API_MISMATCH, "route_effective": False},
        {"action": "agent3_tactical", "error_subtype": _SUBTYPE_PROOF_API_MISMATCH, "route_effective": False},
    ]
    new_action, reason = _check_route_downweight("agent3_tactical", _SUBTYPE_PROOF_API_MISMATCH, history)
    assert new_action == "agent3_tactical"
    assert not reason


def test_hard_route_gate_applies_cooldown():
    history = [
        {"action": "agent3_tactical", "error_subtype": _SUBTYPE_PROOF_API_MISMATCH, "route_effective": False, "outcome": "failed"},
        {"action": "agent3_tactical", "error_subtype": _SUBTYPE_PROOF_API_MISMATCH, "route_effective": False, "outcome": "failed"},
        {"action": "agent3_tactical", "error_subtype": _SUBTYPE_PROOF_API_MISMATCH, "route_effective": False, "outcome": "failed"},
    ]
    cooldowns = {}
    action, reason = _apply_hard_route_gate(
        "agent3_tactical",
        _SUBTYPE_PROOF_API_MISMATCH,
        history,
        cooldowns,
        window=3,
        cooldown_ticks=2,
    )
    assert action == "agent7_signature"
    assert "hard_gate" in reason
    assert cooldowns.get("agent3_tactical", 0) == 2


def test_hard_route_gate_blocks_action_under_cooldown():
    cooldowns = {"agent3_tactical": 1}
    action, reason = _apply_hard_route_gate(
        "agent3_tactical",
        _SUBTYPE_PROOF_API_MISMATCH,
        [],
        cooldowns,
    )
    assert action != "agent3_tactical"
    assert "cooldown blocks" in reason


def test_apollo_fallback_mapping_is_deterministic():
    assert _apollo_fallback_from_failure_kind("interface_failure") == "agent7_signature"
    assert _apollo_fallback_from_failure_kind("instance_failure") == "agent7_signature"
    assert _apollo_fallback_from_failure_kind("glue_failure") == "agent7_then_agent6"
    assert _apollo_fallback_from_failure_kind("strategy_failure") == "agent9_replan"


def test_should_prefer_apollo_when_signature_unchanged_two_ticks(monkeypatch):
    monkeypatch.setattr(
        "orchestrator.phase3_agent8.AGENT8_APOLLO_DECOMPOSE_ENABLED", True
    )
    monkeypatch.setitem(a8.RETRY_LIMITS, "AGENT8_APOLLO_SAME_ERROR_WINDOW", 2)
    monkeypatch.setitem(a8.RETRY_LIMITS, "AGENT8_APOLLO_NO_PROGRESS_WINDOW", 2)
    monkeypatch.setitem(a8.RETRY_LIMITS, "AGENT8_APOLLO_BLOCKED_SORRY_THRESHOLD", 1)
    history = [
        {
            "error_signature": "Application type mismatch",
            "error_count_delta": 0,
            "main_error_signature_changed": False,
            "outcome": "failed",
        },
        {
            "error_signature": "Application type mismatch",
            "error_count_delta": 0,
            "main_error_signature_changed": False,
            "outcome": "failed",
        },
    ]
    ok, reason = _should_prefer_apollo_decompose(
        "agent3_tactical",
        "Application type mismatch",
        history,
        blocked_sorry_count=0,
        action_cooldowns={},
    )
    assert ok
    assert "unchanged" in reason


def test_delta_force_fallback_agent3_to_agent7():
    history = [
        {
            "action": "agent3_tactical",
            "error_count_delta": 0,
            "main_error_signature_changed": False,
        },
        {
            "action": "agent3_tactical",
            "error_count_delta": 1,
            "main_error_signature_changed": False,
        },
    ]
    cooldowns = {}
    action, reason = _apply_delta_force_fallback(
        "agent3_tactical",
        history,
        cooldowns,
        window=2,
        cooldown_ticks=2,
    )
    assert action == "agent7_signature"
    assert "delta_force_fallback" in reason
    assert cooldowns.get("agent3_tactical") == 2


def test_delta_force_fallback_agent7_to_agent9():
    history = [
        {
            "action": "agent7_signature",
            "error_count_delta": 0,
            "main_error_signature_changed": False,
        },
        {
            "action": "agent7_signature",
            "error_count_delta": 3,
            "main_error_signature_changed": False,
        },
    ]
    cooldowns = {}
    action, _ = _apply_delta_force_fallback(
        "agent7_signature",
        history,
        cooldowns,
        window=2,
        cooldown_ticks=2,
    )
    assert action == "agent9_replan"
    assert cooldowns.get("agent7_signature") == 2


def test_delta_force_fallback_not_triggered_when_signature_changed():
    history = [
        {
            "action": "agent3_tactical",
            "error_count_delta": 0,
            "main_error_signature_changed": False,
        },
        {
            "action": "agent3_tactical",
            "error_count_delta": 0,
            "main_error_signature_changed": True,
        },
    ]
    cooldowns = {}
    action, reason = _apply_delta_force_fallback(
        "agent3_tactical",
        history,
        cooldowns,
        window=2,
        cooldown_ticks=2,
    )
    assert action == "agent3_tactical"
    assert not reason


def test_network_failure_not_used_in_downweight_window():
    history = [
        {"action": "agent3_tactical", "error_subtype": _SUBTYPE_PROOF_API_MISMATCH, "route_effective": False, "outcome": "failed"},
        {"action": "agent3_tactical", "error_subtype": _SUBTYPE_PROOF_API_MISMATCH, "route_effective": False, "outcome": "network_failure"},
        {"action": "agent3_tactical", "error_subtype": _SUBTYPE_PROOF_API_MISMATCH, "route_effective": False, "outcome": "failed"},
    ]
    action, reason = _check_route_downweight("agent3_tactical", _SUBTYPE_PROOF_API_MISMATCH, history)
    assert action == "agent3_tactical"
    assert not reason


def test_signature_changed_metric():
    before = "Foo.lean:10:2: error: tactic `rw` failed"
    after = "Foo.lean:12:8: error: application type mismatch"
    assert _signature_changed(before, after)
    assert not _signature_changed(before, before)


def test_coerce_errors_text_with_mixed_payload():
    payload = [
        "Foo.lean:1:1: error: boom",
        {"data": "Bar.lean:2:2: error: bang"},
        "",
    ]
    text = _coerce_errors_text(payload)
    assert "boom" in text
    assert "bang" in text


def test_error_count_prefers_verify_error_count_field():
    verify = {"error_count": 5, "errors": ["a", "b"]}
    assert _error_count_from_verify(verify, "x\ny") == 5


def test_error_count_falls_back_to_errors_list_length():
    verify = {"errors": ["a", "b", "c"]}
    assert _error_count_from_verify(verify, "") == 3


def test_network_error_classifier():
    assert _is_network_error("RemoteProtocolError on attempt 1/5")
    assert _is_network_error("ReadTimeout: upstream timed out")
    assert not _is_network_error("application type mismatch")


# ---------------------------------------------------------------------------
# error_subtype in schema validation
# ---------------------------------------------------------------------------

def test_schema_valid_error_subtype_accepted():
    good = {
        "action": "agent3_tactical",
        "priority_level": "P0b",
        "error_subtype": "proof_api_mismatch",
        "reason": "API mismatch in proof body",
        "targeted_prompt": "fix integral_nonneg args",
        "error_signature": "integral_nonneg wrong args",
        "hypothesis": "integral_nonneg called with wrong arg count",
        "evidence": [
            {"source": "run_lean_verify", "snippet": "integral_nonneg applied to 3 args"},
            {"source": "search_in_file", "snippet": "integral_nonneg : ... → ... → Prop"},
        ],
        "confidence": 0.85,
        "counterfactual": "agent7_signature is for declaration zone, not proof body",
    }
    ok, _ = _validate_agent8_decision_schema(good)
    assert ok


def test_schema_invalid_error_subtype_rejected():
    bad = {
        "action": "agent3_tactical",
        "priority_level": "P4",
        "error_subtype": "unknown_subtype",
        "reason": "some reason",
        "targeted_prompt": "fix it",
        "error_signature": "some error",
        "hypothesis": "something is wrong",
        "evidence": [
            {"source": "run_lean_verify", "snippet": "some error"},
            {"source": "search_in_file", "snippet": "not found"},
        ],
        "confidence": 0.5,
        "counterfactual": "other option worse",
    }
    ok, msg = _validate_agent8_decision_schema(bad)
    assert not ok
    assert "error_subtype" in msg


def test_agent9_hints_are_reference_only_context():
    plan = {
        "theorems": [
            {
                "name": "process_succ",
                "lean_statement_line": 81,
                "dependencies": ["process_zero"],
                "proof_strategy": "rw [process]; simp",
                "proof_technique": "simp_ring",
                "key_lib_lemmas": ["by_cases"],
                "missing_glue_lemmas": [],
                "dependency_map": {},
                "first_action_patch_hint": "Change explicit setup arg at line 81.",
                "expected_lean_shape": "process (Nat.succ t) ξ = ...",
            }
        ]
    }
    ctx = _build_agent9_theorem_context(plan, "process_succ")
    assert "NON-BINDING" in ctx
    assert "first_action_patch_hint" in ctx
    assert "expected_lean_shape" in ctx
