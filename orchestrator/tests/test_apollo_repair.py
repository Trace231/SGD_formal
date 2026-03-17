"""Stage-2 APOLLO repair classifier and outage behavior tests."""

from orchestrator import apollo_repair


def test_classify_failure_kind_prefers_interface_markers():
    kind, reason, _ = apollo_repair.classify_failure_kind(
        "Application type mismatch in declaration"
    )
    assert kind == "interface_failure"
    assert "mismatch" in reason


def test_classify_failure_kind_does_not_use_generic_declaration_token():
    kind, _, _ = apollo_repair.classify_failure_kind(
        "declaration elaboration failed with no structural markers"
    )
    assert kind == "strategy_failure"


def test_classify_failure_kind_instance_markers():
    kind, _, _ = apollo_repair.classify_failure_kind(
        "failed to synthesize instance for Monoid Foo"
    )
    assert kind == "instance_failure"


def test_classify_failure_kind_strategy_markers():
    kind, _, _ = apollo_repair.classify_failure_kind("tactic failed\nunsolved goals")
    assert kind == "strategy_failure"


def test_build_subproblem_graph_prioritizes_compile_then_glue_then_strategy():
    graph = apollo_repair.build_subproblem_graph(
        current_errors="unknown identifier foo\nmissing glue bridge candidates",
        error_subtype="declaration_api_mismatch",
        lemma_count=1,
    )
    kinds = [n["kind"] for n in graph]
    assert kinds[0] == "interface_signature"
    assert "missing_glue" in kinds


def test_run_apollo_decompose_repair_reports_bootstrap_failure(tmp_path, monkeypatch):
    target = tmp_path / "T.lean"
    target.write_text("theorem t : True := by\n  sorry\n", encoding="utf-8")

    def _bad_verify_builder():
        def _verify(_code: str):
            raise RuntimeError("simulated apollo outage")

        return _verify

    monkeypatch.setattr(apollo_repair, "build_apollo_verify_callable", _bad_verify_builder)
    out = apollo_repair.run_apollo_decompose_repair(
        target_file=str(target),
        current_errors="Application type mismatch",
    )
    assert out["status"] == "failed"
    assert out["next_route_hint"] in {
        "agent7_signature",
        "agent7_then_agent6",
        "agent9_replan",
    }
    assert isinstance(out.get("subproblem_graph", []), list)
    assert "unavailable" in out["summary"].lower() or "failed" in out["classifier_reason"].lower()
