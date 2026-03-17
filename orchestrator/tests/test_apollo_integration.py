"""Unit tests for APOLLO verifier adapter normalization and backend wiring."""

from types import SimpleNamespace

from orchestrator import tools
from orchestrator.apollo_integration import normalize_apollo_result


def test_normalize_apollo_result_keeps_schema_compatibility():
    source = "theorem t : True := by\n  sorry\n"
    raw = {
        "pass": False,
        "complete": False,
        "sorries": [{"pos": {"line": 2, "column": 3}}],
        "errors": [{"pos": {"line": 2, "column": 3}, "data": "unsolved goals"}],
        "warnings": [],
        "verify_time": 0.12,
    }
    out = normalize_apollo_result(
        target_rel="Algorithms/Foo.lean",
        source_text=source,
        apollo_result=raw,
    )
    assert out["target"] == "Algorithms/Foo.lean"
    assert out["success"] is False
    assert out["exit_code"] == 1
    assert out["sorry_count"] == 1
    assert out["sorry_declarations"] == 1
    assert out["blocked_sorry_count"] == 0
    assert out["error_count"] == 1
    assert out["errors"]


def test_run_lean_verify_apollo_backend_returns_normalized_result(monkeypatch):
    import orchestrator.apollo_integration as apollo_mod

    monkeypatch.setattr(tools, "LEAN_VERIFY_BACKEND", "apollo")
    monkeypatch.setattr(apollo_mod, "verify_with_apollo", lambda **_: {"pass": True, "complete": True, "sorries": [], "errors": [], "warnings": [], "verify_time": 0.01})

    result = tools.run_lean_verify("Algorithms/SubgradientMethod.lean")
    assert result["success"] is True
    assert result["exit_code"] == 0
    assert "target" in result
    assert "warnings" in result


def test_run_lean_verify_apollo_backend_failure_is_explicit(monkeypatch):
    import orchestrator.apollo_integration as apollo_mod

    monkeypatch.setattr(tools, "LEAN_VERIFY_BACKEND", "apollo")
    monkeypatch.setattr(tools, "APOLLO_FALLBACK_TO_LAKE_ON_FAILURE", False)

    def _boom(**_):
        raise RuntimeError("simulated apollo failure")

    monkeypatch.setattr(apollo_mod, "verify_with_apollo", _boom)
    result = tools.run_lean_verify("Algorithms/SubgradientMethod.lean")
    assert result["success"] is False
    assert result["exit_code"] == 1
    assert any("APOLLO backend failure" in e for e in result.get("errors", []))


def test_run_lean_verify_apollo_failure_degrades_to_lake(monkeypatch):
    import orchestrator.apollo_integration as apollo_mod

    monkeypatch.setattr(tools, "LEAN_VERIFY_BACKEND", "apollo")
    monkeypatch.setattr(tools, "APOLLO_FALLBACK_TO_LAKE_ON_FAILURE", True)

    def _boom(**_):
        raise RuntimeError("simulated network/import outage")

    monkeypatch.setattr(apollo_mod, "verify_with_apollo", _boom)
    monkeypatch.setattr(
        tools,
        "lake_build",
        lambda target=None: SimpleNamespace(returncode=0, errors="", sorry_count=0),
    )
    monkeypatch.setattr(tools, "count_sorrys", lambda _path: 0)

    result = tools.run_lean_verify("Algorithms/SubgradientMethod.lean")
    assert result["success"] is True
    assert result["exit_code"] == 0
    assert any("degraded to lake" in w for w in result.get("warnings", []))


def test_run_lean_verify_apollo_outage_repeated_calls_do_not_deadlock(monkeypatch):
    import orchestrator.apollo_integration as apollo_mod

    monkeypatch.setattr(tools, "LEAN_VERIFY_BACKEND", "apollo")
    monkeypatch.setattr(tools, "APOLLO_FALLBACK_TO_LAKE_ON_FAILURE", True)

    def _boom(**_):
        raise RuntimeError("simulated apollo outage")

    monkeypatch.setattr(apollo_mod, "verify_with_apollo", _boom)
    monkeypatch.setattr(
        tools,
        "lake_build",
        lambda target=None: SimpleNamespace(returncode=0, errors="", sorry_count=0),
    )
    monkeypatch.setattr(tools, "count_sorrys", lambda _path: 0)

    for _ in range(3):
        result = tools.run_lean_verify("Algorithms/SubgradientMethod.lean")
        assert result["exit_code"] == 0
        assert result["success"] is True


def test_run_lean_verify_lake_default_path_unchanged(monkeypatch):
    monkeypatch.setattr(tools, "LEAN_VERIFY_BACKEND", "lake")
    monkeypatch.setattr(
        tools,
        "lake_build",
        lambda target=None: SimpleNamespace(returncode=0, errors="", sorry_count=0),
    )
    monkeypatch.setattr(tools, "count_sorrys", lambda _path: 0)
    result = tools.run_lean_verify("Algorithms/SubgradientMethod.lean")
    assert result["success"] is True
    assert result["exit_code"] == 0
    assert result["sorry_count"] == 0
