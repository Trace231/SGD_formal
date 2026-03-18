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
        "warnings": [
            {
                "severity": "warning",
                "pos": {"line": 1, "column": 1},
                "data": "declaration uses 'sorry'",
            }
        ],
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
    assert out["errors"][0] == "Algorithms/Foo.lean:2:3: error: unsolved goals"


def test_normalize_apollo_result_preserves_warning_severity():
    out = normalize_apollo_result(
        target_rel="Algorithms/Foo.lean",
        source_text="theorem t : True := by\n  sorry\n",
        apollo_result={
            "pass": True,
            "complete": False,
            "sorries": [],
            "errors": [],
            "warnings": [
                {
                    "severity": "warning",
                    "pos": {"line": 2, "column": 3},
                    "data": "declaration uses 'sorry'",
                }
            ],
        },
    )
    assert out["warnings"] == [
        "Algorithms/Foo.lean:2:3: warning: declaration uses 'sorry'"
    ]
    assert out["sorry_declarations"] == 1


def test_run_lean_verify_apollo_backend_returns_normalized_result(monkeypatch):
    import orchestrator.apollo_integration as apollo_mod

    monkeypatch.setattr(tools, "LEAN_VERIFY_BACKEND", "apollo")
    monkeypatch.setattr(
        apollo_mod,
        "verify_with_apollo",
        lambda **_: {
            "pass": True,
            "complete": True,
            "sorries": [],
            "errors": [],
            "warnings": [],
            "verify_time": 0.01,
            "backend_used": "apollo_repl",
            "backend_reason": "repl_success",
        },
    )

    result = tools.run_lean_verify("Algorithms/SubgradientMethod.lean")
    assert result["success"] is True
    assert result["exit_code"] == 0
    assert "target" in result
    assert "warnings" in result
    assert result["verify_backend_used"] == "apollo_repl"
    assert result["verify_backend_reason"] == "repl_success"


def test_run_lean_verify_apollo_backend_failure_is_explicit(monkeypatch):
    import orchestrator.apollo_integration as apollo_mod

    monkeypatch.setattr(tools, "LEAN_VERIFY_BACKEND", "apollo")
    monkeypatch.setattr(tools, "APOLLO_FALLBACK_TO_LAKE_ON_FAILURE", False)
    monkeypatch.setattr(tools, "VERIFY_BACKEND_STRICT", False)

    def _boom(**_):
        raise RuntimeError("simulated apollo failure")

    monkeypatch.setattr(apollo_mod, "verify_with_apollo", _boom)
    result = tools.run_lean_verify("Algorithms/SubgradientMethod.lean")
    assert result["success"] is False
    assert result["exit_code"] == 1
    assert any("APOLLO backend failure" in e for e in result.get("errors", []))
    assert result["verify_backend_used"] == "apollo"
    assert "backend_failure:" in result["verify_backend_reason"]


def test_run_lean_verify_apollo_backend_strict_failure(monkeypatch):
    import orchestrator.apollo_integration as apollo_mod

    monkeypatch.setattr(tools, "LEAN_VERIFY_BACKEND", "apollo")
    monkeypatch.setattr(tools, "APOLLO_FALLBACK_TO_LAKE_ON_FAILURE", True)
    monkeypatch.setattr(tools, "VERIFY_BACKEND_STRICT", True)

    def _boom(**_):
        raise RuntimeError("simulated strict failure")

    monkeypatch.setattr(apollo_mod, "verify_with_apollo", _boom)
    result = tools.run_lean_verify("Algorithms/SubgradientMethod.lean")
    assert result["success"] is False
    assert result["exit_code"] == 1
    assert any("strict failure" in e.lower() for e in result.get("errors", []))
    assert result["verify_backend_used"] == "apollo"
    assert "strict_failure:" in result["verify_backend_reason"]


def test_run_lean_verify_apollo_failure_degrades_to_lake(monkeypatch):
    import orchestrator.apollo_integration as apollo_mod

    monkeypatch.setattr(tools, "LEAN_VERIFY_BACKEND", "apollo")
    monkeypatch.setattr(tools, "APOLLO_FALLBACK_TO_LAKE_ON_FAILURE", True)
    monkeypatch.setattr(tools, "VERIFY_BACKEND_STRICT", False)

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
    assert result["verify_backend_used"] == "lake"
    assert result["verify_backend_reason"] == "degraded_to_lake"


def test_run_lean_verify_apollo_outage_repeated_calls_do_not_deadlock(monkeypatch):
    import orchestrator.apollo_integration as apollo_mod

    monkeypatch.setattr(tools, "LEAN_VERIFY_BACKEND", "apollo")
    monkeypatch.setattr(tools, "APOLLO_FALLBACK_TO_LAKE_ON_FAILURE", True)
    monkeypatch.setattr(tools, "VERIFY_BACKEND_STRICT", False)

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
    assert result["verify_backend_used"] == "lake"
    assert result["verify_backend_reason"] == "lake_default"


def test_run_lean_verify_lake_timeout_does_not_crash(monkeypatch):
    monkeypatch.setattr(tools, "LEAN_VERIFY_BACKEND", "lake")
    monkeypatch.setattr(
        tools,
        "lake_build",
        lambda target=None: SimpleNamespace(  # noqa: ARG001
            returncode=124,
            errors="lake_build timeout: command `lake build Algorithms.SubgradientMethod` exceeded 300s",
            sorry_count=0,
        ),
    )
    result = tools.run_lean_verify("Algorithms/SubgradientMethod.lean")
    assert result["success"] is False
    assert result["exit_code"] == 124
    assert result["verify_backend_used"] == "lake"
    assert result["verify_backend_reason"] == "lake_timeout"
