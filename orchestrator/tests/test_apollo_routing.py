"""Route-order tests for verify_with_apollo (repl-first)."""

from __future__ import annotations

import sys
import types

import orchestrator.apollo_integration as apollo_mod


def test_verify_with_apollo_prefers_repl(monkeypatch, tmp_path):
    ws = tmp_path / "replws"
    (ws / ".lake" / "build" / "bin").mkdir(parents=True)
    (ws / ".lake" / "build" / "bin" / "repl").write_text("", encoding="utf-8")
    apollo_root = tmp_path / "apollo"
    apollo_root.mkdir()
    project_root = tmp_path / "proj"
    project_root.mkdir()
    (project_root / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")

    monkeypatch.setattr(
        apollo_mod,
        "verify_with_repl",
        lambda **_: {
            "pass": True,
            "complete": True,
            "errors": [],
            "warnings": [],
            "sorries": [],
            "verify_time": 0.01,
            "backend_used": "apollo_repl",
            "backend_reason": "repl_success",
        },
    )
    out = apollo_mod.verify_with_apollo(
        code="theorem t : True := by\n  trivial\n",
        timeout=20,
        apollo_project_path=apollo_root,
        repl_workspace=ws,
        lake_path="lake",
        project_root=project_root,
    )
    assert out["backend_used"] == "apollo_repl"
    assert out["backend_reason"] == "repl_success"


def test_verify_with_apollo_falls_back_to_apollo_python(monkeypatch, tmp_path):
    ws = tmp_path / "replws"
    (ws / ".lake" / "build" / "bin").mkdir(parents=True)
    (ws / ".lake" / "build" / "bin" / "repl").write_text("", encoding="utf-8")
    apollo_root = tmp_path / "apollo"
    apollo_root.mkdir()
    project_root = tmp_path / "proj"
    project_root.mkdir()
    (project_root / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")

    monkeypatch.setattr(
        apollo_mod,
        "verify_with_repl",
        lambda **_: (_ for _ in ()).throw(RuntimeError("repl_protocol_error: boom")),
    )

    fake_verifier_mod = types.ModuleType("verifier")
    fake_verifier_mod.verify_lean4_file = lambda **_: {
        "pass": True,
        "complete": True,
        "errors": [],
        "warnings": [],
        "sorries": [],
        "verify_time": 0.02,
    }
    monkeypatch.setitem(sys.modules, "prover", types.ModuleType("prover"))
    monkeypatch.setitem(sys.modules, "prover.lean", types.ModuleType("prover.lean"))
    monkeypatch.setitem(sys.modules, "prover.lean.verifier", fake_verifier_mod)

    out = apollo_mod.verify_with_apollo(
        code="theorem t : True := by\n  trivial\n",
        timeout=20,
        apollo_project_path=apollo_root,
        repl_workspace=ws,
        lake_path="lake",
        project_root=project_root,
    )
    assert out["backend_used"] == "apollo_python"
    assert out["backend_reason"] == "apollo_python_success"


def test_verify_with_apollo_zero_timeout_disables_python_timeout(monkeypatch, tmp_path):
    ws = tmp_path / "replws"
    (ws / ".lake" / "build" / "bin").mkdir(parents=True)
    (ws / ".lake" / "build" / "bin" / "repl").write_text("", encoding="utf-8")
    apollo_root = tmp_path / "apollo"
    apollo_root.mkdir()
    project_root = tmp_path / "proj"
    project_root.mkdir()
    (project_root / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")

    monkeypatch.setattr(
        apollo_mod,
        "verify_with_repl",
        lambda **_: (_ for _ in ()).throw(RuntimeError("repl_protocol_error: boom")),
    )

    captured: dict[str, object] = {}

    def _fake_verify_lean4_file(**kwargs):
        captured["timeout"] = kwargs.get("timeout")
        return {
            "pass": True,
            "complete": True,
            "errors": [],
            "warnings": [],
            "sorries": [],
            "verify_time": 0.02,
        }

    fake_verifier_mod = types.ModuleType("verifier")
    fake_verifier_mod.verify_lean4_file = _fake_verify_lean4_file
    monkeypatch.setitem(sys.modules, "prover", types.ModuleType("prover"))
    monkeypatch.setitem(sys.modules, "prover.lean", types.ModuleType("prover.lean"))
    monkeypatch.setitem(sys.modules, "prover.lean.verifier", fake_verifier_mod)

    out = apollo_mod.verify_with_apollo(
        code="theorem t : True := by\n  trivial\n",
        timeout=0,
        apollo_project_path=apollo_root,
        repl_workspace=ws,
        lake_path="lake",
        project_root=project_root,
    )

    assert captured["timeout"] is None
    assert out["backend_used"] == "apollo_python"


def test_verify_with_apollo_preflight_rejects_missing_repl_binary(tmp_path):
    ws = tmp_path / "replws"
    ws.mkdir()
    apollo_root = tmp_path / "apollo"
    apollo_root.mkdir()
    project_root = tmp_path / "proj"
    project_root.mkdir()
    (project_root / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")

    try:
        apollo_mod.verify_with_apollo(
            code="theorem t : True := by\n  trivial\n",
            timeout=20,
            apollo_project_path=apollo_root,
            repl_workspace=ws,
            lake_path="lake",
            project_root=project_root,
        )
        assert False, "expected preflight failure"
    except RuntimeError as exc:
        assert "repl_binary_missing" in str(exc)
