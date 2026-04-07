"""Regression tests for compile-health gating and Agent9 minimal context."""

from __future__ import annotations

from orchestrator.compile_health import check_compile_health, recover_compile_health
from orchestrator.phase3a_agent9 import (
    _build_glue_signature_block,
    _build_minimal_scaffold_context,
)


class _FakeRegistry:
    def __init__(self, repo_results, file_results):
        self._repo_results = list(repo_results)
        self._file_results = list(file_results)
        self.calls: list[tuple[str, tuple, dict]] = []

    def call(self, name, *args, **kwargs):
        self.calls.append((name, args, kwargs))
        if name == "run_repo_verify":
            return self._repo_results.pop(0)
        if name == "run_lean_verify":
            return self._file_results.pop(0)
        raise AssertionError(f"unexpected tool call: {name}")


def test_check_compile_health_flags_missing_object_file():
    health = check_compile_health(
        {
            "errors": "error: object file 'Lib/Glue/Algebra.olean' of module Lib.Glue.Algebra does not exist",
            "verify_backend_used": "lake",
            "verify_backend_reason": "ok",
        },
        target_file="Algorithms/sorry.lean",
    )
    assert health["healthy"] is False
    assert health["import_resolves"] is False
    assert health["olean_available"] is False
    assert health["verify_backend_healthy"] is True


def test_recover_compile_health_retries_until_verify_is_healthy():
    registry = _FakeRegistry(
        repo_results=[
            {"exit_code": 1, "errors": "dep failed"},
            {"exit_code": 0, "errors": ""},
        ],
        file_results=[
            {
                "exit_code": 1,
                "errors": "error: object file 'Lib/Glue/Algebra.olean' of module Lib.Glue.Algebra does not exist",
                "verify_backend_used": "lake",
                "verify_backend_reason": "ok",
            },
            {
                "exit_code": 0,
                "errors": "",
                "verify_backend_used": "lake",
                "verify_backend_reason": "ok",
            },
        ],
    )
    initial_verify = {
        "exit_code": 1,
        "errors": "error: object file 'Lib/Glue/Algebra.olean' of module Lib.Glue.Algebra does not exist",
        "verify_backend_used": "lake",
        "verify_backend_reason": "ok",
    }

    out = recover_compile_health(
        "Algorithms/sorry.lean",
        registry=registry,
        verify_result=initial_verify,
        max_retries=2,
    )

    assert out["healthy_after"] is True
    assert out["health"]["healthy"] is True
    assert len(out["attempts"]) == 2
    assert [name for name, _args, _kwargs in registry.calls] == [
        "run_repo_verify",
        "run_lean_verify",
        "run_repo_verify",
        "run_lean_verify",
    ]


def test_build_minimal_scaffold_context_uses_headers_and_local_error_window():
    content = "\n".join(
        ["import Mathlib", ""]
        + [f"def filler{i} := {i}" for i in range(80)]
        + [
            "",
            "theorem main_result : True := by",
            "  trivial",
            "",
            "lemma helper_result : True := by",
            "  trivial",
        ]
    )
    verify_state = {"errors": "Algorithms/sorry.lean:84:2: error: unsolved goals"}

    ctx = _build_minimal_scaffold_context(
        "Algorithms/sorry.lean",
        content,
        verify_state=verify_state,
    )

    assert "## Theorem Headers" in ctx
    assert "theorem main_result : True := by" in ctx
    assert "lemma helper_result : True := by" in ctx
    assert "   84| theorem main_result : True := by" in ctx
    assert "    2| def filler0 := 0" not in ctx


def test_build_glue_signature_block_drops_missing_manifest(monkeypatch):
    monkeypatch.setattr(
        "orchestrator.phase3a_agent9.generate_project_manifest",
        lambda _paths: '<manifest path="docs/CONVENTIONS.md">\\n[FILE NOT FOUND]\\n</manifest>',
    )
    assert _build_glue_signature_block() == ""
