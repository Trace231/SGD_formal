from __future__ import annotations

from types import SimpleNamespace

from orchestrator import config
from orchestrator.agents import Agent
from orchestrator.tools import run_lean_verify


def _reset_runtime_defaults() -> None:
    config.set_runtime_overrides(
        agent_runtime="hybrid",
        codex_skip_only=True,
        lean_verify_backend="auto",
        codex_transport="api",
        skip_to_agent9=False,
    )


def test_agent_runtime_codex_for_skip_roles(monkeypatch):
    _reset_runtime_defaults()
    config.set_runtime_overrides(agent_runtime="codex", codex_skip_only=False, skip_to_agent9=False)

    captured: dict[str, str] = {}

    def _fake_call_llm(*, provider, model, system, messages, max_tokens):
        _ = (provider, model, messages, max_tokens)
        captured["system"] = system
        return "{}"

    monkeypatch.setattr("orchestrator.agents.call_llm", _fake_call_llm)

    agent = Agent("sorry_closer")
    assert agent.backend_name == "codex"
    agent.call("ping")
    assert "[CODEX RUNTIME MODE]" in captured["system"]


def test_agent_runtime_hybrid_skip_only_keeps_http_outside_skip(monkeypatch):
    _reset_runtime_defaults()
    config.set_runtime_overrides(agent_runtime="hybrid", codex_skip_only=True, skip_to_agent9=False)

    def _fake_call_llm(*, provider, model, system, messages, max_tokens):
        _ = (provider, model, system, messages, max_tokens)
        return "{}"

    monkeypatch.setattr("orchestrator.agents.call_llm", _fake_call_llm)

    agent = Agent("sorry_closer")
    assert agent.backend_name == "http"


def test_run_lean_verify_auto_falls_back_to_lake_on_leanlsp_failure(monkeypatch):
    _reset_runtime_defaults()
    config.set_runtime_overrides(lean_verify_backend="auto")

    def _boom_verify(self, rel_path, *, timeout=None):
        _ = (self, rel_path, timeout)
        raise RuntimeError("leanlsp unavailable")

    monkeypatch.setattr("orchestrator.tools.LeanLSPService.verify", _boom_verify)
    monkeypatch.setattr(
        "orchestrator.tools.lake_build",
        lambda target=None: SimpleNamespace(returncode=0, errors="", sorry_count=0, elapsed_ms=3),
    )
    monkeypatch.setattr("orchestrator.tools.count_sorrys", lambda _rel: 0)

    out = run_lean_verify("Algorithms/sorry.lean")
    assert out["verify_backend_used"] == "lake"
    assert out["exit_code"] == 0
    assert any("LeanLSP verify failure" in w for w in out.get("warnings", []))
