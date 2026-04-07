"""Runtime tests for Codex SDK transport + fallback behavior."""

from __future__ import annotations

from orchestrator import config
from orchestrator.agents import Agent


def _reset_runtime_defaults() -> None:
    config.set_runtime_overrides(
        agent_runtime="hybrid",
        codex_skip_only=True,
        lean_verify_backend="auto",
        codex_transport="api",
        skip_to_agent9=False,
    )


def test_codex_backend_uses_sdk_transport(monkeypatch):
    _reset_runtime_defaults()
    config.set_runtime_overrides(agent_runtime="codex", codex_skip_only=False, codex_transport="sdk")
    monkeypatch.setitem(config.API_KEYS, "openai", "sk-test")

    def _fake_sdk(*, model, system, messages, max_tokens, timeout):
        _ = (system, messages, max_tokens, timeout)
        assert model.startswith("qwen")
        return "{}"

    monkeypatch.setattr("orchestrator.agents.call_llm_qwen_sdk_with_retry", _fake_sdk)
    monkeypatch.setattr("orchestrator.agents.call_llm", lambda **_k: (_ for _ in ()).throw(AssertionError("api should not be used")))

    agent = Agent("sorry_closer")
    out = agent.call("ping")
    assert out == "{}"
    assert agent.backend_name == "codex"
    assert agent.llm_transport == "sdk-chat"
    assert agent.degraded_to_api is False


def test_codex_backend_falls_back_to_api_on_sdk_error(monkeypatch):
    _reset_runtime_defaults()
    config.set_runtime_overrides(agent_runtime="codex", codex_skip_only=False, codex_transport="sdk")
    monkeypatch.setitem(config.API_KEYS, "openai", "sk-test")
    monkeypatch.setattr("orchestrator.agents.call_llm_qwen_sdk_with_retry", lambda **_k: (_ for _ in ()).throw(RuntimeError("boom")))

    captured = {}

    def _fake_api(*, provider, model, system, messages, max_tokens):
        _ = (provider, model, messages, max_tokens)
        captured["system"] = system
        return "fallback"

    monkeypatch.setattr("orchestrator.agents.call_llm", _fake_api)

    agent = Agent("sorry_closer")
    out = agent.call("ping")
    assert out == "fallback"
    assert agent.llm_transport == "api"
    assert agent.degraded_to_api is True
    assert "sdk_qwen_error" in agent.degrade_reason
    assert "[CODEX RUNTIME MODE]" in captured["system"]
