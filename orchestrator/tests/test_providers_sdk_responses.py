"""Tests for OpenAI Responses SDK transport helpers in providers."""

from __future__ import annotations

import pytest

from orchestrator import providers as p


def test_messages_to_responses_input_contains_system_and_roles() -> None:
    out = p._messages_to_responses_input(
        "sys",
        [
            {"role": "user", "content": "u1"},
            {"role": "assistant", "content": "a1"},
        ],
    )
    assert out[0]["role"] == "system"
    assert out[0]["content"][0]["text"] == "sys"
    assert out[1]["role"] == "user"
    assert out[2]["role"] == "assistant"


def test_call_llm_sdk_extracts_output_text(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setitem(p.API_KEYS, "openai", "sk-test")

    class _Resp:
        output_text = "hello"

    class _Client:
        class _Responses:
            @staticmethod
            def create(**kwargs):
                assert kwargs["model"] == "gpt-5-codex"
                return _Resp()

        responses = _Responses()

    monkeypatch.setattr(p, "get_sdk_client", lambda: _Client())

    out = p.call_llm_sdk(
        model="gpt-5-codex",
        system="s",
        messages=[{"role": "user", "content": "u"}],
        max_tokens=32,
        timeout=10,
    )
    assert out == "hello"


def test_call_llm_sdk_with_retry_retries_retryable(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setitem(p.API_KEYS, "openai", "sk-test")

    class ConnectTimeout(Exception):
        pass

    calls = {"n": 0}

    def _fake_call_llm_sdk(**_kwargs):
        calls["n"] += 1
        if calls["n"] == 1:
            raise ConnectTimeout("timeout")
        return "ok"

    monkeypatch.setattr(p, "call_llm_sdk", _fake_call_llm_sdk)

    out = p.call_llm_sdk_with_retry(
        model="gpt-5-codex",
        system="s",
        messages=[{"role": "user", "content": "u"}],
        max_tokens=32,
        timeout=10,
    )
    assert out == "ok"
    assert calls["n"] == 2
