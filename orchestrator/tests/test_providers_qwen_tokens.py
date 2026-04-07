"""Tests for Qwen API token metering in ``providers``."""

from __future__ import annotations

import pytest

from orchestrator import providers as p


@pytest.fixture(autouse=True)
def reset_meter():
    p.reset_api_token_meters()
    yield
    p.reset_api_token_meters()


def test_qwen_stream_accumulates_usage_from_last_chunk(monkeypatch: pytest.MonkeyPatch) -> None:
    class _Usage:
        prompt_tokens = 3
        completion_tokens = 2
        total_tokens = 5

    class _Delta:
        content = "hi"

    class _Choice:
        delta = _Delta()

    class _Chunk:
        choices = [_Choice()]
        usage = None

    class _FinalChunk:
        choices = []
        usage = _Usage()

    def _fake_stream():
        yield _Chunk()
        yield _FinalChunk()

    class _Client:
        class _Chat:
            class _Completions:
                create = staticmethod(lambda **_k: _fake_stream())

            completions = _Completions()

        chat = _Chat()

    monkeypatch.setattr(p, "get_client", lambda _prov: _Client())

    p._call_llm_once(
        "qwen",
        "qwen3.5-plus",
        "s",
        [{"role": "user", "content": "x"}],
        max_tokens=10,
    )
    t = p.get_qwen_tokens()
    assert t["prompt_tokens"] == 3
    assert t["completion_tokens"] == 2
    assert t["total_tokens"] == 5


def test_deepseek_does_not_touch_qwen_meter(monkeypatch: pytest.MonkeyPatch) -> None:
    class _Msg:
        content = "d"

    class _Choice:
        message = _Msg()

    class _Resp:
        choices = [_Choice()]
        usage = type("U", (), {"prompt_tokens": 50, "completion_tokens": 50, "total_tokens": 100})()

    monkeypatch.setattr(p, "get_client", lambda _prov: type(
        "C",
        (),
        {
            "chat": type(
                "Chat",
                (),
                {
                    "completions": type(
                        "Comp",
                        (),
                        {"create": staticmethod(lambda **_k: _Resp())},
                    )()
                },
            )()
        },
    )())

    p._call_llm_once(
        "deepseek",
        "deepseek-chat",
        "s",
        [{"role": "user", "content": "h"}],
        max_tokens=10,
    )
    assert p.get_qwen_tokens()["total_tokens"] == 0
