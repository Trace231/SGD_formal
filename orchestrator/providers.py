"""Multi-provider LLM client factory and unified call interface.

Supports Qwen and DeepSeek via OpenAI-compatible endpoints, and Anthropic
via its native SDK.  All providers are accessed through a single
``call_llm()`` function so the rest of the codebase is provider-agnostic.

Qwen (Dashscope) streaming chat completions accumulate API ``usage`` tokens when
the response includes them. Heartbeat prints totals via
``start_token_usage_heartbeat`` / ``reset_api_token_meters``.
"""

from __future__ import annotations

import re
import threading
import time
from functools import lru_cache
from typing import Any, Callable

from orchestrator.config import API_KEYS, MAX_TOKENS, PROVIDER_URLS


# ---------------------------------------------------------------------------
# Lazy imports — avoid hard crash if a provider SDK is not installed
# ---------------------------------------------------------------------------

def _get_openai_client(provider: str):
    from openai import OpenAI

    return OpenAI(
        api_key=API_KEYS[provider],
        base_url=PROVIDER_URLS[provider],
    )


def _get_anthropic_client():
    import anthropic

    return anthropic.Anthropic(api_key=API_KEYS["anthropic"])


@lru_cache(maxsize=8)
def get_client(provider: str):
    """Return a cached client instance for *provider*."""
    if provider == "anthropic":
        return _get_anthropic_client()
    if provider not in PROVIDER_URLS:
        raise ValueError(f"Unknown provider: {provider!r}")
    return _get_openai_client(provider)


# ---------------------------------------------------------------------------
# Think-tag stripping (Qwen / DeepSeek reasoning models)
# ---------------------------------------------------------------------------

_THINK_RE = re.compile(r"<think>.*?</think>", re.DOTALL)


def strip_think_tags(text: str) -> str:
    """Remove ``<think>…</think>`` blocks emitted by reasoning models."""
    return _THINK_RE.sub("", text).strip()


# ---------------------------------------------------------------------------
# Unified call — with exponential-backoff retry for transient network errors
# ---------------------------------------------------------------------------

_RETRYABLE_ERRORS = frozenset({
    "ConnectTimeout",
    "ReadTimeout",
    "RemoteProtocolError",
    "APIConnectionError",
    "APITimeoutError",
})
_RETRY_DELAYS = (2, 4, 8, 16, 32)  # seconds between attempts 1→2 … 5→6

# HTTP statuses worth retrying (gateway overload, no upstream, rate limits).
_RETRYABLE_HTTP_STATUSES = frozenset({408, 429, 500, 502, 503, 504})


def _is_retryable_llm_error(exc: Exception) -> bool:
    """True for transient network issues and common recoverable API failures."""
    name = type(exc).__name__
    if name in _RETRYABLE_ERRORS:
        return True
    # Explicit classes from the OpenAI SDK (Qwen / DeepSeek gateways).
    if name in ("InternalServerError", "RateLimitError"):
        return True
    if name == "APIStatusError":
        code = getattr(exc, "status_code", None)
        if code is not None and int(code) in _RETRYABLE_HTTP_STATUSES:
            return True
    return False

# ---------------------------------------------------------------------------
# API token metering (Qwen streaming, when ``usage`` is returned)
# ---------------------------------------------------------------------------

_qwen_stats: dict[str, int] = {
    "prompt_tokens": 0,
    "completion_tokens": 0,
    "total_tokens": 0,
}


def reset_qwen_usage_tokens() -> None:
    """Reset accumulated Qwen (provider ``qwen``) API usage counters."""
    _qwen_stats["prompt_tokens"] = 0
    _qwen_stats["completion_tokens"] = 0
    _qwen_stats["total_tokens"] = 0


def reset_api_token_meters() -> None:
    """Reset Qwen API usage counters (orchestrator run start)."""
    reset_qwen_usage_tokens()


def get_qwen_tokens() -> dict[str, int]:
    """Return accumulated Qwen API usage (prompt/completion/total) when reported."""
    return dict(_qwen_stats)


def start_token_usage_heartbeat(interval_seconds: float = 600.0) -> Callable[[], None]:
    """Print cumulative Qwen API token stats on a fixed interval.

    Prints once immediately (baseline), then every *interval_seconds* until the
    returned ``stop()`` is called (typically from ``run()`` ``finally``).
    """
    stop_evt = threading.Event()

    def _loop() -> None:
        while not stop_evt.is_set():
            qw = get_qwen_tokens()
            print(
                "[Qwen API tokens] "
                f"prompt={qw['prompt_tokens']} "
                f"completion={qw['completion_tokens']} "
                f"total={qw['total_tokens']}",
                flush=True,
            )
            if stop_evt.wait(timeout=interval_seconds):
                break

    thread = threading.Thread(
        target=_loop,
        name="token-usage-heartbeat",
        daemon=True,
    )
    thread.start()

    def stop() -> None:
        stop_evt.set()
        thread.join(timeout=max(interval_seconds, 60.0) + 5.0)

    return stop


def _accumulate_qwen_usage(usage: Any) -> None:
    """Add OpenAI-compatible ``usage`` fields to Qwen totals."""
    if usage is None:
        return
    pt = getattr(usage, "prompt_tokens", None)
    ct = getattr(usage, "completion_tokens", None)
    tt = getattr(usage, "total_tokens", None)
    if pt is not None:
        _qwen_stats["prompt_tokens"] += int(pt)
    if ct is not None:
        _qwen_stats["completion_tokens"] += int(ct)
    if tt is not None:
        _qwen_stats["total_tokens"] += int(tt)


def call_llm(
    provider: str,
    model: str,
    system: str,
    messages: list[dict[str, str]],
    *,
    max_tokens: int = MAX_TOKENS,
) -> str:
    """Send *messages* to the LLM behind *provider*/*model* and return the
    assistant reply as a plain string.

    Retries up to 5 times (6 total attempts) with exponential backoff on
    transient network errors, 5xx / overloaded gateway responses, and rate limits.
    Other exceptions are re-raised immediately.
    """
    last_exc: Exception | None = None
    for attempt, delay in enumerate((*_RETRY_DELAYS, None), start=1):
        try:
            return _call_llm_once(provider, model, system, messages, max_tokens=max_tokens)
        except Exception as exc:
            if not _is_retryable_llm_error(exc) or delay is None:
                raise
            last_exc = exc
            print(f"[LLM] {type(exc).__name__} on attempt {attempt}/5, retrying in {delay}s…")
            time.sleep(delay)
    raise last_exc  # type: ignore[misc]  # unreachable, satisfies type checker


def _call_llm_once(
    provider: str,
    model: str,
    system: str,
    messages: list[dict[str, str]],
    *,
    max_tokens: int = MAX_TOKENS,
) -> str:
    """Single (non-retrying) LLM call — the inner workhorse of ``call_llm``."""
    client = get_client(provider)

    if provider == "anthropic":
        resp = client.messages.create(
            model=model,
            system=system,
            messages=messages,
            max_tokens=max_tokens,
        )
        return resp.content[0].text

    full_messages = [{"role": "system", "content": system}, *messages]

    if provider == "qwen":
        def _qwen_non_stream_fallback() -> str:
            resp = client.chat.completions.create(
                model=model,
                messages=full_messages,
                max_tokens=max_tokens,
            )
            usage = getattr(resp, "usage", None)
            if usage is not None:
                _accumulate_qwen_usage(usage)
            return resp.choices[0].message.content or ""

        # enable_thinking requires stream=True on Dashscope; include_usage when supported
        _stream_kwargs: dict[str, Any] = {
            "model": model,
            "messages": full_messages,
            "max_tokens": max_tokens,
            "extra_body": {"enable_thinking": True},
            "stream": True,
        }
        try:
            stream = client.chat.completions.create(
                **_stream_kwargs,
                stream_options={"include_usage": True},
            )
        except Exception as exc:
            if _is_retryable_llm_error(exc):
                return strip_think_tags(_qwen_non_stream_fallback())
            # Some gateways reject ``stream_options``; retry without usage hints.
            try:
                stream = client.chat.completions.create(**_stream_kwargs)
            except Exception as stream_exc:
                if _is_retryable_llm_error(stream_exc):
                    return strip_think_tags(_qwen_non_stream_fallback())
                raise
        text = ""
        last_usage: Any = None
        try:
            for chunk in stream:
                # Usage-only chunks (e.g. final chunk with ``stream_options.include_usage``)
                # may have empty ``choices`` — do not index ``choices[0]``.
                ch = getattr(chunk, "choices", None) or []
                if ch:
                    delta = ch[0].delta
                    if hasattr(delta, "content") and delta.content:
                        text += delta.content
                u = getattr(chunk, "usage", None)
                if u is not None:
                    last_usage = u
        except Exception as exc:
            if _is_retryable_llm_error(exc):
                return strip_think_tags(_qwen_non_stream_fallback())
            raise
        if last_usage is not None:
            _accumulate_qwen_usage(last_usage)
    else:
        # deepseek / other OpenAI-compatible: non-streaming chat completions
        resp = client.chat.completions.create(
            model=model,
            messages=full_messages,
            max_tokens=max_tokens,
        )
        text = resp.choices[0].message.content or ""
    return strip_think_tags(text)
