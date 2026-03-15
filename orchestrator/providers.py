"""Multi-provider LLM client factory and unified call interface.

Supports Qwen and DeepSeek via OpenAI-compatible endpoints, and Anthropic
via its native SDK.  All providers are accessed through a single
``call_llm()`` function so the rest of the codebase is provider-agnostic.
"""

from __future__ import annotations

import re
import time
from functools import lru_cache

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
    transient network errors (timeouts, connection drops).  All other
    exceptions are re-raised immediately.
    """
    last_exc: Exception | None = None
    for attempt, delay in enumerate((*_RETRY_DELAYS, None), start=1):
        try:
            return _call_llm_once(provider, model, system, messages, max_tokens=max_tokens)
        except Exception as exc:
            if type(exc).__name__ not in _RETRYABLE_ERRORS or delay is None:
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
        # enable_thinking requires stream=True on Dashscope
        stream = client.chat.completions.create(
            model=model,
            messages=full_messages,
            max_tokens=max_tokens,
            extra_body={"enable_thinking": True},
            stream=True,
        )
        text = ""
        for chunk in stream:
            delta = chunk.choices[0].delta
            if hasattr(delta, "content") and delta.content:
                text += delta.content
    else:
        # deepseek-reasoner has thinking built-in; other providers need no extra_body
        resp = client.chat.completions.create(
            model=model,
            messages=full_messages,
            max_tokens=max_tokens,
        )
        text = resp.choices[0].message.content or ""
    return strip_think_tags(text)
