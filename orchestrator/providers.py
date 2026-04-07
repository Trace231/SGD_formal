"""Multi-provider LLM client factory and unified call interface.

Supports Qwen and DeepSeek via OpenAI-compatible endpoints, and Anthropic
via its native SDK.  All providers are accessed through a single
``call_llm()`` function so the rest of the codebase is provider-agnostic.

Qwen (Dashscope) streaming chat completions accumulate API ``usage`` tokens when
the response includes them. Heartbeat prints totals via
``start_token_usage_heartbeat`` / ``reset_api_token_meters``.
"""

from __future__ import annotations

import os
import re
import threading
import time
from functools import lru_cache
from typing import Any, Callable

from orchestrator.config import (
    API_KEYS,
    CODEX_QWEN_SDK_DISABLE_ENV_PROXY,
    CODEX_QWEN_SDK_PROXY,
    CODEX_OPENAI_COMPAT_MAX_RETRIES,
    CODEX_SDK_DISABLE_ENV_PROXY,
    CODEX_SDK_MODEL,
    CODEX_SDK_PROXY,
    CODEX_SDK_RETRY_LIMIT,
    CODEX_SDK_TIMEOUT,
    MAX_TOKENS,
    OPENAI_BASE_URL,
    PROVIDER_URLS,
)


# ---------------------------------------------------------------------------
# Lazy imports — avoid hard crash if a provider SDK is not installed
# ---------------------------------------------------------------------------

def _get_openai_client(provider: str):
    from openai import OpenAI

    return OpenAI(
        api_key=API_KEYS[provider],
        base_url=PROVIDER_URLS[provider],
        max_retries=max(0, int(CODEX_OPENAI_COMPAT_MAX_RETRIES or 0)),
    )


def _get_anthropic_client():
    import anthropic

    return anthropic.Anthropic(api_key=API_KEYS["anthropic"])


def _get_openai_sdk_client():
    from openai import OpenAI

    kwargs: dict[str, Any] = {
        "api_key": API_KEYS.get("openai", ""),
        "max_retries": 0,
    }
    if OPENAI_BASE_URL:
        kwargs["base_url"] = OPENAI_BASE_URL

    if CODEX_SDK_DISABLE_ENV_PROXY or CODEX_SDK_PROXY:
        import httpx

        httpx_kwargs: dict[str, Any] = {
            "trust_env": not CODEX_SDK_DISABLE_ENV_PROXY,
        }
        if CODEX_SDK_PROXY:
            httpx_kwargs["proxy"] = CODEX_SDK_PROXY
        kwargs["http_client"] = httpx.Client(**httpx_kwargs)

    return OpenAI(**kwargs)


def _get_qwen_sdk_client():
    from openai import OpenAI

    kwargs: dict[str, Any] = {
        "api_key": API_KEYS.get("qwen", ""),
        "base_url": PROVIDER_URLS["qwen"],
        "max_retries": 0,
    }
    if CODEX_QWEN_SDK_DISABLE_ENV_PROXY or CODEX_QWEN_SDK_PROXY:
        import httpx

        httpx_kwargs: dict[str, Any] = {
            "trust_env": not CODEX_QWEN_SDK_DISABLE_ENV_PROXY,
        }
        if CODEX_QWEN_SDK_PROXY:
            httpx_kwargs["proxy"] = CODEX_QWEN_SDK_PROXY
        kwargs["http_client"] = httpx.Client(**httpx_kwargs)

    return OpenAI(**kwargs)


@lru_cache(maxsize=8)
def get_client(provider: str):
    """Return a cached client instance for *provider*."""
    if provider == "anthropic":
        return _get_anthropic_client()
    if provider not in PROVIDER_URLS:
        raise ValueError(f"Unknown provider: {provider!r}")
    return _get_openai_client(provider)


@lru_cache(maxsize=1)
def get_sdk_client():
    """Return cached OpenAI SDK client for Responses API."""
    return _get_openai_sdk_client()


@lru_cache(maxsize=1)
def get_qwen_sdk_client():
    """Return cached OpenAI-compatible SDK client for Qwen chat API."""
    return _get_qwen_sdk_client()


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

_sdk_stats: dict[str, int] = {
    "prompt_tokens": 0,
    "completion_tokens": 0,
    "total_tokens": 0,
}


def reset_qwen_usage_tokens() -> None:
    """Reset accumulated Qwen (provider ``qwen``) API usage counters."""
    _qwen_stats["prompt_tokens"] = 0
    _qwen_stats["completion_tokens"] = 0
    _qwen_stats["total_tokens"] = 0


def reset_sdk_usage_tokens() -> None:
    """Reset accumulated OpenAI Responses SDK usage counters."""
    _sdk_stats["prompt_tokens"] = 0
    _sdk_stats["completion_tokens"] = 0
    _sdk_stats["total_tokens"] = 0


def reset_api_token_meters() -> None:
    """Reset all API/SDK usage counters (orchestrator run start)."""
    reset_qwen_usage_tokens()
    reset_sdk_usage_tokens()


def get_qwen_tokens() -> dict[str, int]:
    """Return accumulated Qwen API usage (prompt/completion/total) when reported."""
    return dict(_qwen_stats)


def get_sdk_tokens() -> dict[str, int]:
    """Return accumulated Responses SDK usage (prompt/completion/total)."""
    return dict(_sdk_stats)


def start_token_usage_heartbeat(interval_seconds: float = 600.0) -> Callable[[], None]:
    """Print cumulative Qwen + SDK token stats on a fixed interval.

    Prints once immediately (baseline), then every *interval_seconds* until the
    returned ``stop()`` is called (typically from ``run()`` ``finally``).
    """
    stop_evt = threading.Event()

    def _loop() -> None:
        while not stop_evt.is_set():
            qw = get_qwen_tokens()
            sd = get_sdk_tokens()
            print(
                "[Token usage] "
                f"qwen(prompt={qw['prompt_tokens']}, completion={qw['completion_tokens']}, total={qw['total_tokens']}) "
                f"sdk(prompt={sd['prompt_tokens']}, completion={sd['completion_tokens']}, total={sd['total_tokens']}) "
                f"combined_total={qw['total_tokens'] + sd['total_tokens']}",
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
    timeout: int | None = None,
    retry_limit: int | None = None,
) -> str:
    """Send *messages* to the LLM behind *provider*/*model* and return the
    assistant reply as a plain string.

    Retries with exponential backoff on transient network errors, 5xx /
    overloaded gateway responses, and rate limits. ``retry_limit`` overrides
    the default retry count; ``timeout`` is forwarded to the underlying SDK
    request when the transport supports it. Other exceptions are re-raised
    immediately.
    """
    effective_retry_limit = CODEX_SDK_RETRY_LIMIT if retry_limit is None else retry_limit
    delays = _RETRY_DELAYS[: max(0, int(effective_retry_limit))]
    retry_count = len(delays)
    last_exc: Exception | None = None
    for attempt, delay in enumerate((*delays, None), start=1):
        try:
            return _call_llm_once(
                provider,
                model,
                system,
                messages,
                max_tokens=max_tokens,
                timeout=timeout,
            )
        except Exception as exc:
            if not _is_retryable_llm_error(exc) or delay is None:
                raise
            last_exc = exc
            print(f"[LLM] {type(exc).__name__} on attempt {attempt}/{retry_count}, retrying in {delay}s…")
            time.sleep(delay)
    raise last_exc  # type: ignore[misc]  # unreachable, satisfies type checker


def _call_llm_once(
    provider: str,
    model: str,
    system: str,
    messages: list[dict[str, str]],
    *,
    max_tokens: int = MAX_TOKENS,
    timeout: int | None = None,
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
        # enable_thinking requires stream=True on Dashscope; include_usage when supported
        _stream_kwargs: dict[str, Any] = {
            "model": model,
            "messages": full_messages,
            "max_tokens": max_tokens,
            "extra_body": {"enable_thinking": True},
            "stream": True,
        }
        if timeout is not None:
            _stream_kwargs["timeout"] = timeout
        try:
            stream = client.chat.completions.create(
                **_stream_kwargs,
                stream_options={"include_usage": True},
            )
        except Exception:
            # Some gateways reject ``stream_options``; retry without usage hints.
            stream = client.chat.completions.create(**_stream_kwargs)
        text = ""
        last_usage: Any = None
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
        if last_usage is not None:
            _accumulate_qwen_usage(last_usage)
    else:
        # deepseek / other OpenAI-compatible: non-streaming chat completions
        resp = client.chat.completions.create(
            model=model,
            messages=full_messages,
            max_tokens=max_tokens,
            timeout=timeout,
        )
        text = resp.choices[0].message.content or ""
    return strip_think_tags(text)


def _accumulate_sdk_usage(usage: Any) -> None:
    """Add Responses SDK usage fields to SDK totals."""
    if usage is None:
        return
    pt = getattr(usage, "input_tokens", None)
    ct = getattr(usage, "output_tokens", None)
    tt = getattr(usage, "total_tokens", None)
    # compatibility fallback (some SDK objects may expose prompt/completion names)
    if pt is None:
        pt = getattr(usage, "prompt_tokens", None)
    if ct is None:
        ct = getattr(usage, "completion_tokens", None)
    if tt is None and pt is not None and ct is not None:
        try:
            tt = int(pt) + int(ct)
        except Exception:
            tt = None
    if pt is not None:
        _sdk_stats["prompt_tokens"] += int(pt)
    if ct is not None:
        _sdk_stats["completion_tokens"] += int(ct)
    if tt is not None:
        _sdk_stats["total_tokens"] += int(tt)


# ---------------------------------------------------------------------------
# Codex SDK (Responses API) transport
# ---------------------------------------------------------------------------


def _messages_to_responses_input(system: str, messages: list[dict[str, str]]) -> list[dict[str, Any]]:
    items: list[dict[str, Any]] = []
    if system.strip():
        items.append(
            {
                "role": "system",
                "content": [{"type": "input_text", "text": system}],
            }
        )
    for msg in messages:
        role = str(msg.get("role", "user")).strip().lower()
        if role not in {"system", "user", "assistant"}:
            role = "user"
        content = str(msg.get("content", ""))
        items.append(
            {
                "role": role,
                "content": [{"type": "input_text", "text": content}],
            }
        )
    return items


def _extract_responses_text(resp: Any) -> str:
    output_text = getattr(resp, "output_text", None)
    if isinstance(output_text, str) and output_text.strip():
        return output_text

    out = []
    for item in getattr(resp, "output", []) or []:
        for c in getattr(item, "content", []) or []:
            txt = getattr(c, "text", None)
            if isinstance(txt, str) and txt:
                out.append(txt)
    if out:
        return "".join(out)
    return ""


def call_llm_sdk(
    *,
    model: str,
    system: str,
    messages: list[dict[str, str]],
    max_tokens: int = MAX_TOKENS,
    timeout: int | None = None,
) -> str:
    """Single-call OpenAI Responses API transport."""
    if not API_KEYS.get("openai", "").strip():
        raise RuntimeError("OPENAI_API_KEY is empty; cannot use SDK transport")

    client = get_sdk_client()
    raw_timeout = CODEX_SDK_TIMEOUT if timeout is None else timeout
    req_timeout: int | None
    try:
        req_timeout = int(raw_timeout) if raw_timeout is not None else None
    except Exception:
        req_timeout = None
    if req_timeout is not None and req_timeout <= 0:
        req_timeout = None

    req_kwargs: dict[str, Any] = {
        "model": model,
        "input": _messages_to_responses_input(system, messages),
        "max_output_tokens": max_tokens,
    }
    if req_timeout is not None:
        req_kwargs["timeout"] = req_timeout

    resp = client.responses.create(**req_kwargs)
    _accumulate_sdk_usage(getattr(resp, "usage", None))
    return strip_think_tags(_extract_responses_text(resp))


def call_llm_sdk_with_retry(
    *,
    model: str | None = None,
    system: str,
    messages: list[dict[str, str]],
    max_tokens: int = MAX_TOKENS,
    timeout: int | None = None,
) -> str:
    """Responses API call with retry policy aligned to call_llm()."""
    sdk_model = model or CODEX_SDK_MODEL
    retry_limit = max(0, int(CODEX_SDK_RETRY_LIMIT or 0))
    delays = _RETRY_DELAYS[:retry_limit] if retry_limit > 0 else tuple()
    last_exc: Exception | None = None

    for attempt, delay in enumerate((*delays, None), start=1):
        try:
            return call_llm_sdk(
                model=sdk_model,
                system=system,
                messages=messages,
                max_tokens=max_tokens,
                timeout=timeout,
            )
        except Exception as exc:
            if not _is_retryable_llm_error(exc) or delay is None:
                raise
            last_exc = exc
            print(f"[LLM-SDK] {type(exc).__name__} on attempt {attempt}, retrying in {delay}s…")
            time.sleep(delay)

    raise last_exc  # type: ignore[misc]



def call_llm_qwen_sdk(
    *,
    model: str,
    system: str,
    messages: list[dict[str, str]],
    max_tokens: int = MAX_TOKENS,
    timeout: int | None = None,
) -> str:
    """Single-call Qwen SDK transport via OpenAI-compatible chat completions."""
    if not API_KEYS.get("qwen", "").strip():
        raise RuntimeError("QWEN_API_KEY is empty; cannot use qwen SDK transport")

    client = get_qwen_sdk_client()
    raw_timeout = CODEX_SDK_TIMEOUT if timeout is None else timeout
    req_timeout: int | None
    try:
        req_timeout = int(raw_timeout) if raw_timeout is not None else None
    except Exception:
        req_timeout = None
    if req_timeout is not None and req_timeout <= 0:
        req_timeout = None

    req_kwargs: dict[str, Any] = {
        "model": model,
        "messages": [{"role": "system", "content": system}, *messages],
        "max_tokens": max_tokens,
    }
    if req_timeout is not None:
        req_kwargs["timeout"] = req_timeout

    resp = client.chat.completions.create(**req_kwargs)
    _accumulate_qwen_usage(getattr(resp, "usage", None))
    text = (resp.choices[0].message.content or "") if getattr(resp, "choices", None) else ""
    return strip_think_tags(text)


def call_llm_qwen_sdk_with_retry(
    *,
    model: str,
    system: str,
    messages: list[dict[str, str]],
    max_tokens: int = MAX_TOKENS,
    timeout: int | None = None,
) -> str:
    """Qwen SDK chat call with retry policy aligned to call_llm()."""
    retry_limit = max(0, int(CODEX_SDK_RETRY_LIMIT or 0))
    delays = _RETRY_DELAYS[:retry_limit] if retry_limit > 0 else tuple()
    last_exc: Exception | None = None

    for attempt, delay in enumerate((*delays, None), start=1):
        try:
            return call_llm_qwen_sdk(
                model=model,
                system=system,
                messages=messages,
                max_tokens=max_tokens,
                timeout=timeout,
            )
        except Exception as exc:
            if not _is_retryable_llm_error(exc) or delay is None:
                raise
            last_exc = exc
            print(f"[LLM-SDK-QWEN] {type(exc).__name__} on attempt {attempt}, retrying in {delay}s…")
            time.sleep(delay)

    raise last_exc  # type: ignore[misc]
