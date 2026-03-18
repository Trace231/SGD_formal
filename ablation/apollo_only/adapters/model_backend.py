"""Model backends for APOLLO-only ablation candidate generation."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from orchestrator.providers import call_llm


@dataclass(frozen=True)
class ModelConfig:
    """Text generation backend config."""

    backend: str
    provider: str
    model: str
    system_prompt: str
    max_tokens: int
    temperature: float
    top_p: float


def generate_one_candidate(
    *,
    prompt: str,
    cfg: ModelConfig,
    sample_idx: int,
) -> str:
    """Generate one candidate from configured backend."""
    if cfg.backend == "api":
        # Uses existing orchestrator provider routing and retries.
        # Keep attempt index in prompt tail to encourage sample diversity.
        user_prompt = (
            f"{prompt}\n\n"
            f"## SamplingAttempt\n"
            f"attempt_index={sample_idx}\n"
            "Return Lean code only."
        )
        return call_llm(
            provider=cfg.provider,
            model=cfg.model,
            system=cfg.system_prompt,
            messages=[{"role": "user", "content": user_prompt}],
            max_tokens=cfg.max_tokens,
        )

    if cfg.backend == "vllm":
        try:
            from vllm import LLM, SamplingParams
        except Exception as exc:  # pragma: no cover - env dependent
            raise RuntimeError(
                "vllm_backend_unavailable: install vllm or use --model-backend api"
            ) from exc

        llm = LLM(model=cfg.model, trust_remote_code=True)
        params = SamplingParams(
            temperature=cfg.temperature,
            top_p=cfg.top_p,
            max_tokens=cfg.max_tokens,
            n=1,
        )
        outputs = llm.generate([prompt], params, use_tqdm=False)
        if not outputs or not outputs[0].outputs:
            return ""
        return outputs[0].outputs[0].text or ""

    raise ValueError(f"unsupported_model_backend: {cfg.backend}")


def load_model_config(runtime_cfg: dict[str, Any]) -> ModelConfig:
    """Create ModelConfig from merged runtime config."""
    return ModelConfig(
        backend=str(runtime_cfg.get("model_backend", "api")),
        provider=str(runtime_cfg.get("provider", "qwen")),
        model=str(runtime_cfg.get("model", "qwen3.5-plus")),
        system_prompt=str(
            runtime_cfg.get(
                "system_prompt",
                (
                    "You are an expert in Lean 4 formal proofs. "
                    "Return only Lean code, no explanations."
                ),
            )
        ),
        max_tokens=int(runtime_cfg.get("max_tokens", 4096)),
        temperature=float(runtime_cfg.get("temperature", 0.7)),
        top_p=float(runtime_cfg.get("top_p", 0.95)),
    )

