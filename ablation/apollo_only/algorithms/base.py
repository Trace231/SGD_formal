"""Base sampler abstraction for APOLLO parity."""

from __future__ import annotations

import json
import random
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Any


@dataclass
class SamplerConfig:
    """Sampler-level configuration."""

    sample_num: int = 8
    log_interval: int = 8
    mode: str = "cot_goedel_v2"
    max_tokens: int = 4096
    few_shot_dataset: str = ""
    few_shot_num: int = 0
    prompt_formatter: str = "cot_goedel_v2"
    model_args: dict[str, Any] | None = None


class SamplingAlgorithmBase:
    """Base class with generator scheduler dependency."""

    def __init__(
        self,
        *,
        scheduler: Any,
        process_print: Any,
        cfg: dict[str, Any],
    ):
        self.scheduler = scheduler
        self.process_print = process_print
        self.cfg = SamplerConfig(
            sample_num=int(cfg.get("sample_num", 8)),
            log_interval=int(cfg.get("log_interval", 8)),
            mode=str(cfg.get("mode", "cot_goedel_v2")),
            max_tokens=int(cfg.get("max_tokens", 4096)),
            few_shot_dataset=str(cfg.get("few_shot_dataset", "")),
            few_shot_num=max(0, int(cfg.get("few_shot_num", 0))),
            prompt_formatter=str(cfg.get("prompt_formatter", cfg.get("mode", "cot_goedel_v2"))),
            model_args=dict(cfg.get("model_args", {})),
        )
        self._few_shot_rows = self._load_few_shot_rows(self.cfg.few_shot_dataset)

    @property
    def algorithm_name(self) -> str:
        return self.__class__.__name__

    def _load_few_shot_rows(self, path: str) -> list[dict[str, Any]]:
        if not path:
            return []
        p = Path(path).resolve()
        if not p.exists():
            return []
        rows: list[dict[str, Any]] = []
        with p.open("r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if line:
                    try:
                        rows.append(json.loads(line))
                    except Exception:
                        continue
        return rows

    def _sample_few_shot_prefix(self, *, current_name: str) -> str:
        if not self._few_shot_rows or self.cfg.few_shot_num <= 0:
            return ""
        candidates = [r for r in self._few_shot_rows if str(r.get("name", "")) != current_name]
        if not candidates:
            return ""
        k = min(self.cfg.few_shot_num, len(candidates))
        picked = random.sample(candidates, k=k)
        chunks: list[str] = []
        for row in picked:
            header = str(row.get("header", ""))
            stmt = str(row.get("formal_statement", ""))
            proof = str(row.get("formal_proof", ""))
            if stmt:
                chunks.append(f"```lean4\n{header}{stmt}\n{proof}\n```\n")
        return "".join(chunks)

    def _build_sample_info(self, **kwargs: Any) -> dict[str, Any]:
        return {
            "algorithm": self.algorithm_name,
            "datetime": datetime.utcnow().isoformat() + "Z",
            "mode": self.cfg.mode,
            "max_tokens": self.cfg.max_tokens,
            "sample_num": self.cfg.sample_num,
            "model_args": dict(self.cfg.model_args or {}),
            **kwargs,
        }

    def sample(self, **kwargs: Any):
        raise NotImplementedError

