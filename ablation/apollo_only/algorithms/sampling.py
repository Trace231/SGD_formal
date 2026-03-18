"""Default APOLLO-style sampling algorithm."""

from __future__ import annotations

import copy
import time
from datetime import datetime
from pathlib import Path
from typing import Any

from .base import SamplingAlgorithmBase


def _format_prompt_default(*, source_with_sorry: str, informal_prefix: str, few_shot_prefix: str) -> str:
    return (
        "Complete the following Lean 4 theorem proof.\n\n"
        f"{few_shot_prefix}"
        f"{informal_prefix}\n"
        "```lean4\n"
        f"{source_with_sorry}\n"
        "```\n\n"
        "Return Lean code only. Prefer either theorem body after ':= by' "
        "or full-file Lean snippet."
    )


def _format_prompt_cot_goedel_v2(*, source_with_sorry: str, informal_prefix: str, few_shot_prefix: str) -> str:
    return (
        "You are a Lean 4 theorem prover.\n"
        "Solve the target theorem while preserving declarations/imports.\n"
        "Think privately and output Lean code only.\n\n"
        f"{few_shot_prefix}"
        f"{informal_prefix}\n"
        "### Target Lean file\n"
        "```lean4\n"
        f"{source_with_sorry}\n"
        "```\n\n"
        "Output requirements:\n"
        "1) Return only Lean code.\n"
        "2) Keep theorem statement unchanged.\n"
        "3) Do not add new imports unless strictly necessary.\n"
    )


def _build_prompt(
    *,
    mode: str,
    entry: dict[str, Any],
    source_with_sorry: str,
    few_shot_prefix: str,
) -> str:
    informal_prefix = str(entry.get("informal_prefix", "") or "")
    if mode == "cot_goedel_v2":
        return _format_prompt_cot_goedel_v2(
            source_with_sorry=source_with_sorry,
            informal_prefix=informal_prefix,
            few_shot_prefix=few_shot_prefix,
        )
    return _format_prompt_default(
        source_with_sorry=source_with_sorry,
        informal_prefix=informal_prefix,
        few_shot_prefix=few_shot_prefix,
    )


def _find_theorem_body_region(source: str, theorem_name: str) -> tuple[int, int]:
    key = f"theorem {theorem_name}"
    start = source.find(key)
    if start < 0:
        raise ValueError(f"theorem_not_found: {theorem_name}")
    by_idx = source.find(":= by", start)
    if by_idx < 0:
        raise ValueError(f"theorem_missing_colon_eq_by: {theorem_name}")
    line_end = source.find("\n", by_idx)
    if line_end < 0:
        line_end = len(source)
    body_start = line_end + 1
    return body_start, len(source)


def _render_source_with_sorry(source: str, theorem_name: str) -> str:
    body_start, body_end = _find_theorem_body_region(source, theorem_name)
    return source[:body_start] + "  sorry\n" + source[body_end:]


class Sampling(SamplingAlgorithmBase):
    """Submit N generation requests and stream back samples with metadata."""

    def sample(self, *, data: dict[str, Any], execution_root: Path):
        theorem_name = str(data["theorem_name"])
        target_file = str(data["target_file"])
        target_path = (execution_root / target_file).resolve()
        source = target_path.read_text(encoding="utf-8")
        source_with_sorry = _render_source_with_sorry(source, theorem_name)
        few_shot_prefix = self._sample_few_shot_prefix(current_name=str(data.get("name", "")))
        prompt = _build_prompt(
            mode=self.cfg.prompt_formatter,
            entry=data,
            source_with_sorry=source_with_sorry,
            few_shot_prefix=few_shot_prefix,
        )
        request_payloads = [
            {
                "prompt": prompt,
                "sample_idx": idx,
                "mode": self.cfg.mode,
                "model_args": dict(self.cfg.model_args or {}),
            }
            for idx in range(self.cfg.sample_num)
        ]
        started = time.time()
        req_ids = self.scheduler.generator_submit_all_request(request_payloads)
        for idx, req_id in enumerate(req_ids):
            out = self.scheduler.generator_get_request_outputs(req_id)
            info = {
                "sample_idx": idx,
                "request_id": int(req_id),
                "elapsed_since_start": time.time() - started,
                **self._build_sample_info(
                    prompt_formatter=self.cfg.prompt_formatter,
                    timestamp=datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ"),
                    few_shot_num=self.cfg.few_shot_num,
                ),
            }
            if isinstance(out, dict):
                text = str(out.get("text", ""))
                info["error"] = str(out.get("error", ""))
                info["gen_time"] = float(out.get("gen_time", 0.0) or 0.0)
            else:
                text = str(out or "")
                info["error"] = ""
                info["gen_time"] = 0.0
            if idx % max(1, self.cfg.log_interval) == 0:
                self.process_print(
                    f"[Sampler] received {idx + 1}/{len(req_ids)} candidates",
                    flush=True,
                )
            yield text, copy.deepcopy(info)

