"""Persistent API generator worker process."""

from __future__ import annotations

import multiprocessing as mp
import time
from typing import Any

from orchestrator.providers import call_llm


class GeneratorProcess(mp.Process):
    """Consumes generation requests from scheduler queue."""

    def __init__(
        self,
        *,
        idx: int,
        task_queue: Any,
        request_statuses: Any,
        lock: Any,
        cfg: dict[str, Any],
    ):
        super().__init__()
        self.idx = idx
        self.task_queue = task_queue
        self.request_statuses = request_statuses
        self.lock = lock
        self.cfg = cfg

    def _generate_api(self, prompt: str, sample_idx: int) -> str:
        model_args = self.cfg.get("model_args", {}) if isinstance(self.cfg.get("model_args"), dict) else {}
        system_prompt = str(
            self.cfg.get(
                "system_prompt",
                "You are an expert in Lean 4 formal proofs. Return Lean code only.",
            )
        )
        provider = str(self.cfg.get("provider", model_args.get("provider", "qwen")))
        model = str(self.cfg.get("model", model_args.get("model", "qwen3.5-plus")))
        max_tokens = int(self.cfg.get("max_tokens", model_args.get("max_tokens", 4096)))
        user_prompt = (
            f"{prompt}\n\n"
            "## SamplingAttempt\n"
            f"attempt_index={sample_idx}\n"
            "Return Lean code only."
        )
        return call_llm(
            provider=provider,
            model=model,
            system=system_prompt,
            messages=[{"role": "user", "content": user_prompt}],
            max_tokens=max_tokens,
        )

    def _generate(self, task: dict[str, Any]) -> dict[str, Any]:
        prompt = str(task.get("prompt", ""))
        sample_idx = int(task.get("sample_idx", 0))
        task_model_args = task.get("model_args", {})
        if isinstance(task_model_args, dict) and task_model_args:
            merged_cfg = dict(self.cfg)
            merged_cfg["model_args"] = {**dict(self.cfg.get("model_args", {})), **task_model_args}
            old_cfg = self.cfg
            self.cfg = merged_cfg
        else:
            old_cfg = None
        t0 = time.time()
        try:
            text = self._generate_api(prompt, sample_idx)
            return {
                "text": text,
                "error": "",
                "gen_time": float(time.time() - t0),
                "worker_idx": self.idx,
                "backend": "api",
            }
        except Exception as exc:  # noqa: BLE001
            return {
                "text": "",
                "error": str(exc),
                "gen_time": float(time.time() - t0),
                "worker_idx": self.idx,
                "backend": "api",
            }
        finally:
            if old_cfg is not None:
                self.cfg = old_cfg

    def run(self) -> None:
        print(f"[GeneratorWorker:{self.idx}] started", flush=True)
        while True:
            inputs = self.task_queue.get()
            if inputs is None:
                break
            for _, request_id, task in inputs:
                if not isinstance(task, dict):
                    task = {"prompt": str(task)}
                result = self._generate(task)
                with self.lock:
                    self.request_statuses[int(request_id)] = result
        print(f"[GeneratorWorker:{self.idx}] stopped", flush=True)

