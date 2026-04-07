"""Persistent vLLM generator worker (model initialized once per process)."""

from __future__ import annotations

import multiprocessing as mp
import time
from typing import Any


class GeneratorVllmProcess(mp.Process):
    """vLLM worker with persistent model lifecycle."""

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
        self._llm = None
        self._sampling_params = None

    def _init_model_once(self) -> None:
        if self._llm is not None:
            return
        from vllm import LLM, SamplingParams

        model = str(self.cfg.get("model", "Qwen/Qwen2.5-Coder-7B-Instruct"))
        self._llm = LLM(model=model, trust_remote_code=True)
        self._sampling_params = SamplingParams(
            temperature=float(self.cfg.get("temperature", 0.7)),
            top_p=float(self.cfg.get("top_p", 0.95)),
            max_tokens=int(self.cfg.get("max_tokens", 4096)),
            n=1,
        )

    def _generate(self, task: dict[str, Any]) -> dict[str, Any]:
        prompt = str(task.get("prompt", ""))
        t0 = time.time()
        try:
            self._init_model_once()
            outputs = self._llm.generate([prompt], self._sampling_params, use_tqdm=False)
            text = ""
            if outputs and outputs[0].outputs:
                text = outputs[0].outputs[0].text or ""
            return {
                "text": text,
                "error": "",
                "gen_time": float(time.time() - t0),
                "worker_idx": self.idx,
                "backend": "vllm",
            }
        except Exception as exc:  # noqa: BLE001
            return {
                "text": "",
                "error": str(exc),
                "gen_time": float(time.time() - t0),
                "worker_idx": self.idx,
                "backend": "vllm",
            }

    def run(self) -> None:
        print(f"[GeneratorVllmWorker:{self.idx}] started", flush=True)
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
        print(f"[GeneratorVllmWorker:{self.idx}] stopped", flush=True)

