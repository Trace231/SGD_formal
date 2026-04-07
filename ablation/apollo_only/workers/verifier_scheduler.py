"""Parallel Lean verifier scheduler with timeout/monitor/recovery semantics."""

from __future__ import annotations

import ctypes
import multiprocessing as mp
import threading
import time
from pathlib import Path
from typing import Any

from ablation.apollo_only.adapters.lean_adapter import LeanVerifyConfig, verify_code

from .scheduler import ProcessScheduler


def _classify_failure(error_text: str) -> str:
    lowered = error_text.lower()
    if "timeout" in lowered:
        return "timeout"
    if "json" in lowered or "protocol" in lowered or "decode" in lowered:
        return "protocol"
    return "runtime"


class VerifierProcess(mp.Process):
    """Worker that verifies Lean candidate code."""

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
        self.complete_count = mp.Value(ctypes.c_int, 0)
        self.last_output_time = mp.Value(ctypes.c_double, time.time())
        self.last_input_time = mp.Value(ctypes.c_double, time.time())

    def _build_verify_cfg(self) -> LeanVerifyConfig:
        return LeanVerifyConfig(
            timeout=int(self.cfg.get("verify_timeout", 300)),
            apollo_project_path=Path(str(self.cfg["apollo_project_path"])).resolve(),
            repl_workspace=Path(str(self.cfg["repl_workspace"])).resolve(),
            lake_path=str(self.cfg["lake_path"]),
            execution_root=Path(str(self.cfg["execution_root"])).resolve(),
            workspace_root=Path(str(self.cfg["workspace_root"])).resolve(),
        )

    def run(self) -> None:
        print(f"[VerifierWorker:{self.idx}] started", flush=True)
        verify_cfg = self._build_verify_cfg()
        while True:
            inputs = self.task_queue.get()
            if inputs is None:
                break
            for _, request_id, task in inputs:
                self.last_input_time.value = time.time()
                code = str(task.get("code", "")) if isinstance(task, dict) else str(task)
                target_path = (
                    Path(str(task.get("target_path", ""))).resolve()
                    if isinstance(task, dict) and task.get("target_path")
                    else None
                )
                t0 = time.time()
                try:
                    result = verify_code(code, verify_cfg, target_path=target_path)
                    result["verify_elapsed_worker"] = float(time.time() - t0)
                    result["verifier_worker_idx"] = self.idx
                    result["failure_kind"] = "none" if bool(result.get("pass", False)) else "runtime"
                except Exception as exc:  # noqa: BLE001
                    error_text = str(exc)
                    result = {
                        "pass": False,
                        "complete": False,
                        "errors": [error_text],
                        "warnings": [],
                        "error_count": 1,
                        "warning_count": 0,
                        "sorry_count": 0,
                        "sorries": [],
                        "verify_time": float(time.time() - t0),
                        "verify_backend_used": "verifier_error",
                        "verify_backend_reason": "exception",
                        "blocked_sorry_count": 0,
                        "sorry_declarations": 0,
                        "verifier_worker_idx": self.idx,
                        "failure_kind": _classify_failure(error_text),
                    }
                with self.lock:
                    self.request_statuses[int(request_id)] = result
                    self.last_output_time.value = time.time()
                    self.complete_count.value += 1
        print(f"[VerifierWorker:{self.idx}] stopped", flush=True)


class VerifierScheduler(ProcessScheduler):
    """Spawns verifier workers and serves APOLLO-style requests."""

    def __init__(
        self,
        *,
        max_concurrent_requests: int,
        cfg: dict[str, Any],
        name: str = "verifier",
    ):
        super().__init__(batch_size=1, name=name)
        self.cfg = cfg
        self.max_concurrent_requests = max(1, int(max_concurrent_requests))
        self.request_timeout_sec = float(
            cfg.get("request_timeout_sec", cfg.get("verify_timeout", 300) + 30)
        )
        self.monitor_interval_sec = float(cfg.get("monitor_interval_sec", 5.0))
        self.monitor_stall_sec = float(cfg.get("monitor_stall_sec", self.request_timeout_sec * 1.5))
        self._request_start: dict[int, float] = {}
        self._closed = False
        self._monitor_stop = threading.Event()
        self._monitor_thread = threading.Thread(target=self._monitor_loop, daemon=True)
        self.processes: list[VerifierProcess | None] = []
        self._spawn_all_workers()
        self._monitor_thread.start()
        print(
            f"[VerifierScheduler] workers={len(self.processes)} timeout={self.request_timeout_sec:.1f}s",
            flush=True,
        )

    def _spawn_all_workers(self) -> None:
        for i in range(self.max_concurrent_requests):
            self._spawn_worker(i)

    def _spawn_worker(self, idx: int) -> None:
        proc = VerifierProcess(
            idx=idx,
            task_queue=self.task_queue,
            request_statuses=self.request_statuses,
            lock=self.lock,
            cfg=self.cfg,
        )
        proc.start()
        if idx >= len(self.processes):
            self.processes.extend([None] * (idx - len(self.processes) + 1))
        self.processes[idx] = proc
        print(f"[VerifierScheduler] worker_spawned idx={idx}", flush=True)

    def _restart_worker(self, idx: int, reason: str) -> None:
        old = self.processes[idx]
        try:
            if old is not None and old.is_alive():
                old.terminate()
                old.join(timeout=2.0)
        except Exception:  # noqa: BLE001
            pass
        self._spawn_worker(idx)
        print(f"[VerifierScheduler] worker_restarted idx={idx} reason={reason}", flush=True)

    def _monitor_loop(self) -> None:
        while not self._monitor_stop.wait(self.monitor_interval_sec):
            if self._closed:
                return
            now = time.time()
            pending = len(self.request_statuses)
            for idx, proc in enumerate(self.processes):
                if proc is None:
                    continue
                if not proc.is_alive():
                    self._restart_worker(idx, reason="dead")
                    continue
                if pending <= 0:
                    continue
                since_output = now - float(proc.last_output_time.value)
                since_input = now - float(proc.last_input_time.value)
                if min(since_output, since_input) > self.monitor_stall_sec:
                    self._restart_worker(idx, reason="stalled")

    @staticmethod
    def _timeout_result(elapsed: float) -> dict[str, Any]:
        return {
            "pass": False,
            "complete": False,
            "errors": [f"verifier_request_timeout:{elapsed:.2f}s"],
            "warnings": [],
            "error_count": 1,
            "warning_count": 0,
            "sorry_count": 0,
            "sorries": [],
            "verify_time": float(elapsed),
            "verify_backend_used": "verifier_scheduler",
            "verify_backend_reason": "timeout",
            "blocked_sorry_count": 0,
            "sorry_declarations": 0,
            "verifier_worker_idx": -1,
            "failure_kind": "timeout",
        }

    def submit_request(self, data: Any) -> int:
        req_id = super().submit_request(data)
        self._request_start[int(req_id)] = time.time()
        return req_id

    def get_request_outputs(self, request_id: int) -> Any:
        request_id = int(request_id)
        t0 = self._request_start.get(request_id, time.time())
        while True:
            outputs = self.get_request_status(request_id)
            if outputs is not None:
                self._request_start.pop(request_id, None)
                if isinstance(outputs, dict) and "failure_kind" not in outputs:
                    outputs["failure_kind"] = "none" if bool(outputs.get("pass", False)) else "runtime"
                return outputs
            elapsed = time.time() - t0
            if elapsed > self.request_timeout_sec:
                with self.lock:
                    self.request_statuses.pop(request_id, None)
                self._request_start.pop(request_id, None)
                return self._timeout_result(elapsed)
            time.sleep(0.1)

    def close(self) -> None:
        self._closed = True
        self._monitor_stop.set()
        if self._monitor_thread.is_alive():
            self._monitor_thread.join(timeout=2.0)
        super().close()
        for p in self.processes:
            if p is not None:
                p.join(timeout=5.0)

