"""Schedulers for generator/verifier worker pools (APOLLO-style)."""

from __future__ import annotations

import ctypes
import multiprocessing as mp
import time
from typing import Any

from .task_queue import TaskQueue


class ProcessScheduler:
    """Generic scheduler with request ID lifecycle."""

    def __init__(self, batch_size: int = 32, name: str = "scheduler"):
        self.name = name
        self.manager = mp.Manager()
        self.batch_size = int(batch_size)
        self.task_queue = TaskQueue(batch_size=batch_size, name=name)
        self.request_statuses = self.manager.dict()
        self.request_counter = mp.Value(ctypes.c_int32, 0)
        self.lock = mp.Lock()

    def submit_request(self, data: Any) -> int:
        with self.lock:
            self.request_counter.value += 1
            request_id = int(self.request_counter.value)
            self.request_statuses[request_id] = None
            self.task_queue.put((time.time(), request_id, data))
        return request_id

    def submit_all_request(self, data_list: list[Any]) -> list[int]:
        return [self.submit_request(data) for data in data_list]

    def get_request_status(self, request_id: int) -> Any:
        with self.lock:
            response = self.request_statuses.get(request_id, None)
            if response is not None:
                self.request_statuses.pop(request_id, None)
            return response

    def get_request_outputs(self, request_id: int) -> Any:
        while True:
            outputs = self.get_request_status(request_id)
            if outputs is not None:
                return outputs
            time.sleep(0.1)

    def get_all_request_outputs(self, request_id_list: list[int]) -> list[Any]:
        return [self.get_request_outputs(request_id) for request_id in request_id_list]

    def close(self) -> None:
        self.task_queue.close()


class Scheduler:
    """Unified scheduler facade (generator/verifier)."""

    def __init__(self, scheduler_dict: dict[str, ProcessScheduler]):
        self._scheduler_dict = scheduler_dict
        for name, scheduler in scheduler_dict.items():
            setattr(self, name, scheduler)
            for key in dir(scheduler):
                if not key.startswith("_"):
                    setattr(self, f"{name}_{key}", getattr(scheduler, key))

    def close(self) -> None:
        for scheduler in self._scheduler_dict.values():
            scheduler.close()

