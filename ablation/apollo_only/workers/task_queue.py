"""Task queue with monitor logs (APOLLO-style)."""

from __future__ import annotations

import multiprocessing as mp
import threading
import time


class TaskQueue:
    """Shared queue that supports batched pop and monitor logging."""

    def __init__(self, batch_size: int = 128, name: str = "queue"):
        self.name = name
        self.batch_size = int(batch_size)
        self.manager = mp.Manager()
        self.waiting_list = self.manager.list()
        self.all_tasks_done = mp.Event()
        self.lock = mp.Lock()
        self._monitor_log = self.manager.list()
        self._monitor_thread = threading.Thread(target=self._monitor, daemon=True)
        self._monitor_thread.start()

    def _monitor(self) -> None:
        last_log_time = time.time()
        while not self.all_tasks_done.is_set():
            if time.time() - last_log_time >= 30.0:
                with self.lock:
                    if len(self._monitor_log) > 0:
                        total = int(sum(self._monitor_log))
                        avg = float(total / len(self._monitor_log))
                        print(
                            f"[TaskQueue:{self.name}] popped={total} avg_batch={avg:.1f} "
                            f"pending={len(self.waiting_list)}",
                            flush=True,
                        )
                        self._monitor_log[:] = []
                last_log_time = time.time()
            time.sleep(1.0)

    def __len__(self) -> int:
        return len(self.waiting_list)

    def put(self, item: object) -> None:
        with self.lock:
            self.waiting_list.append(item)

    def get(self, no_wait: bool = False) -> list[object] | None:
        while not self.all_tasks_done.is_set():
            with self.lock:
                if len(self.waiting_list) > 0:
                    tasks = self.waiting_list[: self.batch_size]
                    self.waiting_list[: self.batch_size] = []
                    self._monitor_log.append(len(tasks))
                    return list(tasks)
            if no_wait:
                break
            time.sleep(0.05)
        return None

    def close(self) -> None:
        self.all_tasks_done.set()
        self._monitor_thread.join(timeout=2.0)

