"""JSONL data loader with repeat and completion marks."""

from __future__ import annotations

import copy
import json
import multiprocessing as mp
import os
from pathlib import Path
from typing import Any


class JsonlDataLoader:
    """APOLLO-style data loader for JSONL tasks."""

    def __init__(
        self,
        *,
        data_path: str,
        data_split: str | list[str] | None,
        data_repeat: int,
        node_rank: int,
        world_size: int,
        log_dir: str,
    ):
        self.manager = mp.Manager()
        self.queue = self.manager.Queue()
        self.lock = mp.Lock()
        self.finished_flag_filename = "finished_running.txt"

        done_set: set[str] = set()
        log_root = Path(log_dir)
        if log_root.exists():
            for dirname in os.listdir(log_root):
                run_dir = log_root / dirname
                if run_dir.is_dir():
                    for subdirname in os.listdir(run_dir):
                        if subdirname.startswith("run"):
                            done_flag = run_dir / subdirname / self.finished_flag_filename
                            if done_flag.exists():
                                done_set.add(f"{dirname}/{subdirname}")

        rows: list[dict[str, Any]] = []
        with open(data_path, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if line:
                    rows.append(json.loads(line))

        if isinstance(data_split, str):
            split_set = {data_split}
        elif isinstance(data_split, list):
            split_set = set(data_split)
        else:
            split_set = None

        todo_count = 0
        for rep in range(max(1, int(data_repeat))):
            for prob_idx, row in enumerate(rows):
                name = str(row.get("name", f"problem_{prob_idx}"))
                run_name = f"{name}/run{rep}"
                if f"{prob_idx}_{run_name}" in done_set:
                    continue
                if split_set is not None and str(row.get("split", "")) not in split_set:
                    continue
                if todo_count % max(1, int(world_size)) == int(node_rank):
                    self.queue.put((prob_idx, run_name, copy.deepcopy(row)))
                todo_count += 1
        print(f"[DataLoader] todo_problems={self.queue.qsize()}", flush=True)

    def size(self) -> int:
        return int(self.queue.qsize())

    def get(self) -> tuple[int | None, str | None, dict[str, Any] | None]:
        with self.lock:
            if self.queue.qsize() > 0:
                return self.queue.get()
        return None, None, None

