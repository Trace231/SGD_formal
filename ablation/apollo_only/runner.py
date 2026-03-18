#!/usr/bin/env python3
"""High-fidelity APOLLO-parity launcher (API-first)."""

from __future__ import annotations

import argparse
import json
import traceback
from datetime import datetime
from importlib.machinery import SourceFileLoader
from pathlib import Path
from typing import Any

from orchestrator.config import APOLLO_LAKE_PATH, APOLLO_PROJECT_PATH, APOLLO_VERIFY_TIMEOUT, PROJECT_ROOT

from ablation.apollo_only.workers import (
    GeneratorProcess,
    GeneratorVllmProcess,
    JsonlDataLoader,
    ProcessScheduler,
    Scheduler,
    SearchProcess,
    VerifierScheduler,
)

ABLATION_ROOT = PROJECT_ROOT / "ablation" / "apollo_only"
DEFAULT_WORKSPACE_ROOT = ABLATION_ROOT / "workspace"


def _utc_now_tag() -> str:
    return datetime.utcnow().strftime("%Y%m%d_%H%M%S")


def _is_within(path: Path, root: Path) -> bool:
    try:
        path.resolve().relative_to(root.resolve())
        return True
    except ValueError:
        return False


def _resolve_workspace_root(runtime_cfg: dict[str, Any]) -> Path:
    return Path(runtime_cfg.get("workspace_root", str(DEFAULT_WORKSPACE_ROOT))).resolve()


def _resolve_execution_root(runtime_cfg: dict[str, Any], workspace_root: Path) -> Path:
    return Path(runtime_cfg.get("execution_root", str(workspace_root))).resolve()


def _read_workspace_metadata(workspace_root: Path) -> dict[str, Any]:
    meta_path = workspace_root / ".apollo_ablation_meta.json"
    if not meta_path.exists():
        return {"metadata_path": str(meta_path), "exists": False}
    try:
        payload = json.loads(meta_path.read_text(encoding="utf-8"))
    except Exception as exc:  # noqa: BLE001
        return {"metadata_path": str(meta_path), "exists": True, "parse_error": str(exc)}
    payload["metadata_path"] = str(meta_path)
    payload["exists"] = True
    return payload


def _load_python_config(path: Path) -> dict[str, Any]:
    mod = SourceFileLoader(path.stem, str(path)).load_module()
    cfg: dict[str, Any] = {}
    for name in dir(mod):
        if not name.startswith("__"):
            cfg[name] = getattr(mod, name)
    return cfg


def _load_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if line:
                rows.append(json.loads(line))
    return rows


def _collect_success_metrics(log_dir: Path) -> tuple[int, int]:
    sample_total = 0
    success_total = 0
    for p in log_dir.glob("**/summary.json"):
        try:
            obj = json.loads(p.read_text(encoding="utf-8"))
        except Exception:  # noqa: BLE001
            continue
        sample_total += int(obj.get("sample_count", 0))
        success_total += int(obj.get("success_count", 0))
    return sample_total, success_total


def _build_isolation_meta(*, runtime_cfg: dict[str, Any], first_entry: dict[str, Any]) -> dict[str, Any]:
    workspace_root = _resolve_workspace_root(runtime_cfg)
    execution_root = _resolve_execution_root(runtime_cfg, workspace_root)
    target_rel = str(first_entry.get("target_file", ""))
    target_abs = str((execution_root / Path(target_rel)).resolve()) if target_rel else ""
    workspace_meta = _read_workspace_metadata(workspace_root)
    source_snapshot_hash = str(workspace_meta.get("source_scaffold_hash", ""))
    return {
        "workspace_root": str(workspace_root),
        "execution_root": str(execution_root),
        "target_file_rel": target_rel,
        "target_file_abs": target_abs,
        "workspace_metadata": workspace_meta,
        "source_snapshot_hash": source_snapshot_hash,
        "isolation_check_passed": bool(
            _is_within(execution_root, workspace_root)
            and bool(target_rel)
            and _is_within(Path(target_abs), execution_root)
        ),
    }


def _validate_dataset_isolation(entries: list[dict[str, Any]], execution_root: Path, workspace_root: Path) -> None:
    if not _is_within(execution_root, workspace_root):
        raise RuntimeError(
            f"execution_root_outside_workspace: {execution_root} not under {workspace_root}"
        )
    for row in entries:
        target_rel = str(row.get("target_file", ""))
        if not target_rel:
            raise RuntimeError("dataset_missing_target_file")
        target_path = (execution_root / Path(target_rel)).resolve()
        if not _is_within(target_path, execution_root):
            raise RuntimeError(
                f"target_file_outside_execution_root: {target_path} not under {execution_root}"
            )


def _default_runtime_from_cfg(cfg: dict[str, Any]) -> dict[str, Any]:
    workspace_root = str(cfg.get("workspace_root", str(DEFAULT_WORKSPACE_ROOT)))
    runtime = dict(cfg)
    runtime.setdefault("execution_root", workspace_root)
    runtime.setdefault("repl_workspace", workspace_root)
    runtime.setdefault("apollo_project_path", str(APOLLO_PROJECT_PATH))
    runtime.setdefault("lake_path", APOLLO_LAKE_PATH)
    runtime.setdefault("verify_timeout", APOLLO_VERIFY_TIMEOUT)
    runtime.setdefault("n_search_procs", 2)
    runtime.setdefault("batch_size", 8)
    runtime.setdefault("lean_max_concurrent_requests", 4)
    runtime.setdefault("data_split", None)
    runtime.setdefault("data_repeat", 1)
    runtime.setdefault(
        "sampler",
        {
            "sample_num": int(runtime.get("n_samples", 8)),
            "log_interval": 8,
            "mode": "cot_goedel_v2",
            "prompt_formatter": "cot_goedel_v2",
            "few_shot_dataset": "",
            "few_shot_num": 0,
        },
    )
    runtime.setdefault("model_args", {})
    runtime.setdefault("monitor_interval_sec", 5.0)
    runtime.setdefault("monitor_stall_sec", float(runtime.get("verify_timeout", APOLLO_VERIFY_TIMEOUT) * 1.5))
    runtime.setdefault("request_timeout_sec", int(runtime.get("verify_timeout", APOLLO_VERIFY_TIMEOUT)) + 30)
    return runtime


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Launch APOLLO parity ablation pipeline.")
    parser.add_argument(
        "--dataset",
        type=str,
        default=str(PROJECT_ROOT / "ablation" / "apollo_only" / "datasets" / "subgradient_single.jsonl"),
    )
    parser.add_argument(
        "--config",
        type=str,
        default=str(PROJECT_ROOT / "ablation" / "apollo_only" / "configs" / "apollo_api_parity.py"),
    )
    parser.add_argument("--log-dir", type=str, default=str(PROJECT_ROOT / "ablation_logs" / f"parity_{_utc_now_tag()}"))
    parser.add_argument("--node-rank", type=int, default=0)
    parser.add_argument("--world-size", type=int, default=1)
    parser.add_argument("--model-backend", type=str, default=None, choices=["api", "vllm"])
    parser.add_argument("--provider", type=str, default=None)
    parser.add_argument("--model", type=str, default=None)
    parser.add_argument("--n-samples", type=int, default=None)
    parser.add_argument("--monitor-interval-sec", type=float, default=None)
    parser.add_argument("--monitor-stall-sec", type=float, default=None)
    parser.add_argument("--request-timeout-sec", type=float, default=None)
    parser.add_argument("--apply-best-candidate", action="store_true")
    parser.add_argument("--quiet", action="store_true")
    return parser


def main() -> int:
    args = build_arg_parser().parse_args()
    cfg = _load_python_config(Path(args.config).resolve())
    runtime_cfg = _default_runtime_from_cfg(cfg)
    if args.model_backend is not None:
        runtime_cfg["model_backend"] = args.model_backend
    if args.provider is not None:
        runtime_cfg["provider"] = args.provider
    if args.model is not None:
        runtime_cfg["model"] = args.model
    if args.n_samples is not None:
        runtime_cfg.setdefault("sampler", {})
        runtime_cfg["sampler"]["sample_num"] = int(args.n_samples)
    if args.monitor_interval_sec is not None:
        runtime_cfg["monitor_interval_sec"] = float(args.monitor_interval_sec)
    if args.monitor_stall_sec is not None:
        runtime_cfg["monitor_stall_sec"] = float(args.monitor_stall_sec)
    if args.request_timeout_sec is not None:
        runtime_cfg["request_timeout_sec"] = float(args.request_timeout_sec)
    if bool(args.apply_best_candidate):
        runtime_cfg["apply_best_candidate"] = True
    if bool(args.quiet):
        runtime_cfg["quiet"] = True

    entries = _load_jsonl(Path(args.dataset).resolve())
    if not entries:
        raise RuntimeError("empty_dataset")

    workspace_root = _resolve_workspace_root(runtime_cfg)
    execution_root = _resolve_execution_root(runtime_cfg, workspace_root)
    _validate_dataset_isolation(entries, execution_root, workspace_root)

    isolation_meta = _build_isolation_meta(runtime_cfg=runtime_cfg, first_entry=entries[0])
    print(json.dumps({"ablation_isolation": isolation_meta}, ensure_ascii=False, indent=2), flush=True)

    log_dir = Path(args.log_dir).resolve()
    log_dir.mkdir(parents=True, exist_ok=True)
    (log_dir / "config.json").write_text(
        json.dumps(runtime_cfg, ensure_ascii=False, indent=2, default=str),
        encoding="utf-8",
    )
    (log_dir / "isolation.json").write_text(
        json.dumps(isolation_meta, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )

    # queue-based loaders/schedulers
    data_loader = JsonlDataLoader(
        data_path=str(Path(args.dataset).resolve()),
        data_split=runtime_cfg.get("data_split", None),
        data_repeat=int(runtime_cfg.get("data_repeat", 1)),
        node_rank=int(args.node_rank),
        world_size=int(args.world_size),
        log_dir=str(log_dir),
    )

    verifier_cfg = {
        "verify_timeout": int(runtime_cfg.get("verify_timeout", APOLLO_VERIFY_TIMEOUT)),
        "apollo_project_path": str(Path(str(runtime_cfg["apollo_project_path"])).resolve()),
        "repl_workspace": str(Path(str(runtime_cfg["repl_workspace"])).resolve()),
        "lake_path": str(runtime_cfg["lake_path"]),
        "execution_root": str(execution_root),
        "workspace_root": str(workspace_root),
        "monitor_interval_sec": float(runtime_cfg.get("monitor_interval_sec", 5.0)),
        "monitor_stall_sec": float(
            runtime_cfg.get(
                "monitor_stall_sec",
                float(runtime_cfg.get("verify_timeout", APOLLO_VERIFY_TIMEOUT)) * 1.5,
            )
        ),
        "request_timeout_sec": float(
            runtime_cfg.get(
                "request_timeout_sec",
                int(runtime_cfg.get("verify_timeout", APOLLO_VERIFY_TIMEOUT)) + 30,
            )
        ),
    }
    verifier_scheduler = VerifierScheduler(
        max_concurrent_requests=int(runtime_cfg.get("lean_max_concurrent_requests", 4)),
        cfg=verifier_cfg,
        name="verifier",
    )

    generator_scheduler = ProcessScheduler(
        batch_size=int(runtime_cfg.get("batch_size", 8)),
        name="generator",
    )
    generator_cfg = {
        "model_backend": str(runtime_cfg.get("model_backend", "api")),
        "provider": str(runtime_cfg.get("provider", runtime_cfg.get("model_args", {}).get("provider", "qwen"))),
        "model": str(runtime_cfg.get("model", runtime_cfg.get("model_args", {}).get("model", "qwen3.5-plus"))),
        "system_prompt": str(runtime_cfg.get("system_prompt", "")),
        "max_tokens": int(runtime_cfg.get("max_tokens", runtime_cfg.get("model_args", {}).get("max_tokens", 4096))),
        "temperature": float(runtime_cfg.get("temperature", runtime_cfg.get("model_args", {}).get("temperature", 0.7))),
        "top_p": float(runtime_cfg.get("top_p", runtime_cfg.get("model_args", {}).get("top_p", 0.95))),
        "model_args": dict(runtime_cfg.get("model_args", {})),
    }
    generator_worker_cls = (
        GeneratorVllmProcess
        if str(runtime_cfg.get("model_backend", "api")) == "vllm"
        else GeneratorProcess
    )
    gen_workers = [
        generator_worker_cls(
            idx=i,
            task_queue=generator_scheduler.task_queue,
            request_statuses=generator_scheduler.request_statuses,
            lock=generator_scheduler.lock,
            cfg=generator_cfg,
        )
        for i in range(max(1, int(runtime_cfg.get("n_search_procs", 2))))
    ]
    for p in gen_workers:
        p.start()
    print(
        f"[Launcher] generator_workers={len(gen_workers)} backend={runtime_cfg.get('model_backend', 'api')}",
        flush=True,
    )

    scheduler = Scheduler({"generator": generator_scheduler, "verifier": verifier_scheduler})
    search_cfg = {
        **runtime_cfg,
        "execution_root": str(execution_root),
    }
    search_processes = [
        SearchProcess(
            idx=i + int(args.node_rank) * max(1, int(runtime_cfg.get("n_search_procs", 2))),
            log_dir=str(log_dir),
            scheduler=scheduler,
            data_loader=data_loader,
            cfg=search_cfg,
        )
        for i in range(min(max(1, int(runtime_cfg.get("n_search_procs", 2))), data_loader.size()))
    ]
    for p in search_processes:
        p.start()
    print(f"[Launcher] search_processes={len(search_processes)}", flush=True)

    status = 0
    try:
        for p in search_processes:
            p.join()
    except Exception as exc:  # noqa: BLE001
        status = 1
        err = {"status": "failed", "error": str(exc), "traceback": traceback.format_exc()}
        (log_dir / "fatal_error.json").write_text(
            json.dumps(err, ensure_ascii=False, indent=2),
            encoding="utf-8",
        )
        print(json.dumps(err, ensure_ascii=False, indent=2), flush=True)
    finally:
        scheduler.close()
        for p in gen_workers:
            p.join(timeout=5.0)
    sample_total, success_total = _collect_success_metrics(log_dir)
    if status == 0 and sample_total > 0 and success_total == 0:
        status = 2
    status_label = "ok" if status == 0 else ("no_solution" if status == 2 else "failed")
    print(
        json.dumps(
            {
                "status": status_label,
                "log_dir": str(log_dir),
                "search_processes": len(search_processes),
                "generator_workers": len(gen_workers),
                "sample_count": sample_total,
                "success_count": success_total,
            },
            ensure_ascii=False,
            indent=2,
        ),
        flush=True,
    )
    return status


if __name__ == "__main__":
    raise SystemExit(main())

