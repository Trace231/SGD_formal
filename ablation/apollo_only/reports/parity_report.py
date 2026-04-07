#!/usr/bin/env python3
"""Build parity metrics summary from APOLLO-parity logs."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def _iter_summary_files(log_dir: Path) -> list[Path]:
    return sorted(log_dir.glob("**/summary.json"))


def _iter_failure_jsonl_files(log_dir: Path) -> list[Path]:
    return sorted(log_dir.glob("**/failure-*.jsonl"))


def _failure_distribution(log_dir: Path) -> dict[str, int]:
    out: dict[str, int] = {}
    for p in _iter_failure_jsonl_files(log_dir):
        with p.open("r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    obj = json.loads(line)
                except Exception:
                    continue
                result = obj.get("result", {})
                kind = str(result.get("failure_kind", "unknown") or "unknown")
                out[kind] = out.get(kind, 0) + 1
    return out


def build_report(log_dir: Path) -> dict:
    files = _iter_summary_files(log_dir)
    total_problems = len(files)
    total_samples = 0
    total_success = 0
    total_gen_time = 0.0
    total_verify_time = 0.0
    for p in files:
        obj = json.loads(p.read_text(encoding="utf-8"))
        total_samples += int(obj.get("sample_count", 0))
        total_success += int(obj.get("success_count", 0))
        total_gen_time += float(obj.get("sample_time", 0.0) or 0.0)
        total_verify_time += float(obj.get("verify_time", 0.0) or 0.0)

    end_to_end = total_gen_time + total_verify_time
    return {
        "log_dir": str(log_dir.resolve()),
        "problem_count": total_problems,
        "sample_count": total_samples,
        "success_count": total_success,
        "success_rate": (total_success / total_samples) if total_samples > 0 else 0.0,
        "generation_time_total": total_gen_time,
        "verification_time_total": total_verify_time,
        "end_to_end_time_total": end_to_end,
        "samples_per_second": (total_samples / end_to_end) if end_to_end > 0 else 0.0,
        "failure_distribution": _failure_distribution(log_dir),
    }


def _safe_delta(a: float, b: float) -> float:
    return float(a) - float(b)


def build_comparison_report(parity_log_dir: Path, baseline_log_dir: Path) -> dict:
    parity = build_report(parity_log_dir)
    baseline = build_report(baseline_log_dir)
    return {
        "parity": parity,
        "baseline": baseline,
        "delta": {
            "success_rate": _safe_delta(parity["success_rate"], baseline["success_rate"]),
            "samples_per_second": _safe_delta(parity["samples_per_second"], baseline["samples_per_second"]),
            "generation_time_total": _safe_delta(
                parity["generation_time_total"], baseline["generation_time_total"]
            ),
            "verification_time_total": _safe_delta(
                parity["verification_time_total"], baseline["verification_time_total"]
            ),
            "end_to_end_time_total": _safe_delta(
                parity["end_to_end_time_total"], baseline["end_to_end_time_total"]
            ),
            "sample_count": _safe_delta(parity["sample_count"], baseline["sample_count"]),
            "success_count": _safe_delta(parity["success_count"], baseline["success_count"]),
            "failure_distribution": {
                k: int(parity["failure_distribution"].get(k, 0)) - int(baseline["failure_distribution"].get(k, 0))
                for k in set(parity["failure_distribution"]) | set(baseline["failure_distribution"])
            },
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Generate APOLLO parity summary report.")
    parser.add_argument("--log-dir", type=str, required=True)
    parser.add_argument("--baseline-log-dir", type=str, default=None)
    args = parser.parse_args()
    if args.baseline_log_dir:
        report = build_comparison_report(
            Path(args.log_dir),
            Path(args.baseline_log_dir),
        )
    else:
        report = build_report(Path(args.log_dir))
    print(json.dumps(report, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

