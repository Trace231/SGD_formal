"""Long-run watcher for tmux-based sample-test runs."""

from __future__ import annotations

import argparse
import json
import hashlib
import os
import signal
import subprocess
import time
from collections import Counter, deque
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from orchestrator.config import PROJECT_ROOT, WATCH_ANALYSIS_EVERY_N, WATCH_INTERVAL_SEC


@dataclass
class JournalState:
    offsets: dict[str, int]


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {}
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return {}


def _sha256_path(path: Path) -> str:
    if not path.exists():
        return "missing"
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _capture_tmux(tmux_target: str, lines: int = 200) -> str:
    try:
        proc = subprocess.run(
            ["tmux", "capture-pane", "-p", "-t", tmux_target, "-S", f"-{lines}"],
            check=False,
            capture_output=True,
            text=True,
            timeout=10,
        )
    except Exception as exc:
        return f"[tmux capture failed] {exc}"
    return proc.stdout


def _runner_alive(tmux_target: str) -> bool:
    proc = subprocess.run(
        ["tmux", "list-panes", "-t", tmux_target, "-F", "#{pane_id}"],
        check=False,
        capture_output=True,
        text=True,
        timeout=10,
    )
    return proc.returncode == 0


def parse_agent8_decision(captured: str) -> dict[str, Any]:
    latest: dict[str, Any] = {}
    for line in captured.splitlines():
        if "[Agent8] tick=" not in line:
            continue
        parts = line.strip()
        latest = {"raw": parts}
        for token in parts.replace("[Agent8]", "").split():
            if "=" not in token:
                continue
            key, value = token.split("=", 1)
            latest[key.strip()] = value.strip()
    reason = ""
    for line in reversed(captured.splitlines()):
        if "[Agent8] reason:" in line:
            reason = line.split("reason:", 1)[1].strip()
            break
    if latest:
        latest["reason"] = reason
    return latest


def parse_agent9_status(captured: str) -> dict[str, Any]:
    status = {"state": "unknown", "raw": ""}
    for line in reversed(captured.splitlines()):
        if "[Agent9] Plan ready" in line:
            status = {"state": "plan_ready", "raw": line.strip()}
            break
        if "[Agent9] All parse attempts failed" in line:
            status = {"state": "parse_failed", "raw": line.strip()}
            break
        if "Strategy plan unavailable" in line:
            status = {"state": "empty_plan", "raw": line.strip()}
            break
        if "Parse attempt" in line and "[Agent9]" in line:
            status = {"state": "retrying", "raw": line.strip()}
            break
    return status


def inspect_sorry_file(target_file: str) -> dict[str, Any]:
    path = PROJECT_ROOT / target_file
    text = path.read_text(encoding="utf-8") if path.exists() else ""
    headers = {
        "process_zero": "theorem process_zero" in text,
        "process_succ": "theorem process_succ" in text,
        "subgradient_convergence_convex": "theorem subgradient_convergence_convex" in text,
    }
    return {
        "path": target_file,
        "exists": path.exists(),
        "hash": _sha256_path(path),
        "size_bytes": path.stat().st_size if path.exists() else 0,
        "line_count": len(text.splitlines()) if text else 0,
        "header_integrity": all(headers.values()),
        "headers": headers,
        "decl_count": sum(text.count(token) for token in ["theorem ", "lemma "]) if text else 0,
        "content": text,
    }


def _latest_audit(run_id: str) -> Path | None:
    direct = PROJECT_ROOT / "orchestrator" / "audits" / f"audit_{run_id}.json"
    if direct.exists():
        return direct
    candidates = sorted((PROJECT_ROOT / "orchestrator" / "audits").glob(f"audit_*{run_id.split('_', 1)[-1]}.json"))
    return candidates[-1] if candidates else None


def extract_audit_summary(run_id: str) -> dict[str, Any]:
    audit_path = _latest_audit(run_id)
    payload = _read_json(audit_path) if audit_path else {}
    events = payload.get("events", []) if isinstance(payload.get("events", []), list) else []
    latest_compile = {}
    latest_agent8 = {}
    latest_context_mode = {}
    for event in events:
        if event.get("type") == "compile_health_check":
            latest_compile = event
        elif event.get("type") == "agent8_llm_route":
            latest_agent8 = event
        elif event.get("type") == "context_mode":
            latest_context_mode = event
    return {
        "path": str(audit_path.relative_to(PROJECT_ROOT)) if audit_path else "",
        "event_count": len(events),
        "latest_phase": max((int(e.get("phase", 0) or 0) for e in events), default=0),
        "latest_compile_health": latest_compile,
        "latest_agent8_route": latest_agent8,
        "latest_context_mode": latest_context_mode,
    }


def consume_journal(run_id: str, state: JournalState) -> dict[str, Any]:
    base = PROJECT_ROOT / "orchestrator" / "context_journal" / run_id
    latest_entries: dict[str, Any] = {}
    offsets = dict(state.offsets)
    for role in ["sorry_closer", "glue_filler", "interface_auditor", "decision_hub", "strategy_planner"]:
        path = base / f"{role}.jsonl"
        if not path.exists():
            continue
        current = offsets.get(role, 0)
        with path.open("r", encoding="utf-8") as fh:
            fh.seek(current)
            new_lines = fh.readlines()
            offsets[role] = fh.tell()
        if new_lines:
            try:
                latest_entries[role] = json.loads(new_lines[-1])
            except Exception:
                latest_entries[role] = {"raw": new_lines[-1].strip()}
    state.offsets = offsets
    return {"latest_entries": latest_entries, "journal_offsets": offsets}


def classify_labels(samples: list[dict[str, Any]]) -> list[str]:
    labels: set[str] = set()
    if any(not s.get("latest_compile_health", {}).get("healthy", True) for s in samples):
        labels.add("infra_block")
    if sum(1 for s in samples if s.get("latest_agent9_status", {}).get("state") in {"parse_failed", "retrying", "empty_plan"}) >= 3:
        labels.add("agent9_parse_instability")
    sigs = [
        str((s.get("latest_journal_entries", {}).get("decision_hub", {}) or {}).get("canonical_error_signature", ""))
        for s in samples
        if (s.get("latest_journal_entries", {}).get("decision_hub", {}) or {}).get("canonical_error_signature")
    ]
    if sigs and Counter(sigs).most_common(1)[0][1] >= max(3, len(sigs) // 2):
        labels.add("proof_local_stall")
    agent8_actions = [str((s.get("latest_agent8_decision") or {}).get("action", "")) for s in samples]
    if agent8_actions.count("agent7_signature") >= max(3, len(agent8_actions) // 2):
        labels.add("agent7_overrouting")
    prompt_lens = [
        int((s.get("latest_journal_entries", {}).get("strategy_planner", {}) or {}).get("prompt_len", 0) or 0)
        for s in samples
    ]
    if prompt_lens and max(prompt_lens) > 0 and min(prompt_lens) > 0 and max(prompt_lens) >= 2 * min(prompt_lens):
        labels.add("prompt_drift")
    if any(not s.get("sorry_header_integrity", True) for s in samples):
        labels.add("routing_misclassification")
    return sorted(labels)


def build_analysis_markdown(run_id: str, sample_window: list[dict[str, Any]]) -> str:
    agent8_actions = [str((s.get("latest_agent8_decision") or {}).get("action", "unknown")) for s in sample_window]
    compile_states = [bool((s.get("latest_compile_health") or {}).get("healthy", True)) for s in sample_window]
    agent9_states = [str((s.get("latest_agent9_status") or {}).get("state", "unknown")) for s in sample_window]
    header_failures = sum(1 for s in sample_window if not s.get("sorry_header_integrity", True))
    prompt_lengths = [int((s.get("latest_journal_entries", {}).get("strategy_planner", {}) or {}).get("prompt_len", 0) or 0) for s in sample_window]
    sig_counter = Counter(
        str((s.get("latest_journal_entries", {}).get("decision_hub", {}) or {}).get("canonical_error_signature", ""))
        for s in sample_window
        if (s.get("latest_journal_entries", {}).get("decision_hub", {}) or {}).get("canonical_error_signature")
    )
    labels = classify_labels(sample_window)
    main_bottleneck = labels[0] if labels else "stable_observation"
    lines = [
        f"# Sample Test Analysis for {run_id}",
        "",
        f"- Window size: {len(sample_window)} samples",
        f"- Agent8 action distribution: {dict(Counter(agent8_actions))}",
        f"- Compile health healthy count: {sum(compile_states)}/{len(compile_states)}",
        f"- Agent9 states: {dict(Counter(agent9_states))}",
        f"- sorry.lean header regressions: {header_failures}",
        f"- Strategy planner prompt lengths: {prompt_lengths}",
        f"- Repeated error signatures: {dict(sig_counter)}",
        f"- Labels: {labels}",
        f"- Main bottleneck: {main_bottleneck}",
        "",
        "## Suggested Next Step",
        "Do not auto-execute. Review the latest Agent8 decision, the latest Agent9 plan status, and the repeated error signature before changing routing or prompts.",
    ]
    return "\n".join(lines) + "\n"


def _append_jsonl(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as fh:
        fh.write(json.dumps(payload, ensure_ascii=False) + "\n")


def run_watch_loop(*, run_id: str, tmux_target: str, target_file: str, run_dir: Path, stop_sentinel: Path, interval_sec: int, analysis_every_n: int) -> None:
    watch_jsonl = run_dir / "watch.jsonl"
    summary_log = run_dir / "watch_summary.log"
    recent_samples: deque[dict[str, Any]] = deque(maxlen=max(analysis_every_n, 10))
    journal_state = JournalState(offsets={})
    sample_index = 0

    while True:
        if stop_sentinel.exists():
            break
        sample_index += 1
        captured = _capture_tmux(tmux_target, lines=200)
        agent8 = parse_agent8_decision(captured)
        agent9 = parse_agent9_status(captured)
        audit = extract_audit_summary(run_id)
        sorry_info = inspect_sorry_file(target_file)
        journal = consume_journal(run_id, journal_state)
        sample = {
            "ts": _now_iso(),
            "run_id": run_id,
            "sample_index": sample_index,
            "runner_alive": _runner_alive(tmux_target),
            "tmux_target": tmux_target,
            "latest_phase": int(audit.get("latest_phase", 0) or 0),
            "latest_compile_health": audit.get("latest_compile_health", {}),
            "latest_agent8_decision": agent8,
            "latest_agent9_status": agent9,
            "latest_audit_path": audit.get("path", ""),
            "audit_event_count": int(audit.get("event_count", 0) or 0),
            "sorry_file_hash": sorry_info["hash"],
            "sorry_file_size": sorry_info["size_bytes"],
            "sorry_line_count": sorry_info["line_count"],
            "sorry_header_integrity": sorry_info["header_integrity"],
            "journal_offsets": journal.get("journal_offsets", {}),
            "latest_journal_entries": journal.get("latest_entries", {}),
        }
        _append_jsonl(watch_jsonl, sample)
        with summary_log.open("a", encoding="utf-8") as fh:
            fh.write(
                f"[{sample['ts']}] sample={sample_index} phase={sample['latest_phase']} "
                f"agent8={agent8.get('action', 'n/a')} agent9={agent9.get('state', 'n/a')} "
                f"headers_ok={sample['sorry_header_integrity']} audit={sample['audit_event_count']}\n"
            )
        if not sorry_info["header_integrity"]:
            snapshot = run_dir / f"sorry_snapshot_{sample_index:04d}.lean"
            snapshot.write_text(sorry_info["content"], encoding="utf-8")
        recent_samples.append(sample)
        if sample_index % max(1, analysis_every_n) == 0:
            analysis_path = run_dir / f"analysis_{sample_index:04d}.md"
            analysis_path.write_text(build_analysis_markdown(run_id, list(recent_samples)), encoding="utf-8")
        time.sleep(max(1, interval_sec))


def main() -> None:
    parser = argparse.ArgumentParser(description="Watch a tmux-based sample-test run.")
    parser.add_argument("--run-id", required=True)
    parser.add_argument("--tmux-target", required=True)
    parser.add_argument("--target-file", required=True)
    parser.add_argument("--run-dir", required=True)
    parser.add_argument("--stop-sentinel", required=True)
    parser.add_argument("--interval-sec", type=int, default=WATCH_INTERVAL_SEC)
    parser.add_argument("--analysis-every-n", type=int, default=WATCH_ANALYSIS_EVERY_N)
    args = parser.parse_args()

    signal.signal(signal.SIGTERM, lambda *_args: (_ for _ in ()).throw(SystemExit(0)))
    run_watch_loop(
        run_id=args.run_id,
        tmux_target=args.tmux_target,
        target_file=args.target_file,
        run_dir=Path(args.run_dir),
        stop_sentinel=Path(args.stop_sentinel),
        interval_sec=int(args.interval_sec),
        analysis_every_n=int(args.analysis_every_n),
    )


if __name__ == "__main__":
    main()
