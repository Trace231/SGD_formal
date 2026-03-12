#!/usr/bin/env python3
"""Isolated Agent6 glue-filler test with real-time JSONL logging.

This script reuses production `_run_agent6_glue_loop`, but writes into a dedicated
harness staging file so the result is not blocked by pre-existing errors in
`Lib/Glue/Staging/SVRGOuterLoop.lean`.
"""

from __future__ import annotations

import json
import multiprocessing as mp
import os
import re
import sys
import time
import traceback
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


PROJECT_ROOT = Path(__file__).resolve().parent
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

from orchestrator.agents import Agent, ToolRegistry
from orchestrator.main import _run_agent6_glue_loop
from orchestrator.tools import check_lean_have, get_lean_goal, run_lean_verify


TARGET_FILE = "Algorithms/SVRGOuterLoop.lean"
TARGET_ALGO = Path(TARGET_FILE).stem
HARNESS_REL = "Lib/Glue/Staging/SVRGOuterLoop_Agent6Harness.lean"
HARNESS_PATH = PROJECT_ROOT / HARNESS_REL
LOG_PATH = PROJECT_ROOT / "test_agent6_log.jsonl"
TIMEOUT_SEC = int(os.getenv("AGENT6_TEST_TIMEOUT_SEC", "480"))
FORCE_DONE_ON_CLEAN_VERIFY = os.getenv("AGENT6_TEST_FORCE_DONE_ON_CLEAN_VERIFY", "1") == "1"

TARGET_THEOREM_NAME = "svrg_outer_telescope_direct"
GOAL = (
    "α ^ (K + 1) * V₀ + β * (1 - α ^ (K + 1)) * Δ = "
    "α * (α ^ K * V₀ + β * (1 - α ^ K) * Δ) + β * (1 - α) * Δ"
)
ERROR_MESSAGE = (
    "error: Algorithms/SVRGOuterLoop.lean:406:117: unsolved goals\n"
    "error: telescoping step requires algebraic bridge lemma"
)
DIAGNOSIS = (
    "Need a bridge lemma for telescoping. Write theorem `svrg_outer_telescope_direct` "
    "to staging with the exact goal shape and close by algebraic normalization."
)
HYPOTHESES = ["hα_nonneg : 0 ≤ α", "hα_le_one : α ≤ 1"]
EXTRA_CONTEXT = (
    "Please create exactly one theorem in staging. Recommended proof: "
    "`rw [pow_succ, mul_assoc, mul_assoc α (α ^ K) V₀]` then `ring`."
)
STUCK_LINE = 406

HARNESS_TEMPLATE = """import Lib.Glue.Probability
import Lib.Glue.Algebra
import Lib.Glue.Measurable
import Lib.Glue.Calculus
import Algorithms.SVRG

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

/-- Dedicated external harness for Agent6 glue proving tests. -/
"""


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _extract_json_object(reply: str) -> dict[str, Any] | None:
    text = reply.strip()
    if text.startswith("```"):
        text = re.sub(r"^```(?:json)?\s*", "", text)
        text = re.sub(r"\s*```$", "", text)
    try:
        obj = json.loads(text)
    except json.JSONDecodeError:
        return None
    return obj if isinstance(obj, dict) else None


def _jsonl_append(path: Path, payload: dict[str, Any]) -> None:
    with path.open("a", encoding="utf-8") as fh:
        fh.write(json.dumps(payload, ensure_ascii=False) + "\n")
        fh.flush()
        os.fsync(fh.fileno())


def _summarize_log(path: Path) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    if not path.exists():
        return {"exists": False}
    for raw in path.read_text(encoding="utf-8").splitlines():
        raw = raw.strip()
        if not raw:
            continue
        try:
            rows.append(json.loads(raw))
        except json.JSONDecodeError:
            continue

    turns = [r for r in rows if "turn" in r]
    tool_errors = 0
    parameter_errors = 0
    json_errors = 0
    compile_feedback = 0
    for r in turns:
        preview = str(r.get("prompt_preview", ""))
        if preview.startswith("Tool error:"):
            tool_errors += 1
            if (
                "unexpected keyword argument" in preview
                or "multiple values for argument" in preview
                or "missing 2 required positional arguments" in preview
                or "does NOT accept `patch`" in preview
            ):
                parameter_errors += 1
        if preview.startswith("Invalid JSON."):
            json_errors += 1
        if preview.startswith("## run_lean_verify result"):
            compile_feedback += 1

    return {
        "exists": True,
        "total_rows": len(rows),
        "turn_count": len(turns),
        "tool_error_turns": tool_errors,
        "parameter_error_turns": parameter_errors,
        "json_error_turns": json_errors,
        "compile_feedback_turns": compile_feedback,
        "has_agent6_done_event": any(r.get("event") == "agent6_done" for r in rows),
        "has_harness_restored_event": any(r.get("event") == "harness_restored" for r in rows),
    }


class _LoggingAgent(Agent):
    """Wrap Agent.call and append each turn to JSONL immediately."""

    def __init__(self, *args: Any, log_path: Path, **kwargs: Any) -> None:
        super().__init__(*args, **kwargs)
        self._log_path = log_path
        self._turn = 0

    def call(self, user_msg: str) -> str:  # type: ignore[override]
        if (
            FORCE_DONE_ON_CLEAN_VERIFY
            and
            user_msg.startswith("## run_lean_verify result")
            and '"success": true' in user_msg
            and '"exit_code": 0' in user_msg
            and HARNESS_REL in user_msg
        ):
            # Convergence guard for external test: once staging is clean, force done.
            reply = json.dumps(
                {
                    "thought": "Harness staging builds cleanly; glue proof is complete.",
                    "tool": "done",
                    "arguments": {},
                },
                ensure_ascii=False,
            )
        else:
            reply = super().call(user_msg)
        self._turn += 1
        parsed = _extract_json_object(reply)
        _jsonl_append(
            self._log_path,
            {
                "ts": _now_iso(),
                "turn": self._turn,
                "prompt_preview": user_msg[:260],
                "reply_preview": reply[:320],
                "parsed_json": parsed is not None,
                "thought": (parsed or {}).get("thought", ""),
                "tool": (parsed or {}).get("tool", ""),
                "arguments": (parsed or {}).get("arguments", {}),
            },
        )
        return reply


def _build_agent6_registry(target_algo: str) -> ToolRegistry:
    registry = ToolRegistry()
    registry.register_staging_tools(target_algo=target_algo)
    registry.register("get_lean_goal", get_lean_goal)
    registry.register("check_lean_have", check_lean_have)
    return registry


def _init_log(path: Path) -> None:
    if path.exists():
        path.unlink()
    _jsonl_append(
        path,
        {
            "ts": _now_iso(),
            "event": "header",
            "target_file": TARGET_FILE,
            "staging_file": HARNESS_REL,
            "target_theorem": TARGET_THEOREM_NAME,
            "timeout_sec": TIMEOUT_SEC,
        },
    )


def _agent6_worker(result_queue: Any, log_path_str: str) -> None:
    log_path = Path(log_path_str)
    try:
        agent6 = _LoggingAgent("glue_filler", extra_files=[TARGET_FILE], log_path=log_path)
        registry = _build_agent6_registry(TARGET_ALGO)
        success, message = _run_agent6_glue_loop(
            agent6=agent6,
            registry=registry,
            target_file=TARGET_FILE,
            staging_path=HARNESS_PATH,
            staging_rel=HARNESS_REL,
            goal=GOAL,
            error_message=ERROR_MESSAGE,
            diagnosis=DIAGNOSIS,
            target_algo=TARGET_ALGO,
            hypotheses=HYPOTHESES,
            extra_context=EXTRA_CONTEXT,
            stuck_line=STUCK_LINE,
        )
        result_queue.put(
            {
                "ok": True,
                "success": bool(success),
                "message": str(message),
                "turns": getattr(agent6, "_turn", 0),
            }
        )
    except Exception as exc:  # noqa: BLE001
        result_queue.put({"ok": False, "error": str(exc), "traceback": traceback.format_exc()})


def _restore_harness(backup: str | None) -> None:
    if backup is None:
        if HARNESS_PATH.exists():
            HARNESS_PATH.unlink()
    else:
        HARNESS_PATH.write_text(backup, encoding="utf-8")


def run_test() -> int:
    _init_log(LOG_PATH)
    started = time.time()
    exit_code = 1
    backup: str | None = None

    if HARNESS_PATH.exists():
        backup = HARNESS_PATH.read_text(encoding="utf-8")
        _jsonl_append(LOG_PATH, {"ts": _now_iso(), "event": "backup_ok", "bytes": len(backup)})
    else:
        _jsonl_append(LOG_PATH, {"ts": _now_iso(), "event": "backup_missing_create_new"})

    try:
        HARNESS_PATH.write_text(HARNESS_TEMPLATE, encoding="utf-8")
        _jsonl_append(
            LOG_PATH,
            {"ts": _now_iso(), "event": "harness_ready", "bytes": len(HARNESS_TEMPLATE)},
        )
        print(f"[INFO] harness staging prepared: {HARNESS_REL}")
        print(f"[INFO] realtime log: {LOG_PATH}")

        ctx = mp.get_context("spawn")
        result_queue = ctx.Queue()
        worker = ctx.Process(target=_agent6_worker, args=(result_queue, str(LOG_PATH)))
        worker.start()
        worker.join(TIMEOUT_SEC)

        if worker.is_alive():
            _jsonl_append(
                LOG_PATH,
                {"ts": _now_iso(), "event": "timeout_hard", "timeout_sec": TIMEOUT_SEC},
            )
            worker.terminate()
            worker.join(10)
            if worker.is_alive():
                worker.kill()
                worker.join(5)
            print(f"[FAIL] hard timeout after {TIMEOUT_SEC}s")
            exit_code = 124
            return exit_code

        if result_queue.empty():
            _jsonl_append(
                LOG_PATH,
                {
                    "ts": _now_iso(),
                    "event": "worker_no_result",
                    "worker_exitcode": worker.exitcode,
                },
            )
            print("[FAIL] worker finished without result payload")
            exit_code = 125
            return exit_code

        result = result_queue.get()
        if not result.get("ok", False):
            _jsonl_append(
                LOG_PATH,
                {
                    "ts": _now_iso(),
                    "event": "worker_exception",
                    "error": result.get("error", ""),
                    "traceback": result.get("traceback", ""),
                },
            )
            print(f"[FAIL] worker exception: {result.get('error', '')}")
            exit_code = 1
            return exit_code

        success = bool(result.get("success", False))
        message = str(result.get("message", ""))
        turns = int(result.get("turns", 0))
        _jsonl_append(
            LOG_PATH,
            {
                "ts": _now_iso(),
                "event": "agent6_done",
                "success": success,
                "message": message,
                "turns": turns,
            },
        )

        verify_harness = run_lean_verify(HARNESS_REL)
        _jsonl_append(
            LOG_PATH,
            {
                "ts": _now_iso(),
                "event": "harness_verify",
                "exit_code": verify_harness.get("exit_code"),
                "sorry_count": verify_harness.get("sorry_count"),
                "errors_head": (verify_harness.get("errors") or [])[:5],
            },
        )
        print("\n=== Agent6 harness result ===")
        print(f"success: {success}")
        print(message)
        print(
            f"[INFO] harness verify: exit={verify_harness.get('exit_code')} "
            f"sorry={verify_harness.get('sorry_count')}"
        )
        exit_code = 0 if success else 1
        return exit_code
    finally:
        _restore_harness(backup)
        _jsonl_append(LOG_PATH, {"ts": _now_iso(), "event": "harness_restored"})
        summary = _summarize_log(LOG_PATH)
        _jsonl_append(
            LOG_PATH,
            {
                "ts": _now_iso(),
                "event": "summary",
                "elapsed_sec": round(time.time() - started, 2),
                "exit_code": exit_code,
                **summary,
            },
        )
        print("[INFO] harness restored")


if __name__ == "__main__":
    raise SystemExit(run_test())
