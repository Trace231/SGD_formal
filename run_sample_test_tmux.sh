#!/bin/bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"

if ! command -v tmux >/dev/null 2>&1; then
  echo "tmux is required but not installed"
  exit 1
fi

RUN_TS="$(date -u +%Y%m%d_%H%M%S)"
RUN_ID="${ORCHESTRATOR_RUN_ID_OVERRIDE:-${RUN_TS}_sorry_sample}"
SESSION_NAME="${SAMPLE_TEST_SESSION:-sample_sorry}"
WINDOW_NAME="${SAMPLE_TEST_WINDOW:-$RUN_ID}"
TARGET_FILE="${TARGET_FILE:-Algorithms/sorry.lean}"
RUN_DIR="$SCRIPT_DIR/orchestrator/watch_logs/$RUN_ID"
STOP_SENTINEL="$RUN_DIR/STOP"
CURRENT_RUN="$SCRIPT_DIR/orchestrator/watch_logs/current_run.json"
RUNNER_LOG="$RUN_DIR/runner.log"
CLEANUP_LOG="$RUN_DIR/cleanup.json"

mkdir -p "$RUN_DIR"
rm -f "$STOP_SENTINEL"

python -m orchestrator.sample_test_cleanup > "$CLEANUP_LOG"

EXCLUDE_GLOBS="orchestrator/audits/**,orchestrator/context_journal/**,orchestrator/watch_logs/**,Algorithms/SubgradientMethod*.lean,Algorithms/test.lean"
BASE_CMD=(python -m orchestrator.main
  --algorithm sorry
  --update-rule "w_{t+1} = w_t - η g_t"
  --proof-sketch "Use the existing scaffold"
  --archetype B
  --target-file "$TARGET_FILE"
  --skip-to-agent9
  --progress-detail compact)
if [[ $# -gt 0 ]]; then
  BASE_CMD+=("$@")
fi
printf -v CMD_DISPLAY '%q ' "${BASE_CMD[@]}"
CMD_DISPLAY="${CMD_DISPLAY% }"

RUNNER_CMD="cd $(printf '%q' "$SCRIPT_DIR") && \
export SAMPLE_TEST_MODE=1 && \
export DISABLE_PHASE4_PERSISTENCE=1 && \
export CONTEXT_JOURNAL_ENABLED=1 && \
export MANUAL_STOP_ONLY=1 && \
export WATCH_INTERVAL_SEC=600 && \
export WATCH_ANALYSIS_EVERY_N=10 && \
export ORCHESTRATOR_AUDIT=1 && \
export SGD_AUDIT_FULL_PROMPTS=1 && \
export SGD_AUDIT_CODE_PATCH=1 && \
export RUNTIME_ARTIFACT_EXCLUDE_GLOBS=$(printf '%q' "$EXCLUDE_GLOBS") && \
export ORCHESTRATOR_RUN_ID_OVERRIDE=$(printf '%q' "$RUN_ID") && \
$CMD_DISPLAY 2>&1 | tee $(printf '%q' "$RUNNER_LOG")"

if tmux has-session -t "$SESSION_NAME" 2>/dev/null; then
  RUNNER_PANE="$(tmux new-window -d -t "$SESSION_NAME" -n "$WINDOW_NAME" -P -F '#{pane_id}' "$RUNNER_CMD")"
else
  RUNNER_PANE="$(tmux new-session -d -s "$SESSION_NAME" -n "$WINDOW_NAME" -P -F '#{pane_id}' "$RUNNER_CMD")"
fi
TMUX_TARGET="$SESSION_NAME:$WINDOW_NAME"
WATCHER_CMD="cd $(printf '%q' "$SCRIPT_DIR") && python -m orchestrator.sample_test_watch --run-id $(printf '%q' "$RUN_ID") --tmux-target $(printf '%q' "$RUNNER_PANE") --target-file $(printf '%q' "$TARGET_FILE") --run-dir $(printf '%q' "$RUN_DIR") --stop-sentinel $(printf '%q' "$STOP_SENTINEL") --interval-sec 600 --analysis-every-n 10"
WATCHER_PANE="$(tmux split-window -h -P -F '#{pane_id}' -t "$RUNNER_PANE" "$WATCHER_CMD")"

python - <<PY
import json
from pathlib import Path
manifest = {
    "run_id": "$RUN_ID",
    "session_name": "$SESSION_NAME",
    "window_name": "$WINDOW_NAME",
    "tmux_target": "$TMUX_TARGET",
    "runner_pane": "$RUNNER_PANE",
    "watcher_pane": "$WATCHER_PANE",
    "command": "$CMD_DISPLAY",
    "target_file": "$TARGET_FILE",
    "start_time": "$(date -Iseconds)",
    "run_dir": "$RUN_DIR",
    "cleanup_log": "$CLEANUP_LOG",
    "runner_log": "$RUNNER_LOG",
    "stop_sentinel": "$STOP_SENTINEL",
    "stop_policy": "manual_only"
}
run_dir = Path("$RUN_DIR")
run_dir.mkdir(parents=True, exist_ok=True)
(run_dir / "run_manifest.json").write_text(json.dumps(manifest, indent=2, ensure_ascii=False), encoding="utf-8")
Path("$CURRENT_RUN").write_text(json.dumps(manifest, indent=2, ensure_ascii=False), encoding="utf-8")
PY

echo "Sample test started"
echo "  run_id: $RUN_ID"
echo "  session: $SESSION_NAME"
echo "  window: $WINDOW_NAME"
echo "  target: $TARGET_FILE"
echo "  runner pane: $RUNNER_PANE"
echo "  watcher pane: $WATCHER_PANE"
echo "  attach: tmux attach -t $SESSION_NAME"
echo "  stop:   ./stop_sample_test.sh"
