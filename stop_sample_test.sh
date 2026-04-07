#!/bin/bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CURRENT_RUN="$SCRIPT_DIR/orchestrator/watch_logs/current_run.json"

if [[ ! -f "$CURRENT_RUN" ]]; then
  echo "No active sample-test manifest found"
  exit 1
fi

read_json() {
  python - <<PY
import json
from pathlib import Path
obj = json.loads(Path("$CURRENT_RUN").read_text(encoding="utf-8"))
print(obj.get("$1", ""))
PY
}

RUN_ID="$(read_json run_id)"
RUN_DIR="$(read_json run_dir)"
STOP_SENTINEL="$(read_json stop_sentinel)"
RUNNER_PANE="$(read_json runner_pane)"
WATCHER_PANE="$(read_json watcher_pane)"
MANIFEST_PATH="$RUN_DIR/run_manifest.json"

mkdir -p "$RUN_DIR"
touch "$STOP_SENTINEL"

tmux send-keys -t "$RUNNER_PANE" C-c 2>/dev/null || true
tmux send-keys -t "$WATCHER_PANE" C-c 2>/dev/null || true

python - <<PY
import json
from pathlib import Path
path = Path("$MANIFEST_PATH")
if path.exists():
    data = json.loads(path.read_text(encoding="utf-8"))
else:
    data = {"run_id": "$RUN_ID"}
data["stop_requested_at"] = "$(date -Iseconds)"
path.write_text(json.dumps(data, indent=2, ensure_ascii=False), encoding="utf-8")
PY

echo "Stop requested for run_id=$RUN_ID"
echo "Sentinel: $STOP_SENTINEL"
