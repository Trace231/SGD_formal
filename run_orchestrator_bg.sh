#!/bin/bash
# Run orchestrator in background with logging
# Usage: ./run_orchestrator_bg.sh [--spec-file FILE] [--target-file FILE] [--skip-to-agent9]
#
# This script:
# 1. Starts orchestrator in background
# 2. Redirects all output to orchestrator.log
# 3. Records PID for monitoring
# 4. Returns immediately (does not wait for completion)

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
LOG_FILE="$SCRIPT_DIR/orchestrator.log"
PID_FILE="$SCRIPT_DIR/orchestrator.pid"
STATUS_FILE="$SCRIPT_DIR/orchestrator_status.json"

# Build command from arguments without collapsing quoted arguments.
CMD=(python -m orchestrator.main "$@")
printf -v CMD_DISPLAY '%q ' "${CMD[@]}"
CMD_DISPLAY="${CMD_DISPLAY% }"

echo "Starting orchestrator in background..."
echo "Log file: $LOG_FILE"
echo "PID file: $PID_FILE"

# Remove old status file
rm -f "$STATUS_FILE"

# Run in background with nohup
(
  cd "$SCRIPT_DIR" || exit 1
  nohup "${CMD[@]}" > "$LOG_FILE" 2>&1 &
  echo $! > "$PID_FILE"
)
PID="$(cat "$PID_FILE")"

# Save PID
echo $PID > "$PID_FILE"

# Create initial status file
cat > "$STATUS_FILE" << EOF
{
  "pid": $PID,
  "start_time": "$(date -Iseconds)",
  "status": "running",
  "log_file": "$LOG_FILE",
  "command": "$CMD_DISPLAY"
}
EOF

echo "Orchestrator started with PID: $PID"
echo ""
echo "To monitor progress:"
echo "  tail -f $LOG_FILE"
echo "  ./check_orchestrator_status.sh"
echo ""
echo "To wait for completion:"
echo "  ./wait_for_orchestrator.sh"
