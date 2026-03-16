#!/bin/bash
# Check orchestrator background status
# Usage: ./check_orchestrator_status.sh

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PID_FILE="$SCRIPT_DIR/orchestrator.pid"
LOG_FILE="$SCRIPT_DIR/orchestrator.log"
STATUS_FILE="$SCRIPT_DIR/orchestrator_status.json"

if [[ ! -f "$PID_FILE" ]]; then
    echo "No orchestrator process found (no PID file)"
    exit 1
fi

PID=$(cat "$PID_FILE")

# Check if process is running
if ps -p $PID > /dev/null 2>&1; then
    STATUS="running"
    
    # Get log file stats
    if [[ -f "$LOG_FILE" ]]; then
        LOG_SIZE=$(wc -c < "$LOG_FILE")
        LAST_LINES=$(tail -n 20 "$LOG_FILE")
        
        # Try to extract sorry_count from log
        SORRY_COUNT=$(grep -o "sorry_count.*[0-9]*" "$LOG_FILE" | tail -1 | grep -o "[0-9]*" || echo "unknown")
        
        # Try to extract current phase
        CURRENT_PHASE=$(grep -o "\[Phase [0-9]\]" "$LOG_FILE" | tail -1 || echo "unknown")
        
        # Count lines
        LOG_LINES=$(wc -l < "$LOG_FILE")
    else
        LOG_SIZE=0
        LAST_LINES="Log file not found"
        SORRY_COUNT="unknown"
        CURRENT_PHASE="unknown"
        LOG_LINES=0
    fi
    
    # Get process runtime
    ELAPSED=$(ps -p $PID -o etime= 2>/dev/null || echo "unknown")
    
    echo "=== Orchestrator Status ==="
    echo "PID: $PID"
    echo "Status: RUNNING"
    echo "Elapsed time: $ELAPSED"
    echo "Current phase: $CURRENT_PHASE"
    echo "Last known sorry_count: $SORRY_COUNT"
    echo "Log file size: $LOG_SIZE bytes ($LOG_LINES lines)"
    echo ""
    echo "=== Last 20 lines of log ==="
    echo "$LAST_LINES"
    echo ""
    echo "=== Full log: tail -f $LOG_FILE ==="
    
    # Update status file
    cat > "$STATUS_FILE" << EOF
{
  "pid": $PID,
  "status": "running",
  "elapsed": "$ELAPSED",
  "log_size": $LOG_SIZE,
  "log_lines": $LOG_LINES,
  "sorry_count": "$SORRY_COUNT",
  "phase": "$CURRENT_PHASE",
  "check_time": "$(date -Iseconds)"
}
EOF
    
    exit 0
else
    # Process not running, check exit code from log
    if [[ -f "$LOG_FILE" ]]; then
        # Check for success/failure in log
        if grep -q "Task completed successfully" "$LOG_FILE" || grep -q "Success.*sorry_count.*0" "$LOG_FILE"; then
            EXIT_STATUS="success"
        elif grep -q "error\|Error\|FAILED\|Exception" "$LOG_FILE"; then
            EXIT_STATUS="failed"
        else
            EXIT_STATUS="unknown"
        fi
        
        LAST_LINES=$(tail -n 30 "$LOG_FILE")
    else
        EXIT_STATUS="not_found"
        LAST_LINES="Log file not found"
    fi
    
    echo "=== Orchestrator Status ==="
    echo "PID: $PID (not running)"
    echo "Status: COMPLETED ($EXIT_STATUS)"
    echo ""
    echo "=== Last 30 lines of log ==="
    echo "$LAST_LINES"
    
    # Update status file
    cat > "$STATUS_FILE" << EOF
{
  "pid": $PID,
  "status": "$EXIT_STATUS",
  "end_time": "$(date -Iseconds)",
  "log_file": "$LOG_FILE"
}
EOF
    
    exit 0
fi
