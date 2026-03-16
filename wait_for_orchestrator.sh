#!/bin/bash
# Wait for orchestrator to complete and show final results
# Usage: ./wait_for_orchestrator.sh [--timeout SECONDS]
#
# This script:
# 1. Waits for orchestrator process to finish
# 2. Shows progress every 30 seconds
# 3. Displays final results

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PID_FILE="$SCRIPT_DIR/orchestrator.pid"
LOG_FILE="$SCRIPT_DIR/orchestrator.log"

TIMEOUT=${1:-0}  # 0 means no timeout

if [[ ! -f "$PID_FILE" ]]; then
    echo "Error: No orchestrator process found"
    exit 1
fi

PID=$(cat "$PID_FILE")

if ! ps -p $PID > /dev/null 2>&1; then
    echo "Orchestrator already finished"
    ./check_orchestrator_status.sh
    exit 0
fi

echo "Waiting for orchestrator (PID: $PID) to complete..."
echo "Log file: $LOG_FILE"
echo ""

START_TIME=$(date +%s)
CHECK_INTERVAL=30  # Show progress every 30 seconds
LAST_LOG_SIZE=0

while ps -p $PID > /dev/null 2>&1; do
    CURRENT_TIME=$(date +%s)
    ELAPSED=$((CURRENT_TIME - START_TIME))
    
    # Check timeout
    if [[ $TIMEOUT -gt 0 && $ELAPSED -ge $TIMEOUT ]]; then
        echo "Timeout after ${TIMEOUT}s"
        echo "Process still running. Use 'kill $PID' to stop."
        exit 1
    fi
    
    # Show progress
    if [[ -f "$LOG_FILE" ]]; then
        LOG_SIZE=$(wc -c < "$LOG_FILE")
        if [[ $LOG_SIZE -ne $LAST_LOG_SIZE ]]; then
            LAST_LINES=$(tail -n 5 "$LOG_FILE")
            SORRY_COUNT=$(grep -o "sorry_count.*[0-9]*" "$LOG_FILE" | tail -1 | grep -o "[0-9]*" || echo "?")
            PHASE=$(grep -o "\[Phase [0-9]\]" "$LOG_FILE" | tail -1 || echo "?")
            
            echo "[$(date '+%H:%M:%S')] Elapsed: ${ELAPSED}s | Phase: $PHASE | sorry_count: $SORRY_COUNT | Log: $LOG_SIZE bytes"
            echo "  Last: ${LAST_LINES:0:100}..."
            LAST_LOG_SIZE=$LOG_SIZE
        fi
    fi
    
    sleep $CHECK_INTERVAL
done

echo ""
echo "=== Orchestrator Finished ==="
./check_orchestrator_status.sh

# Clean up PID file
rm -f "$PID_FILE"
