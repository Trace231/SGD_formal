#!/usr/bin/env python3
"""
Monitor orchestrator background execution.
This script can be called by Trae Agent to check orchestrator progress.

Usage:
    python orchestrator_monitor.py status    # Check current status
    python orchestrator_monitor.py wait      # Wait for completion
    python orchestrator_monitor.py logs      # Show last N lines
    python orchestrator_monitor.py start     # Start in background
"""

import json
import os
import sys
import subprocess
from pathlib import Path
from datetime import datetime

PROJECT_ROOT = Path(__file__).parent
PID_FILE = PROJECT_ROOT / "orchestrator.pid"
LOG_FILE = PROJECT_ROOT / "orchestrator.log"
STATUS_FILE = PROJECT_ROOT / "orchestrator_status.json"


def check_status():
    """Check orchestrator status and return dict."""
    if not PID_FILE.exists():
        return {
            "status": "not_running",
            "message": "No orchestrator process found"
        }
    
    pid = int(PID_FILE.read_text().strip())
    
    # Check if process is running
    try:
        os.kill(pid, 0)
        is_running = True
    except OSError:
        is_running = False
    
    if not is_running:
        return {
            "status": "completed",
            "pid": pid,
            "message": "Process finished"
        }
    
    # Process is running
    result = {
        "status": "running",
        "pid": pid,
        "timestamp": datetime.now().isoformat()
    }
    
    # Read log file
    if LOG_FILE.exists():
        content = LOG_FILE.read_text()
        lines = content.splitlines()
        
        result["log_lines"] = len(lines)
        result["log_size"] = len(content)
        
        # Extract sorry_count
        for line in reversed(lines[-50:]):
            if "sorry_count" in line:
                import re
                match = re.search(r"sorry_count.*?(\d+)", line)
                if match:
                    result["sorry_count"] = int(match.group(1))
                    break
        
        # Extract phase
        for line in reversed(lines[-20:]):
            if "[Phase" in line:
                import re
                match = re.search(r"\[Phase (\d+)\]", line)
                if match:
                    result["current_phase"] = int(match.group(1))
                    break
        
        # Last few lines
        result["last_lines"] = lines[-10:]
    
    return result


def start_background(args):
    """Start orchestrator in background."""
    cmd = [
        str(PROJECT_ROOT / "run_orchestrator_bg.sh")
    ] + args
    
    result = subprocess.run(cmd, cwd=PROJECT_ROOT, capture_output=True, text=True)
    
    if result.returncode == 0:
        # Read PID
        if PID_FILE.exists():
            pid = int(PID_FILE.read_text().strip())
            return {
                "status": "started",
                "pid": pid,
                "output": result.stdout
            }
    
    return {
        "status": "failed",
        "error": result.stderr,
        "output": result.stdout
    }


def wait_for_completion(timeout=0):
    """Wait for orchestrator to complete."""
    if not PID_FILE.exists():
        return {
            "status": "error",
            "message": "No orchestrator process found"
        }
    
    pid = int(PID_FILE.read_text().strip())
    start_time = datetime.now()
    
    import time
    while True:
        # Check if process is running
        try:
            os.kill(pid, 0)
        except OSError:
            break
        
        # Check timeout
        if timeout > 0:
            elapsed = (datetime.now() - start_time).total_seconds()
            if elapsed >= timeout:
                return {
                    "status": "timeout",
                    "elapsed": elapsed,
                    "pid": pid
                }
        
        # Wait before next check
        time.sleep(10)
    
    # Process finished
    return {
        "status": "completed",
        "elapsed": (datetime.now() - start_time).total_seconds(),
        "final_status": check_status()
    }


def show_logs(lines=20):
    """Show last N lines of log."""
    if not LOG_FILE.exists():
        return {
            "status": "no_log",
            "message": "Log file not found"
        }
    
    content = LOG_FILE.read_text()
    all_lines = content.splitlines()
    last_lines = all_lines[-lines:] if len(all_lines) > lines else all_lines
    
    return {
        "status": "success",
        "total_lines": len(all_lines),
        "shown_lines": len(last_lines),
        "lines": last_lines
    }


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    command = sys.argv[1]
    
    if command == "status":
        result = check_status()
        print(json.dumps(result, indent=2))
    
    elif command == "start":
        # Remaining args are orchestrator args
        args = sys.argv[2:]
        result = start_background(args)
        print(json.dumps(result, indent=2))
    
    elif command == "wait":
        timeout = int(sys.argv[2]) if len(sys.argv) > 2 else 0
        result = wait_for_completion(timeout)
        print(json.dumps(result, indent=2))
    
    elif command == "logs":
        lines = int(sys.argv[2]) if len(sys.argv) > 2 else 20
        result = show_logs(lines)
        print(json.dumps(result, indent=2))
    
    else:
        print(f"Unknown command: {command}")
        print(__doc__)
        sys.exit(1)


if __name__ == "__main__":
    main()
