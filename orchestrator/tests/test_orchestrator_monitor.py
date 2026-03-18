"""Regression tests for background launcher argument forwarding."""

from __future__ import annotations

from types import SimpleNamespace

import orchestrator_monitor


def test_start_background_preserves_skip_to_agent9_args(monkeypatch):
    observed = {}

    def _fake_run(cmd, cwd=None, capture_output=None, text=None):
        observed["cmd"] = cmd
        observed["cwd"] = cwd
        observed["capture_output"] = capture_output
        observed["text"] = text
        return SimpleNamespace(returncode=0, stdout="started", stderr="")

    monkeypatch.setattr(orchestrator_monitor.subprocess, "run", _fake_run)
    fake_pid_file = SimpleNamespace(exists=lambda: True, read_text=lambda: "12345")
    monkeypatch.setattr(orchestrator_monitor, "PID_FILE", fake_pid_file)

    result = orchestrator_monitor.start_background(
        [
            "--skip-to-agent9",
            "--spec-file",
            "book/FOML/SubgradientMethod.json",
            "--target-file",
            "Algorithms/SubgradientMethod.lean",
        ]
    )

    assert observed["cmd"] == [
        str(orchestrator_monitor.PROJECT_ROOT / "run_orchestrator_bg.sh"),
        "--skip-to-agent9",
        "--spec-file",
        "book/FOML/SubgradientMethod.json",
        "--target-file",
        "Algorithms/SubgradientMethod.lean",
    ]
    assert observed["cwd"] == orchestrator_monitor.PROJECT_ROOT
    assert observed["capture_output"] is True
    assert observed["text"] is True
    assert result == {"status": "started", "pid": 12345, "output": "started"}
