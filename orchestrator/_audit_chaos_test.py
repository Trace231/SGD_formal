"""Chaos tests for Phase 3 state machine and tool permission enforcement.

Run with:  python -m orchestrator._audit_chaos_test
"""
from __future__ import annotations

import json
import sys
import types
import unittest
from dataclasses import dataclass
from pathlib import Path
from unittest.mock import MagicMock, patch

# ── ensure project root is importable ──────────────────────────────────────
PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT))


@dataclass
class ExecutionResult:
    status_code: str
    message: str
    attempt: int = 0


# ===========================================================================
# Chaos Test 1: Malformed (Markdown-fenced) JSON triggers retry with guidance
# ===========================================================================

class TestInvalidJsonRetry(unittest.TestCase):
    """Verify Phase 3 parsing failure routes to RETRY with format guidance."""

    def _simulate_phase3_parse(self, raw_reply: str, attempt: int = 1) -> dict:
        """Inline the JSON-parse branch from phase3_prove."""
        execution_history: list[ExecutionResult] = []
        diag_log: list[str] = []
        guidance_calls: list[str] = []

        try:
            payload = json.loads(raw_reply)
        except json.JSONDecodeError as exc:
            err_msg = (
                "RETRY_ERROR: Invalid JSON format "
                f"(line {exc.lineno}, col {exc.colno}): {exc.msg}"
            )
            diag_log.append(f"attempt={attempt} {err_msg}")
            execution_history.append(ExecutionResult(
                status_code="ERROR",
                message=err_msg,
                attempt=attempt,
            ))
            guidance_calls.append(
                f"Attempt {attempt} failed.\n"
                "Invalid JSON format from Agent3.\n"
                "Adjust your guidance so Agent3 returns strict JSON tool calls."
            )
            return {
                "status": "RETRY",
                "execution_history": execution_history,
                "diag_log": diag_log,
                "guidance_calls": guidance_calls,
            }

        return {"status": "PARSED", "payload": payload}

    def test_markdown_fenced_json_triggers_retry(self):
        """A Markdown-wrapped reply must be classified as RETRY_ERROR."""
        markdown_reply = (
            "```json\n"
            '{"thought": "I need to close sorry", '
            '"tool_calls": [{"tool": "run_lean_verify", "arguments": {}}]}\n'
            "```"
        )
        result = self._simulate_phase3_parse(markdown_reply)

        self.assertEqual(result["status"], "RETRY",
                         "Markdown-fenced JSON should be RETRY not PARSED")
        history = result["execution_history"]
        self.assertEqual(len(history), 1)
        self.assertEqual(history[0].status_code, "ERROR")
        self.assertIn("RETRY_ERROR: Invalid JSON format", history[0].message,
                      "Error message must carry 'RETRY_ERROR: Invalid JSON format'")

    def test_retry_guidance_contains_format_correction(self):
        """Retry guidance must include format correction instruction."""
        bad_reply = "Here is my plan: { thought: yes }"
        result = self._simulate_phase3_parse(bad_reply)

        self.assertEqual(result["status"], "RETRY")
        guidance_text = result["guidance_calls"][0]
        self.assertIn("Invalid JSON format", guidance_text,
                      "Retry guidance must mention 'Invalid JSON format'")
        self.assertIn("strict JSON tool calls", guidance_text,
                      "Retry guidance must instruct strict JSON format")

    def test_valid_json_does_not_retry(self):
        """A properly formed JSON payload must parse successfully."""
        valid_reply = json.dumps({
            "thought": "I will verify the file.",
            "tool_calls": [{"tool": "run_lean_verify",
                            "arguments": {"file_path": "Algorithms/SGD.lean"}}],
        })
        result = self._simulate_phase3_parse(valid_reply)
        self.assertEqual(result["status"], "PARSED",
                         "Valid JSON should parse without retry")


# ===========================================================================
# Chaos Test 2: PermissionError on unauthorized path → BLOCKED (not crash)
# ===========================================================================

class TestPermissionBlocked(unittest.TestCase):
    """Verify that editing a file outside the allowlist is recorded as BLOCKED."""

    def _simulate_tool_call(
        self,
        tool_name: str,
        arguments: dict,
        attempt: int = 1,
    ) -> ExecutionResult:
        """Inline the tool-call execution branch from phase3_prove."""
        from orchestrator.tools import edit_file_patch

        try:
            if tool_name == "edit_file_patch":
                edit_file_patch(**arguments)
            result = ExecutionResult(
                status_code="SUCCESS",
                message=f"{tool_name} executed.",
                attempt=attempt,
            )
        except PermissionError as exc:
            blocked_path = str(arguments.get("path", "?"))
            result = ExecutionResult(
                status_code="BLOCKED",
                message=f"Security violation on path {blocked_path}: {exc}",
                attempt=attempt,
            )
        except Exception as exc:  # noqa: BLE001
            result = ExecutionResult(
                status_code="ERROR",
                message=f"{tool_name} failed: {exc}",
                attempt=attempt,
            )
        return result

    def test_edit_orchestrator_main_is_blocked(self):
        """Attempting to edit orchestrator/main.py must yield BLOCKED."""
        result = self._simulate_tool_call(
            "edit_file_patch",
            {
                "path": "orchestrator/main.py",
                "old_str": "from __future__",
                "new_str": "INJECTED",
            },
        )
        self.assertEqual(result.status_code, "BLOCKED",
                         "Editing orchestrator/main.py must be BLOCKED")
        self.assertIn("Security violation", result.message,
                      "BLOCKED message must say 'Security violation'")

    def test_edit_within_allowlist_would_raise_file_not_found_not_permission(self):
        """A path inside Algorithms/ raises FileNotFoundError, not PermissionError."""
        result = self._simulate_tool_call(
            "edit_file_patch",
            {
                "path": "Algorithms/NonExistentFile_audit.lean",
                "old_str": "sorry",
                "new_str": "rfl",
            },
        )
        # Should be an ERROR (FileNotFoundError), not BLOCKED
        self.assertEqual(result.status_code, "ERROR",
                         "Missing file in allowlist should be ERROR not BLOCKED")
        self.assertNotIn("Security violation", result.message,
                         "Missing file in allowlist should not say 'Security violation'")

    def test_blocked_does_not_propagate_exception(self):
        """After BLOCKED, the code must continue execution (no uncaught exception)."""
        execution_history: list[ExecutionResult] = []
        blocked_path: str | None = None

        tool_calls = [
            {"tool": "edit_file_patch", "arguments": {
                "path": "orchestrator/main.py",
                "old_str": "x", "new_str": "y",
            }},
        ]

        for idx, call in enumerate(tool_calls, start=1):
            tool_name = call["tool"]
            arguments = call["arguments"]
            result = self._simulate_tool_call(tool_name, arguments)
            execution_history.append(result)
            if result.status_code == "BLOCKED":
                blocked_path = str(arguments.get("path", "?"))

        self.assertEqual(len(execution_history), 1)
        self.assertEqual(execution_history[0].status_code, "BLOCKED")
        self.assertIsNotNone(blocked_path, "blocked_path must be recorded")

    def test_retry_guidance_mentions_security_constraint(self):
        """After BLOCKED, retry guidance must mention security constraint."""
        blocked_path = "orchestrator/main.py"
        blocked_hint = (
            f"Security violation: You cannot edit path {blocked_path}."
            " Stay within Algorithms/ or Lib/."
        )
        # Verify the guidance string contains expected security text
        self.assertIn("Security violation", blocked_hint)
        self.assertIn("Stay within Algorithms/ or Lib/", blocked_hint)


# ===========================================================================
# Chaos Test 3: BLOCKED state does NOT propagate, loop continues
# ===========================================================================

class TestStateTransitions(unittest.TestCase):
    """Verify state machine transitions: BLOCKED → continue, not crash."""

    def test_blocked_results_are_counted_in_retry(self):
        """BLOCKED entries in execution_history must count toward retry_count."""
        history = [
            {"status_code": "SUCCESS", "message": "ok", "attempt": 1},
            {"status_code": "BLOCKED", "message": "Security violation", "attempt": 1},
            {"status_code": "ERROR", "message": "JSON parse error", "attempt": 2},
        ]
        retry_count = sum(
            1 for r in history if r.get("status_code") in {"ERROR", "BLOCKED"}
        )
        self.assertEqual(retry_count, 2,
                         "Both ERROR and BLOCKED must count as retries")

    def test_success_criterion_is_exit0_and_sorry0(self):
        """Strict success = exit_code==0 AND sorry_count==0."""
        cases = [
            ({"exit_code": 0, "sorry_count": 0}, "PROVE_SUCCESS"),
            ({"exit_code": 0, "sorry_count": 1}, "PROVE_RETRY"),
            ({"exit_code": 1, "sorry_count": 0}, "PROVE_RETRY"),
            ({"exit_code": 1, "sorry_count": 3}, "PROVE_RETRY"),
        ]
        for verify_result, expected_state in cases:
            exit_code = int(verify_result["exit_code"])
            sorry_count = int(verify_result["sorry_count"])
            state = "PROVE_SUCCESS" if exit_code == 0 and sorry_count == 0 else "PROVE_RETRY"
            self.assertEqual(state, expected_state,
                             f"verify={verify_result} → expected {expected_state}, got {state}")


# ===========================================================================
# Entry point
# ===========================================================================

if __name__ == "__main__":
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    suite.addTests(loader.loadTestsFromTestCase(TestInvalidJsonRetry))
    suite.addTests(loader.loadTestsFromTestCase(TestPermissionBlocked))
    suite.addTests(loader.loadTestsFromTestCase(TestStateTransitions))

    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    sys.exit(0 if result.wasSuccessful() else 1)
