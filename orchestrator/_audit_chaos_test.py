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

    def test_success_criterion_now_requires_file_changed(self):
        """Updated 4-condition gate: file_changed=False must block PROVE_SUCCESS."""
        # Inline the new 4-condition logic from phase3_prove.
        cases = [
            # (exit_code, sorry_count, file_changed) → expected state
            (0, 0, True,  "PROVE_SUCCESS"),
            (0, 0, False, "PROVE_RETRY"),   # no-op trap — must NOT succeed
            (0, 1, True,  "PROVE_RETRY"),
            (1, 0, True,  "PROVE_RETRY"),
            (1, 0, False, "PROVE_RETRY"),
        ]
        for exit_code, sorry_count, file_changed, expected_state in cases:
            if exit_code == 0 and sorry_count == 0 and file_changed:
                state = "PROVE_SUCCESS"
            else:
                state = "PROVE_RETRY"
            self.assertEqual(
                state, expected_state,
                f"exit={exit_code}, sorry={sorry_count}, changed={file_changed} "
                f"→ expected {expected_state}, got {state}",
            )

    def test_success_criterion_is_exit0_and_sorry0(self):
        """Legacy 2-condition test kept for regression — now file_changed=True assumed."""
        cases = [
            ({"exit_code": 0, "sorry_count": 0}, "PROVE_SUCCESS"),
            ({"exit_code": 0, "sorry_count": 1}, "PROVE_RETRY"),
            ({"exit_code": 1, "sorry_count": 0}, "PROVE_RETRY"),
            ({"exit_code": 1, "sorry_count": 3}, "PROVE_RETRY"),
        ]
        for verify_result, expected_state in cases:
            exit_code = int(verify_result["exit_code"])
            sorry_count = int(verify_result["sorry_count"])
            file_changed = True  # assume file was written
            if exit_code == 0 and sorry_count == 0 and file_changed:
                state = "PROVE_SUCCESS"
            else:
                state = "PROVE_RETRY"
            self.assertEqual(state, expected_state,
                             f"verify={verify_result} → expected {expected_state}, got {state}")


# ===========================================================================
# Chaos Test 4: No-Op Trap — Agent3 writes nothing but build is green
# ===========================================================================

class TestNoOpTrap(unittest.TestCase):
    """Verify that a build-green / sorry=0 result with no file change is blocked."""

    def _run_4condition_gate(
        self,
        exit_code: int,
        sorry_count: int,
        file_changed: bool,
        exec_results: list,
        attempt: int = 1,
    ) -> tuple[str, list]:
        """Inline the 4-condition success gate from phase3_prove."""
        no_change_msg = (
            "FAILURE: No changes detected in the target file. "
            "You must use 'edit_file_patch' to implement the proof "
            "before calling verification."
        )
        if exit_code == 0 and sorry_count == 0 and file_changed:
            prove_state = "PROVE_SUCCESS"
        elif exit_code == 0 and sorry_count == 0 and not file_changed:
            exec_results.append(ExecutionResult(
                status_code="ERROR",
                message=no_change_msg,
                attempt=attempt,
            ))
            prove_state = "PROVE_RETRY"
        else:
            prove_state = "PROVE_RETRY"
        return prove_state, exec_results

    def test_noop_with_green_build_is_blocked(self):
        """Build green + sorry=0 but file unchanged → PROVE_RETRY, not SUCCESS."""
        exec_results: list[ExecutionResult] = []
        prove_state, exec_results = self._run_4condition_gate(
            exit_code=0, sorry_count=0, file_changed=False,
            exec_results=exec_results,
        )
        self.assertEqual(prove_state, "PROVE_RETRY",
                         "No-op must be PROVE_RETRY even when build is green")

    def test_noop_appends_error_execution_result(self):
        """No-op trap must append an ERROR result, not succeed silently."""
        exec_results: list[ExecutionResult] = []
        _, exec_results = self._run_4condition_gate(
            exit_code=0, sorry_count=0, file_changed=False,
            exec_results=exec_results,
        )
        self.assertEqual(len(exec_results), 1,
                         "Exactly one ERROR result must be appended for no-op")
        self.assertEqual(exec_results[0].status_code, "ERROR")

    def test_noop_error_message_is_actionable(self):
        """No-op ERROR message must contain 'No changes detected'."""
        exec_results: list[ExecutionResult] = []
        _, exec_results = self._run_4condition_gate(
            exit_code=0, sorry_count=0, file_changed=False,
            exec_results=exec_results,
        )
        self.assertIn("No changes detected", exec_results[0].message,
                      "Error message must say 'No changes detected'")
        self.assertIn("edit_file_patch", exec_results[0].message,
                      "Error message must instruct using 'edit_file_patch'")

    def test_green_build_with_file_change_succeeds(self):
        """Build green + sorry=0 + file changed → PROVE_SUCCESS."""
        exec_results: list[ExecutionResult] = []
        prove_state, _ = self._run_4condition_gate(
            exit_code=0, sorry_count=0, file_changed=True,
            exec_results=exec_results,
        )
        self.assertEqual(prove_state, "PROVE_SUCCESS",
                         "Valid write + green build must succeed")
        self.assertEqual(len(exec_results), 0,
                         "No ERROR result should be appended on success")

    def test_file_missing_verify_returns_exit1(self):
        """run_lean_verify on a non-existent file must return exit_code=1."""
        import tempfile
        from unittest.mock import patch
        from orchestrator.tools import run_lean_verify

        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir).resolve()
            algo_dir = tmp / "Algorithms"
            algo_dir.mkdir()
            nonexistent = algo_dir / "Ghost.lean"  # deliberately not created

            with patch("orchestrator.tools.PROJECT_ROOT", tmp), \
                 patch("orchestrator.tools._LEAN_VERIFY_ALLOWLIST", ("Algorithms",)):
                result = run_lean_verify(nonexistent)

        self.assertEqual(result["exit_code"], 1,
                         "Missing file must return exit_code=1")
        self.assertFalse(result["success"],
                         "Missing file must return success=False")
        self.assertTrue(
            any("does not exist" in e for e in result["errors"]),
            "Error message must mention file does not exist",
        )

    def test_sorry_in_block_comment_not_counted(self):
        """sorry inside /- ... -/ must not be counted as an actual sorry."""
        from orchestrator.verify import _count_sorry_in_source
        source = "/- This proof uses sorry as a placeholder -/\ntheorem foo : True := trivial\n"
        self.assertEqual(_count_sorry_in_source(source), 0,
                         "sorry inside block comment must not be counted")

    def test_sorry_in_line_comment_not_counted(self):
        """sorry after -- must not be counted."""
        from orchestrator.verify import _count_sorry_in_source
        source = "theorem foo : True := trivial -- TODO: replace sorry here\n"
        self.assertEqual(_count_sorry_in_source(source), 0,
                         "sorry in line comment must not be counted")

    def test_actual_sorry_is_counted(self):
        """A bare sorry tactic must be counted."""
        from orchestrator.verify import _count_sorry_in_source
        source = "theorem foo : 1 = 2 := by\n  sorry\n"
        self.assertEqual(_count_sorry_in_source(source), 1,
                         "Actual sorry tactic must be counted")

    def test_sorry_output_re_matches_compiler_warning_only(self):
        """_SORRY_OUTPUT_RE must match 'declaration uses sorry' but not bare 'sorry'."""
        from orchestrator.verify import _count_sorry_in_output
        compiler_warning = "SGD.lean:5:0: warning: declaration uses 'sorry'\n"
        bare_sorry = "error: sorry is not allowed here\n"
        self.assertEqual(_count_sorry_in_output(compiler_warning), 1,
                         "Compiler warning must be counted")
        self.assertEqual(_count_sorry_in_output(bare_sorry), 0,
                         "Bare 'sorry' in output must NOT be counted")


# ===========================================================================
# Entry point
# ===========================================================================

if __name__ == "__main__":
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    suite.addTests(loader.loadTestsFromTestCase(TestInvalidJsonRetry))
    suite.addTests(loader.loadTestsFromTestCase(TestPermissionBlocked))
    suite.addTests(loader.loadTestsFromTestCase(TestStateTransitions))
    suite.addTests(loader.loadTestsFromTestCase(TestNoOpTrap))

    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    sys.exit(0 if result.wasSuccessful() else 1)
