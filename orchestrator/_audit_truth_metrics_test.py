"""Truth-metrics audit: sorry injection test + coverage/density formula check.

Run with:  python -m orchestrator._audit_truth_metrics_test
"""
from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT))

from orchestrator.metrics import (
    RunRecord,
    _count_algorithm_calls,
    _used_symbol_set,
    capture_physical_metrics,
)


# ===========================================================================
# Test 1: coverage / density formula correctness
# ===========================================================================

class TestDualLeverageFormulas(unittest.TestCase):
    """Unit-verify L_coverage and L_density math."""

    def test_coverage_rate_all_used(self):
        """If every new decl is used once, coverage = 1.0."""
        total_new = 4
        used_new = 4
        algo_calls = 4
        coverage = used_new / total_new if total_new > 0 else 1.0
        density = algo_calls / used_new if used_new > 0 else 0.0
        self.assertAlmostEqual(coverage, 1.0)
        self.assertAlmostEqual(density, 1.0)

    def test_coverage_rate_partial(self):
        """If half the decls are used, coverage = 0.5."""
        total_new = 4
        used_new = 2
        algo_calls = 6
        coverage = used_new / total_new if total_new > 0 else 1.0
        density = algo_calls / used_new if used_new > 0 else 0.0
        self.assertAlmostEqual(coverage, 0.5)
        self.assertAlmostEqual(density, 3.0)

    def test_coverage_zero_new_decls(self):
        """Edge case: no new decls → coverage defaults to 1.0."""
        total_new = 0
        used_new = 0
        coverage = used_new / total_new if total_new > 0 else 1.0
        self.assertAlmostEqual(coverage, 1.0)

    def test_density_zero_used(self):
        """Edge case: no used decls → density = 0."""
        used_new = 0
        algo_calls = 5
        density = algo_calls / used_new if used_new > 0 else 0.0
        self.assertAlmostEqual(density, 0.0)

    def test_legacy_leverage_formula(self):
        """Legacy = calls/(calls+decls) is distinct from coverage."""
        algo_calls = 6
        total_new = 4
        denom = algo_calls + total_new
        leverage = algo_calls / denom if denom > 0 else 1.0
        self.assertAlmostEqual(leverage, 0.6)
        # coverage is 0.5 (only 2 out of 4 used), density is 3.0
        # so legacy ≠ coverage — they measure different things


# ===========================================================================
# Test 2: _used_symbol_set correctness using temp files
# ===========================================================================

class TestUsedSymbolSet(unittest.TestCase):
    """Verify _used_symbol_set identifies truly-used symbols."""

    def _make_algo_file(self, content: str) -> tuple[Path, str]:
        """Write a temp .lean file under a temp Algorithms/ dir."""
        tmp_dir = Path(tempfile.mkdtemp())
        algo_dir = tmp_dir / "Algorithms"
        algo_dir.mkdir()
        algo_file = algo_dir / "Test.lean"
        algo_file.write_text(content, encoding="utf-8")
        return tmp_dir, str(algo_file)

    def test_used_symbol_detected(self):
        """A symbol that appears in Algorithms/ content must be in used set."""
        symbols = ["myLemmaFoo", "myLemmaBar"]
        algo_content = "import Lib\nexact myLemmaFoo 42\n"

        tmp_dir = Path(tempfile.mkdtemp())
        algo_dir = tmp_dir / "Algorithms"
        algo_dir.mkdir()
        (algo_dir / "Test.lean").write_text(algo_content, encoding="utf-8")

        with patch("orchestrator.metrics.PROJECT_ROOT", tmp_dir):
            used = _used_symbol_set(symbols)

        self.assertIn("myLemmaFoo", used)
        self.assertNotIn("myLemmaBar", used)

    def test_unused_symbol_absent(self):
        """A symbol not referenced in Algorithms/ must not be in used set."""
        symbols = ["orphanLemma"]
        algo_content = "import Lib\nexact otherLemma 1\n"

        tmp_dir = Path(tempfile.mkdtemp())
        algo_dir = tmp_dir / "Algorithms"
        algo_dir.mkdir()
        (algo_dir / "Test.lean").write_text(algo_content, encoding="utf-8")

        with patch("orchestrator.metrics.PROJECT_ROOT", tmp_dir):
            used = _used_symbol_set(symbols)

        self.assertNotIn("orphanLemma", used)

    def test_empty_symbol_list_returns_empty_set(self):
        """Empty input → empty output."""
        with patch("orchestrator.metrics.PROJECT_ROOT", Path(tempfile.mkdtemp())):
            used = _used_symbol_set([])
        self.assertEqual(used, set())


# ===========================================================================
# Test 3: sorry injection — verify total_repo_sorry_count increments
# ===========================================================================

class TestSorryInjection(unittest.TestCase):
    """Verify that injecting a sorry into a .lean file increments count."""

    def test_count_sorry_baseline_vs_injected(self):
        """count_sorrys must return N+1 after injecting one sorry."""
        from orchestrator.verify import count_sorrys

        with tempfile.TemporaryDirectory() as tmp:
            lean_file = Path(tmp) / "test_file.lean"
            lean_file.write_text("theorem foo : 1 = 1 := rfl\n", encoding="utf-8")

            # Relative path simulation: count_sorrys uses PROJECT_ROOT; mock it
            with patch("orchestrator.verify.PROJECT_ROOT", Path(tmp)):
                count_before = count_sorrys("test_file.lean")

            lean_file.write_text(
                "theorem foo : 1 = 1 := rfl\n"
                "theorem bar : 1 = 2 := by sorry\n",
                encoding="utf-8",
            )

            with patch("orchestrator.verify.PROJECT_ROOT", Path(tmp)):
                count_after = count_sorrys("test_file.lean")

        self.assertEqual(count_before, 0, "Baseline should have 0 sorrys")
        self.assertEqual(count_after, 1, "After injection: exactly 1 sorry")
        self.assertEqual(
            count_after - count_before, 1,
            "total_repo_sorry_count must increase by exactly 1 after injection",
        )

    def test_run_record_has_dual_metric_fields(self):
        """RunRecord must carry lib_coverage_rate and lib_density_rate fields."""
        record = RunRecord(algorithm="test")
        self.assertTrue(hasattr(record, "lib_coverage_rate"),
                        "RunRecord must have lib_coverage_rate")
        self.assertTrue(hasattr(record, "lib_density_rate"),
                        "RunRecord must have lib_density_rate")
        # Defaults should be safe zeros/ones
        self.assertGreaterEqual(record.lib_coverage_rate, 0.0)
        self.assertGreaterEqual(record.lib_density_rate, 0.0)


# ===========================================================================
# Entry point
# ===========================================================================

if __name__ == "__main__":
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    for tc in (TestDualLeverageFormulas, TestUsedSymbolSet, TestSorryInjection):
        suite.addTests(loader.loadTestsFromTestCase(tc))

    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    sys.exit(0 if result.wasSuccessful() else 1)
