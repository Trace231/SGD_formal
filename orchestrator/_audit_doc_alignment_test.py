"""Doc-code alignment audit tests.

Tests:
1. CATALOG conflict detection: fake lemma → doc_code_alignment_missing populated
2. apply_doc_patch anchor uniqueness: multiple matches → ValueError (not silent skip)
3. apply_doc_patch single-match: normal case works

Run with:  python -m orchestrator._audit_doc_alignment_test
"""
from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT))

from orchestrator.metrics import _audit_doc_code_alignment
from orchestrator.tools import apply_doc_patch


# ===========================================================================
# Test 1: CATALOG lemma conflict detection
# ===========================================================================

class TestCatalogAlignment(unittest.TestCase):
    """Verify _audit_doc_code_alignment catches fake lemma entries."""

    def _make_catalog(self, tmp: Path, fake_lemma: str | None = None) -> Path:
        """Write a minimal CATALOG.md, optionally adding a fake lemma heading."""
        docs = tmp / "docs"
        docs.mkdir(parents=True, exist_ok=True)
        catalog = docs / "CATALOG.md"
        content = "# SGD Catalog\n\n"
        if fake_lemma:
            content += f"#### `{fake_lemma}`\n\nSome description.\n"
        catalog.write_text(content, encoding="utf-8")
        return catalog

    def _make_lean_lib(self, tmp: Path, *decl_names: str) -> None:
        """Write a minimal Lean file in Lib/ declaring given names."""
        lib = tmp / "Lib"
        lib.mkdir(parents=True, exist_ok=True)
        content = "\n".join(f"theorem {name} : True := trivial" for name in decl_names)
        (lib / "Defs.lean").write_text(content, encoding="utf-8")

    def test_fake_catalog_entry_shows_in_missing(self):
        """A lemma referenced in CATALOG but absent from Lib/ → alignment_missing."""
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            self._make_catalog(tmp, fake_lemma="nonExistentLemmaXYZ")
            self._make_lean_lib(tmp, "realLemma")

            with patch("orchestrator.metrics.PROJECT_ROOT", tmp):
                ok, missing = _audit_doc_code_alignment()

        self.assertFalse(ok, "Alignment should FAIL when catalog has fake lemma")
        self.assertIn("nonExistentLemmaXYZ", missing,
                      "Missing lemma must appear in alignment_missing list")

    def test_real_catalog_entry_passes(self):
        """A lemma referenced in CATALOG that exists in Lib/ → no missing."""
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            self._make_catalog(tmp, fake_lemma="realLemma")
            self._make_lean_lib(tmp, "realLemma")

            with patch("orchestrator.metrics.PROJECT_ROOT", tmp):
                ok, missing = _audit_doc_code_alignment()

        self.assertTrue(ok, "Alignment should PASS when lemma exists in Lib/")
        self.assertEqual(missing, [], "No missing entries expected")

    def test_empty_catalog_always_passes(self):
        """A CATALOG with no lemma headings → alignment always OK."""
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            self._make_catalog(tmp, fake_lemma=None)  # no lemma entries
            self._make_lean_lib(tmp, "someOtherLemma")

            with patch("orchestrator.metrics.PROJECT_ROOT", tmp):
                ok, missing = _audit_doc_code_alignment()

        self.assertTrue(ok)
        self.assertEqual(missing, [])

    def test_multiple_fake_lemmas_all_in_missing(self):
        """Multiple fake lemmas should all appear in missing list."""
        with tempfile.TemporaryDirectory() as tmpdir:
            tmp = Path(tmpdir)
            docs = tmp / "docs"
            docs.mkdir(parents=True, exist_ok=True)
            (docs / "CATALOG.md").write_text(
                "#### `fakeAlpha`\n#### `fakeBeta`\n#### `realDef`\n",
                encoding="utf-8",
            )
            self._make_lean_lib(tmp, "realDef")

            with patch("orchestrator.metrics.PROJECT_ROOT", tmp):
                ok, missing = _audit_doc_code_alignment()

        self.assertFalse(ok)
        self.assertIn("fakeAlpha", missing)
        self.assertIn("fakeBeta", missing)
        self.assertNotIn("realDef", missing)


# ===========================================================================
# Test 2: apply_doc_patch anchor uniqueness constraint
# ===========================================================================

class TestAnchorUniqueness(unittest.TestCase):
    """Verify that apply_doc_patch raises ValueError on multiple anchor matches."""

    def _make_doc_file(self, content: str) -> tuple[Path, Path]:
        """Create a temp docs directory + file, return (resolved_tmp, doc_file)."""
        # Resolve to canonical path to avoid macOS /var → /private/var symlink issues
        tmp = Path(tempfile.mkdtemp()).resolve()
        docs = tmp / "docs"
        docs.mkdir()
        doc_file = docs / "TESTDOC.md"
        doc_file.write_text(content, encoding="utf-8")
        return tmp, doc_file

    def test_multiple_anchor_matches_raises(self):
        """When anchor matches 2+ locations, apply_doc_patch must raise ValueError."""
        content = (
            "## Section 1\nSome text.\n\n"
            "## Section 1\nDuplicate heading.\n"  # same heading twice
        )
        tmp, doc_file = self._make_doc_file(content)

        # Patch PROJECT_ROOT and allowlist to point at resolved temp dir
        with patch("orchestrator.tools.PROJECT_ROOT", tmp), \
             patch("orchestrator.tools._DOC_ALLOWLIST", ("docs",)):
            with self.assertRaises(ValueError) as ctx:
                apply_doc_patch(
                    path=doc_file,
                    anchor=r"^## Section 1",
                    new_content="New paragraph.",
                )

        msg = str(ctx.exception)
        self.assertIn("matches 2 locations", msg,
                      "Error must state the number of matches found")
        self.assertIn("must be unique", msg,
                      "Error must instruct anchor to be unique")

    def test_single_anchor_match_succeeds(self):
        """When anchor matches exactly once, apply_doc_patch must succeed."""
        content = (
            "## Section A\nSome text.\n\n"
            "## Section B\nDifferent heading.\n"
        )
        tmp, doc_file = self._make_doc_file(content)

        with patch("orchestrator.tools.PROJECT_ROOT", tmp), \
             patch("orchestrator.tools._DOC_ALLOWLIST", ("docs",)):
            result = apply_doc_patch(
                path=doc_file,
                anchor=r"^## Section A",
                new_content="Inserted content.",
            )

        self.assertTrue(result.get("changed"), "Single-match anchor should apply change")

    def test_anchor_not_found_raises(self):
        """When anchor matches zero times, apply_doc_patch must raise ValueError."""
        content = "## Only Section\nSome text.\n"
        tmp, doc_file = self._make_doc_file(content)

        with patch("orchestrator.tools.PROJECT_ROOT", tmp), \
             patch("orchestrator.tools._DOC_ALLOWLIST", ("docs",)):
            with self.assertRaises(ValueError) as ctx:
                apply_doc_patch(
                    path=doc_file,
                    anchor=r"^## Missing Section",
                    new_content="Should not be inserted.",
                )

        self.assertIn("Anchor not found", str(ctx.exception))

    def test_deduplication_skips_existing_content(self):
        """If new_content already exists in the file, apply_doc_patch is a no-op."""
        content = "## Section A\nAlready present content.\n"
        tmp, doc_file = self._make_doc_file(content)

        with patch("orchestrator.tools.PROJECT_ROOT", tmp), \
             patch("orchestrator.tools._DOC_ALLOWLIST", ("docs",)):
            result = apply_doc_patch(
                path=doc_file,
                anchor=r"^## Section A",
                new_content="Already present content.",
            )

        self.assertFalse(result.get("changed"), "Duplicate content must be skipped")
        self.assertEqual(result.get("reason"), "content already present")


# ===========================================================================
# Entry point
# ===========================================================================

if __name__ == "__main__":
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    for tc in (TestCatalogAlignment, TestAnchorUniqueness):
        suite.addTests(loader.loadTestsFromTestCase(tc))

    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    sys.exit(0 if result.wasSuccessful() else 1)
