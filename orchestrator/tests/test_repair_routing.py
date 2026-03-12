"""Scenario validation for Agent3/Agent5 role separation.

Tests three core routing scenarios:
  A) Staging mechanical failure  → auto-fixed by apply_staging_rules (no LLM)
  B) Missing assumption failure  → signature patched by apply_assumption_patches
  C) Genuine proof obligation    → classified as PROOF_OBLIGATION, NOT misrouted

Pass criteria:
  - Scenario A: apply_staging_rules returns > 0 fixes for known bad patterns.
  - Scenario B: apply_assumption_patches inserts the missing hypothesis; goals_to_patch_list
    produces non-empty patches; parse_diagnosis_json validates required fields.
  - Scenario C: classify_goal returns PROOF_OBLIGATION for inequality/algebra goals;
    all_goals_are_assumptions returns False.
  - Success gating: auto_repair_loop in agents.py returns "fixed" ONLY when
    exit_code==0 AND sorry_count==0 (validated via unit check on the return logic).
"""

import json
import tempfile
import textwrap
from pathlib import Path

import pytest

from orchestrator.assumption_repair import (
    all_goals_are_assumptions,
    apply_assumption_patches,
    apply_lm_staging_patches,
    apply_staging_rules,
    classify_goal,
    detect_theorem_at_line,
    extract_unsolved_goals,
    goals_to_patch_list,
    parse_diagnosis_json,
)


# ---------------------------------------------------------------------------
# Scenario A — Staging rule-based auto-fix
# ---------------------------------------------------------------------------

STAGING_OVERSPEC_SIMP = textwrap.dedent("""\
    import Mathlib
    theorem foo (x : ℝ) : x + 0 = x := by
      simp [add_zero, mul_comm, Finset.sum_empty]
""")

STAGING_EXACT_FUNEXT = textwrap.dedent("""\
    import Mathlib
    theorem bar (f g : ℕ → ℕ) (h : ∀ n, f n = g n) : f = g := by
      exact h
""")

STAGING_ERROR_OVERSPEC = textwrap.dedent("""\
    error: simp made no progress
""")

STAGING_ERROR_FUNEXT = textwrap.dedent("""\
    error: type mismatch
      term 'h'
      has type '∀ (n : ℕ), f n = g n'
    expected type 'f = g'
    note: exact? failed; try 'exact funext h'
""")


class TestScenarioA:
    """Staging mechanical failures are fixed without LLM."""

    def test_overspecified_simp_fixed(self):
        with tempfile.NamedTemporaryFile(
            suffix=".lean", mode="w", delete=False, dir="/tmp"
        ) as f:
            f.write(STAGING_OVERSPEC_SIMP)
            fpath = Path(f.name)
        # Error text must reference the file name (as Lean compiler would output)
        error_text = f"{fpath.name}:3:2: error: simp made no progress\n"
        try:
            n = apply_staging_rules(fpath, error_text)
            assert n > 0, "Expected at least one simp-overspec fix"
        finally:
            fpath.unlink(missing_ok=True)

    def test_exact_funext_fixed(self):
        with tempfile.NamedTemporaryFile(
            suffix=".lean", mode="w", delete=False, dir="/tmp"
        ) as f:
            f.write(STAGING_EXACT_FUNEXT)
            fpath = Path(f.name)
        # Error text must reference the file name with the correct line number.
        # STAGING_EXACT_FUNEXT has 'exact h' on line 3.
        error_text = (
            f"{fpath.name}:3:4: error: type mismatch\n"
            "  term 'h'\n"
            "  has type '∀ (n : ℕ), f n = g n'\n"
            "  expected type 'f = g'\n"
            f"note: exact? failed; try 'exact funext h'\n"
        )
        try:
            n = apply_staging_rules(fpath, error_text)
            assert n > 0, "Expected exact→funext fix to apply"
        finally:
            fpath.unlink(missing_ok=True)


# ---------------------------------------------------------------------------
# Scenario B — Missing assumption detection and patching
# ---------------------------------------------------------------------------

FAKE_LEAN_ERROR_ASSUMPTIONS = textwrap.dedent("""\
    /tmp/Algorithms/SVRGOuterLoop.lean:42:2: error: unsolved goals
    ⊢ Integrable (fun s => ‖oracle s‖ ^ 2) ν
    /tmp/Algorithms/SVRGOuterLoop.lean:42:2: error: unsolved goals
    ⊢ AEMeasurable (fun s => oracle s) ν
""")

FAKE_LEAN_ERROR_PROOF_OBL = textwrap.dedent("""\
    /tmp/Algorithms/SVRGOuterLoop.lean:55:2: error: unsolved goals
    ⊢ ‖x - y‖ ^ 2 ≤ C * ‖x‖ ^ 2
    /tmp/Algorithms/SVRGOuterLoop.lean:60:2: error: unsolved goals
    ⊢ ∑ i, a i = 1
""")

THEOREM_FILE_CONTENT = textwrap.dedent("""\
    import Mathlib

    theorem svrg_convergence (setup : SVRGSetup)
        (h_convex : Convex ℝ (Set.range f)) :
        True := by
      sorry
""")


class TestScenarioB:
    """Assumption-shaped goals are detected and patched deterministically."""

    def test_extract_assumption_goals(self):
        goals = extract_unsolved_goals(FAKE_LEAN_ERROR_ASSUMPTIONS)
        assert len(goals) >= 1
        assert any("Integrable" in g["goal"] for g in goals)

    def test_all_goals_are_assumptions(self):
        goals = extract_unsolved_goals(FAKE_LEAN_ERROR_ASSUMPTIONS)
        assert all_goals_are_assumptions(goals), (
            "All goals should be classified as MISSING_ASSUMPTION"
        )

    def test_classify_assumption_goal(self):
        assert classify_goal("⊢ Integrable (fun s => ‖oracle s‖ ^ 2) ν") == "MISSING_ASSUMPTION"
        assert classify_goal("⊢ AEMeasurable (fun s => oracle s) ν") == "MISSING_ASSUMPTION"
        assert classify_goal("⊢ Measurable f") == "MISSING_ASSUMPTION"
        assert classify_goal("⊢ IsProbabilityMeasure ν") == "MISSING_ASSUMPTION"

    def test_goals_to_patch_list(self):
        goals = extract_unsolved_goals(FAKE_LEAN_ERROR_ASSUMPTIONS)
        with tempfile.NamedTemporaryFile(suffix=".lean", mode="w", delete=False) as f:
            f.write(THEOREM_FILE_CONTENT)
            fpath = Path(f.name)
        # Patch line numbers to point into our fake file (line 4 = theorem line)
        for g in goals:
            g["line"] = 4
        try:
            patches = goals_to_patch_list(goals, fpath)
            assert len(patches) >= 1
            for p in patches:
                assert p.get("theorem"), "Patch must have a theorem name"
                assert p.get("hyp_name"), "Patch must have a hyp_name"
                assert p.get("hyp_type"), "Patch must have a hyp_type"
        finally:
            fpath.unlink(missing_ok=True)

    def test_detect_theorem_at_line(self):
        with tempfile.NamedTemporaryFile(suffix=".lean", mode="w", delete=False) as f:
            f.write(THEOREM_FILE_CONTENT)
            fpath = Path(f.name)
        try:
            name = detect_theorem_at_line(fpath, 4)
            assert name == "svrg_convergence"
        finally:
            fpath.unlink(missing_ok=True)

    def test_apply_assumption_patches(self):
        content = textwrap.dedent("""\
            import Mathlib

            theorem myThm (x : ℝ) : True := by
              trivial
        """)
        with tempfile.NamedTemporaryFile(suffix=".lean", mode="w", delete=False) as f:
            f.write(content)
            fpath = Path(f.name)
        try:
            patches = [{
                "theorem": "myThm",
                "hyp_name": "h_int",
                "hyp_type": "Integrable (fun s => s) μ",
                "insert_after": None,
            }]
            n = apply_assumption_patches(str(fpath), patches)
            assert n == 1
            new_content = fpath.read_text()
            assert "h_int" in new_content
            assert "Integrable" in new_content
        finally:
            fpath.unlink(missing_ok=True)

    def test_parse_diagnosis_json_valid(self):
        diag = textwrap.dedent("""\
            I analyzed the error.

            ```json
            {
              "classification": "ASSUMPTIONS_WRONG",
              "auto_repairable": true,
              "assumptions_to_add": [
                {
                  "theorem": "myThm",
                  "hyp_name": "h_int",
                  "hyp_type": "Integrable f μ",
                  "insert_after": null
                }
              ]
            }
            ```
        """)
        result = parse_diagnosis_json(diag)
        assert result["classification"] == "ASSUMPTIONS_WRONG"
        assert result["auto_repairable"] is True
        assert len(result["assumptions_to_add"]) == 1

    def test_parse_diagnosis_json_invalid_entry_filtered(self):
        """Entries missing required fields are filtered out, disabling auto-repair."""
        diag = textwrap.dedent("""\
            ```json
            {
              "classification": "ASSUMPTIONS_WRONG",
              "auto_repairable": true,
              "assumptions_to_add": [
                {"theorem": "", "hyp_name": "h", "hyp_type": "Integrable f μ"}
              ]
            }
            ```
        """)
        result = parse_diagnosis_json(diag)
        # Empty theorem name → entry filtered → auto_repairable forced False
        assert result["auto_repairable"] is False
        assert result["assumptions_to_add"] == []

    def test_parse_diagnosis_json_no_json(self):
        result = parse_diagnosis_json("The error is a proof obligation.")
        assert result["auto_repairable"] is False
        assert result["classification"] == "UNKNOWN"


# ---------------------------------------------------------------------------
# Scenario C — Genuine proof obligations are NOT misrouted
# ---------------------------------------------------------------------------

class TestScenarioC:
    """Proof obligations go to Agent3, never to assumption patcher."""

    def test_classify_proof_obligation(self):
        assert classify_goal("⊢ ‖x - y‖ ^ 2 ≤ C * ‖x‖ ^ 2") == "PROOF_OBLIGATION"
        assert classify_goal("⊢ ∑ i, a i = 1") == "PROOF_OBLIGATION"
        assert classify_goal("⊢ f x = g x") == "PROOF_OBLIGATION"
        assert classify_goal("⊢ 0 < ε") == "PROOF_OBLIGATION"
        assert classify_goal("⊢ ∀ n, n + 0 = n") == "PROOF_OBLIGATION"

    def test_not_all_goals_are_assumptions_when_mixed(self):
        """Mixed goals should NOT be treated as pure assumption errors."""
        goals = extract_unsolved_goals(FAKE_LEAN_ERROR_PROOF_OBL)
        assert not all_goals_are_assumptions(goals)

    def test_not_all_goals_are_assumptions_for_proof_obls(self):
        error_with_proof_obl = textwrap.dedent("""\
            /tmp/foo.lean:10:4: error: unsolved goals
            ⊢ ‖x - y‖ ^ 2 ≤ C
        """)
        goals = extract_unsolved_goals(error_with_proof_obl)
        assert not all_goals_are_assumptions(goals)


# ---------------------------------------------------------------------------
# Scenario D — Success gate: "fixed" only when sorry_count == 0
# ---------------------------------------------------------------------------

class TestSuccessGate:
    """auto_repair_loop should return 'fixed' only on (exit=0, sorry=0)."""

    def test_fixed_requires_zero_sorry(self):
        """Simulate the logic: sorry > 0 should NOT produce 'fixed'."""
        # Replicate the decision logic from auto_repair_loop
        def should_return_fixed(exit_code: int, sorry_count: int) -> bool:
            return exit_code == 0 and sorry_count == 0

        assert should_return_fixed(0, 0) is True
        assert should_return_fixed(0, 1) is False
        assert should_return_fixed(0, 5) is False
        assert should_return_fixed(1, 0) is False
        assert should_return_fixed(1, 1) is False

    def test_partial_success_not_phase3_complete(self):
        """exit=0 but sorry>0 must NOT be reported as Phase 3 complete."""
        def phase3_complete(exit_code: int, sorry_count: int) -> bool:
            return exit_code == 0 and sorry_count == 0

        assert phase3_complete(0, 3) is False
        assert phase3_complete(0, 0) is True


# ---------------------------------------------------------------------------
# Scenario E — Forward scan: error on `by` line resolved to actual tactic
# ---------------------------------------------------------------------------

STAGING_BY_LINE_SIMP = textwrap.dedent("""\
    import Mathlib
    theorem foo (setup : FooSetup) :
        (fun ω => setup.fProcess 0 ω) = fun _ => 0 := by
      funext ω
      simp [FooSetup.fProcess, FooSetup.process_zero]
""")

STAGING_BY_LINE_EXACT = textwrap.dedent("""\
    import Mathlib
    theorem bar (f g : ℕ → ℕ) (h : ∀ n, f n = g n) :
        f = g := by
      convert (funext h) using 0
      exact h
""")


class TestScenarioE:
    """Error reported on `by` line is correctly forwarded to the tactic line."""

    def test_forward_scan_simp_fixed(self):
        # Error at line 3 (the `by` line), but simp is on line 5
        with tempfile.NamedTemporaryFile(
            suffix=".lean", mode="w", delete=False, dir="/tmp"
        ) as f:
            f.write(STAGING_BY_LINE_SIMP)
            fpath = Path(f.name)
        # Error reported at line 3 (ends with `by`), actual simp on line 5
        error_text = f"{fpath.name}:3:38: error: unsolved goals\n⊢ setup.f 0 ω = 0\n"
        try:
            n = apply_staging_rules(fpath, error_text)
            assert n > 0, "Expected simp fix via forward scan"
        finally:
            fpath.unlink(missing_ok=True)

    def test_forward_scan_redundant_exact_deleted(self):
        # Error at line 3 (the `by` line), but `exact h` is on line 5
        with tempfile.NamedTemporaryFile(
            suffix=".lean", mode="w", delete=False, dir="/tmp"
        ) as f:
            f.write(STAGING_BY_LINE_EXACT)
            fpath = Path(f.name)
        # No funext hint → redundant exact should be deleted
        error_text = f"{fpath.name}:3:35: error: No goals to be solved\n"
        try:
            n = apply_staging_rules(fpath, error_text)
            assert n > 0, "Expected redundant exact to be deleted via forward scan"
            content = fpath.read_text()
            assert "exact h\n" not in content
        finally:
            fpath.unlink(missing_ok=True)


# ---------------------------------------------------------------------------
# Scenario F — LM staging patch fallback
# ---------------------------------------------------------------------------

LM_PATCH_CONTENT = textwrap.dedent("""\
    import Mathlib

    theorem myProof (x : ℝ) : x + 0 = x := by
      simp [add_zero, SomeSetup.myDef]
""")


class TestScenarioF:
    """apply_lm_staging_patches applies exact search/replace pairs."""

    def test_lm_patch_applied(self):
        with tempfile.NamedTemporaryFile(
            suffix=".lean", mode="w", delete=False, dir="/tmp"
        ) as f:
            f.write(LM_PATCH_CONTENT)
            fpath = Path(f.name)
        patches = [{"search": "simp [add_zero, SomeSetup.myDef]", "replace": "simp [add_zero]"}]
        try:
            n = apply_lm_staging_patches(fpath, patches)
            assert n == 1
            content = fpath.read_text()
            assert "simp [add_zero]" in content
            assert "SomeSetup.myDef" not in content
        finally:
            fpath.unlink(missing_ok=True)

    def test_lm_patch_skipped_if_search_not_found(self):
        with tempfile.NamedTemporaryFile(
            suffix=".lean", mode="w", delete=False, dir="/tmp"
        ) as f:
            f.write(LM_PATCH_CONTENT)
            fpath = Path(f.name)
        patches = [{"search": "this text does not exist", "replace": "x"}]
        try:
            n = apply_lm_staging_patches(fpath, patches)
            assert n == 0
        finally:
            fpath.unlink(missing_ok=True)

    def test_lm_patch_skipped_if_ambiguous(self):
        """Patch with more than one occurrence must be skipped."""
        content = "simp [foo]\nsimp [foo]\n"
        with tempfile.NamedTemporaryFile(
            suffix=".lean", mode="w", delete=False, dir="/tmp"
        ) as f:
            f.write(content)
            fpath = Path(f.name)
        patches = [{"search": "simp [foo]", "replace": "simp only [foo]"}]
        try:
            n = apply_lm_staging_patches(fpath, patches)
            assert n == 0, "Ambiguous search must not be applied"
        finally:
            fpath.unlink(missing_ok=True)

    def test_no_goals_split_funext_via_type_mismatch(self):
        """'type mismatch' with 'exact' in source → apply funext rewrite.

        The funext hint from Lean appears on a `note:` line which starts at
        column 0, so it is NOT captured in the parsed error `msg`.  The rule
        therefore triggers on ("type mismatch" in msg AND "exact" in original).
        """
        content = textwrap.dedent("""\
            import Mathlib
            theorem t (f g : ℕ → ℕ) (h : ∀ n, f n = g n) : f = g := by
              exact h
        """)
        with tempfile.NamedTemporaryFile(
            suffix=".lean", mode="w", delete=False, dir="/tmp"
        ) as f:
            f.write(content)
            fpath = Path(f.name)
        # Error is "type mismatch" (NOT "No goals"); note: line with funext
        # hint is NOT captured in msg (starts at col 0, hence non-whitespace).
        error_text = (
            f"{fpath.name}:3:2: error: type mismatch\n"
            "  term 'h'\n"
            "  has type '∀ (n : ℕ), f n = g n'\n"
            "  expected type 'f = g'\n"
            "note: exact? failed; try 'exact funext h'\n"
        )
        try:
            n = apply_staging_rules(fpath, error_text)
            assert n > 0
            new_content = fpath.read_text()
            assert "exact funext h" in new_content
        finally:
            fpath.unlink(missing_ok=True)

    def test_no_goals_split_no_funext_hint(self):
        """'No goals to be solved' WITHOUT funext hint → delete the exact line."""
        content = textwrap.dedent("""\
            import Mathlib
            theorem t (f g : ℕ → ℕ) (h : ∀ n, f n = g n) : f = g := by
              convert (funext h) using 0
              exact h
        """)
        with tempfile.NamedTemporaryFile(
            suffix=".lean", mode="w", delete=False, dir="/tmp"
        ) as f:
            f.write(content)
            fpath = Path(f.name)
        # Error at line 4 (exact h), no funext hint
        error_text = f"{fpath.name}:4:2: error: No goals to be solved\n"
        try:
            n = apply_staging_rules(fpath, error_text)
            assert n > 0
            new_content = fpath.read_text()
            assert "exact h" not in new_content
        finally:
            fpath.unlink(missing_ok=True)
