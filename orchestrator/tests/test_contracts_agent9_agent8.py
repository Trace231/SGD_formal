"""Contract-level compatibility checks for Agent8/Agent9 schemas."""

from orchestrator import contracts
from orchestrator.phase3_agent8 import _build_agent9_theorem_context
from orchestrator.phase3a_agent9 import _validate_agent9_plan


def test_agent9_contract_constants_present():
    assert "theorems" in contracts.AGENT9_REQUIRED_KEYS
    assert "recommended_order" in contracts.AGENT9_REQUIRED_KEYS
    assert "estimated_difficulty" in contracts.AGENT9_REQUIRED_THEOREM_FIELDS
    assert contracts.AGENT9_ALLOWED_DIFFICULTIES == {"low", "medium", "high"}


def test_validate_agent9_plan_accepts_strict_required_fields():
    plan = {
        "target_algo": "Foo",
        "theorems": [
            {
                "name": "thm1",
                "lean_statement_line": 10,
                "dependencies": [],
                "proof_strategy": "intro x; simp",
                "proof_technique": "simp_ring",
                "key_lib_lemmas": ["simp"],
                "missing_glue_lemmas": [],
                "dependency_map": {},
                "first_action_patch_hint": "",
                "expected_lean_shape": "",
                "estimated_difficulty": "low",
            }
        ],
        "recommended_order": ["thm1"],
    }
    ok, msg = _validate_agent9_plan(plan)
    assert ok, msg


def test_validate_agent9_plan_rejects_bad_recommended_order():
    bad = {
        "target_algo": "Foo",
        "theorems": [
            {
                "name": "thm1",
                "lean_statement_line": 10,
                "dependencies": [],
                "proof_strategy": "intro x; simp",
                "proof_technique": "simp_ring",
                "key_lib_lemmas": ["simp"],
                "missing_glue_lemmas": [],
                "dependency_map": {},
                "first_action_patch_hint": "",
                "expected_lean_shape": "",
                "estimated_difficulty": "low",
            }
        ],
        "recommended_order": ["thm1", "thm1"],
    }
    ok, msg = _validate_agent9_plan(bad)
    assert not ok
    assert "duplicate" in msg.lower()


def test_agent8_theorem_context_supports_legacy_fields():
    legacy_plan = {
        "theorems": [
            {
                "name": "process_succ",
                "line_number": 81,
                "depends_on": ["process_zero"],
                "difficulty": "medium",
                "proof_strategy": "rw [process]; simp",
                "proof_technique": "simp_ring",
                "key_lib_lemmas": ["by_cases"],
                "missing_glue_lemmas": [],
                "dependency_map": {},
            }
        ]
    }
    ctx = _build_agent9_theorem_context(legacy_plan, "process_succ")
    assert "lean_statement_line: 81" in ctx
    assert "estimated_difficulty: medium" in ctx
    assert "depends_on: ['process_zero']" in ctx

