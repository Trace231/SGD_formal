"""Shared protocol contracts for Agent8 / Agent9 interactions.

This module centralizes schema-oriented constants and lightweight typing helpers
so routing/planning modules do not duplicate protocol definitions.
"""

from __future__ import annotations

from typing import Literal, TypedDict


# ---------------------------------------------------------------------------
# Shared constants
# ---------------------------------------------------------------------------

AGENT9_REQUIRED_KEYS = frozenset({"theorems", "recommended_order"})
AGENT9_REQUIRED_THEOREM_FIELDS = frozenset(
    {
        "name",
        "proof_strategy",
        "key_lib_lemmas",
        "dependencies",
        "estimated_difficulty",
    }
)
AGENT9_ALLOWED_DIFFICULTIES = frozenset({"low", "medium", "high"})

AGENT8_VALID_ACTIONS = frozenset(
    {
        "agent3_tactical",
        "agent7_signature",
        "agent7_then_agent6",
        "apollo_decompose_repair",
        "agent9_replan",
        "human_missing_assumption",
    }
)
AGENT8_REQUIRED_DECISION_FIELDS = frozenset(
    {
        "action",
        "priority_level",
        "reason",
        "error_signature",
        "hypothesis",
        "evidence",
        "confidence",
        "counterfactual",
    }
)
AGENT8_VALID_ERROR_SUBTYPES = frozenset(
    {
        "declaration_syntax_failure",
        "declaration_api_mismatch",
        "proof_api_mismatch",
        "proof_tactic_failure",
        "strategy_mismatch",
    }
)
AGENT8_VALID_REPAIR_UNITS = frozenset(
    {
        "local_patch",
        "block_restructure",
        "glue",
        "global_replan",
        "statement_gap",
    }
)
AGENT8_VALID_BLOCKER_STATUSES = frozenset(
    {
        "resolved",
        "escalated_subproblem",
        "certified_statement_gap",
        "certified_structural_block",
        "infra_failure",
    }
)


# ---------------------------------------------------------------------------
# TypedDict contracts (static typing only; runtime validation remains in callers)
# ---------------------------------------------------------------------------

DifficultyLevel = Literal["low", "medium", "high"]
Agent8Action = Literal[
    "agent3_tactical",
    "agent7_signature",
    "agent7_then_agent6",
    "apollo_decompose_repair",
    "agent9_replan",
    "human_missing_assumption",
]
Agent8ErrorSubtype = Literal[
    "declaration_syntax_failure",
    "declaration_api_mismatch",
    "proof_api_mismatch",
    "proof_tactic_failure",
    "strategy_mismatch",
]
Agent8RepairUnit = Literal[
    "local_patch",
    "block_restructure",
    "glue",
    "global_replan",
    "statement_gap",
]
Agent8BlockerStatus = Literal[
    "resolved",
    "escalated_subproblem",
    "certified_statement_gap",
    "certified_structural_block",
    "infra_failure",
]


class MissingGlueLemma(TypedDict, total=False):
    name: str
    description: str
    proposed_lean_type: str


class Agent9TheoremPlan(TypedDict, total=False):
    name: str
    lean_statement_line: int
    line_number: int  # legacy compatibility
    dependencies: list[str]
    depends_on: list[str]  # legacy compatibility
    proof_strategy: str
    proof_technique: str
    key_lib_lemmas: list[str]
    missing_glue_lemmas: list[MissingGlueLemma]
    dependency_map: dict[str, str]
    first_action_patch_hint: str
    expected_lean_shape: str
    estimated_difficulty: DifficultyLevel
    difficulty: str  # legacy compatibility


class Agent9Plan(TypedDict, total=False):
    target_algo: str
    theorems: list[Agent9TheoremPlan]
    recommended_order: list[str]


class Agent8Evidence(TypedDict):
    source: str
    snippet: str


class Agent8Decision(TypedDict, total=False):
    action: Agent8Action
    priority_level: str
    reason: str
    targeted_prompt: str
    error_signature: str
    hypothesis: str
    evidence: list[Agent8Evidence]
    confidence: float
    counterfactual: str
    error_subtype: Agent8ErrorSubtype
    target_theorem: str
    allowed_edit_lines: str
    agent7_targeted_prompt: str
    agent6_targeted_prompt: str
    trigger_reason: str
    expected_fallback: str
    investigation_success: bool
    investigation_failures: list[dict]
    route_locked: bool
    candidate_id: str
    allowed_span: str
    repair_unit: Agent8RepairUnit
    target_region: str
    blocker_status: Agent8BlockerStatus
    blocker_report: dict

