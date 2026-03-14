"""Centralized configuration for orchestrator runtime behavior."""

from __future__ import annotations

import json
import os
from pathlib import Path

from dotenv import load_dotenv

load_dotenv()

# ---------------------------------------------------------------------------
# Paths
# ---------------------------------------------------------------------------

PROJECT_ROOT = Path(__file__).resolve().parent.parent
DOCS_DIR = PROJECT_ROOT / "docs"
LIB_DIR = PROJECT_ROOT / "Lib"
ALGORITHMS_DIR = PROJECT_ROOT / "Algorithms"
METRICS_PATH = PROJECT_ROOT / "orchestrator" / "metrics.json"
AUDIT_DIR = PROJECT_ROOT / "orchestrator" / "audits"
AUDIT_ENABLED = os.getenv("ORCHESTRATOR_AUDIT", "1") != "0"

# Full-audit controls (default ON; can be disabled via env for privacy/volume).
AUDIT_FULL_PROMPTS_ENABLED = os.getenv("SGD_AUDIT_FULL_PROMPTS", "1") != "0"
AUDIT_CODE_PATCH_ENABLED = os.getenv("SGD_AUDIT_CODE_PATCH", "1") != "0"
AUDIT_FLUSH_INTERVAL_SECONDS = int(os.getenv("ORCHESTRATOR_AUDIT_FLUSH_INTERVAL", "60"))

# ---------------------------------------------------------------------------
# API keys (loaded from .env or environment)
# ---------------------------------------------------------------------------

API_KEYS: dict[str, str] = {
    "qwen": os.getenv("QWEN_API_KEY", "sk-sp-4626175acf3049baa139a39a53b87105"),
    "deepseek": os.getenv("DEEPSEEK_API_KEY", "sk-2f6d72eb427d44d8b96b96da7c6f9b5c"),
    "anthropic": os.getenv("ANTHROPIC_API_KEY", ""),
}

# ---------------------------------------------------------------------------
# Provider base URLs (OpenAI-compatible endpoints)
# ---------------------------------------------------------------------------

PROVIDER_URLS: dict[str, str] = {
    "qwen": "https://coding.dashscope.aliyuncs.com/v1",
    "deepseek": "https://api.deepseek.com",
}

# ---------------------------------------------------------------------------
# Per-agent provider + model configuration
# Edit this dict to reassign any agent to any provider/model.
# ---------------------------------------------------------------------------

AGENT_CONFIGS: dict[str, dict] = {
    "orchestrator":  {"provider": "qwen",     "model": "qwen3.5-plus"  ,  "max_tokens": 32768},
    "planner":       {"provider": "qwen",     "model": "qwen3.5-plus",  "max_tokens": 32768},
    #"sorry_closer":  {"provider": "deepseek", "model": "deepseek-reasoner", "temperature": 0.0,   "max_tokens": 8192, "use_manifest": True},
    "sorry_closer":  {"provider": "qwen",     "model": "qwen3.5-plus", "max_tokens": 32768, "use_manifest": True},
    "strategy_planner": {"provider": "qwen", "model": "qwen3.5-plus", "max_tokens": 16384},
    "persister":     {"provider": "qwen",     "model": "qwen3.5-plus", "max_tokens": 32768},
    "diagnostician": {"provider": "qwen",     "model": "qwen3.5-plus",  "max_tokens": 16384},
    "glue_filler":   {"provider": "qwen",     "model": "qwen3.5-plus", "max_tokens": 32768, "use_manifest": True},
    "interface_auditor": {"provider": "qwen", "model": "qwen3.5-plus", "max_tokens": 32768},
    "decision_hub":      {"provider": "qwen", "model": "qwen3.5-plus", "max_tokens": 32768},
}

# ---------------------------------------------------------------------------
# Centralized runtime controls
# ---------------------------------------------------------------------------

WHITELIST_PATHS = ["Algorithms/", "Lib/", "docs/"]
LEAN_VERIFY_PATHS = ["Algorithms/", "Lib/"]

# Root-level Lean files that agents may read (but never write) to inspect
# the project import graph and detect circular dependencies before adding imports.
READ_ONLY_PATHS = ["Algorithms/", "Lib/", "docs/", "Main.lean", "lakefile.lean"]

DOC_ANCHORS_BY_FILE: dict[str, list[str]] = {
    "docs/CATALOG.md": ["CATALOG_ALGO_LAYER", "CATALOG_ROADMAP"],
    "docs/GLUE_TRICKS.md": ["GLUE_PATTERNS"],
    "docs/METHODOLOGY.md": ["METHODOLOGY_ROADMAP"],
}

DOC_ANCHORS: dict[str, dict[str, str]] = {
    "CATALOG_ALGO_LAYER": {
        "path": "docs/CATALOG.md",
        "regex": r"^## Algorithm Layer \(Layer 2\)\s+—\s+`Algorithms/SGD\.lean`",
    },
    "CATALOG_ROADMAP": {
        "path": "docs/CATALOG.md",
        "regex": r"^## Roadmap & Dependency Tree",
    },
    "GLUE_PATTERNS": {
        "path": "docs/GLUE_TRICKS.md",
        "regex": r"^## Section 3 — Standard Proof Patterns",
    },
    "METHODOLOGY_ROADMAP": {
        "path": "docs/METHODOLOGY.md",
        "regex": r"^## 2\. Stub-Probe Protocol",
    },
}

# ---------------------------------------------------------------------------
# Lib/Glue anchors for glue lemma insertion (Phase 4 refactoring architect)
# ---------------------------------------------------------------------------

LIB_GLUE_ANCHORS: dict[str, dict[str, dict[str, str]]] = {
    "Lib/Glue/Probability.lean": {
        "BEFORE_LEMMA_2": {
            "regex": r"^-- Lemma 2: Squared norm of stochastic gradient",
            "insert": "before",
        },
        "BEFORE_SVRG": {
            "regex": r"^/-- SVRG variance-reduction inequality",
            "insert": "before",
        },
    },
    "Lib/Glue/Algebra.lean": {
        "BEFORE_INNER_PRODUCT": {
            "regex": r"^-- Inner product and norm helpers for the non-convex step",
            "insert": "before",
        },
        "AFTER_NORM_SQ_SGD": {
            "regex": r"simp \[inner_smul_right, norm_smul, mul_pow, sq_abs\]; ring$",
            "insert": "after",
        },
    },
    "Lib/Glue/Measurable.lean": {
        "BEFORE_SECTION_2": {
            "regex": r"^-- 2\. Integrability of Lipschitz function composed",
            "insert": "before",
        },
    },
    "Lib/Glue/Calculus.lean": {
        "BEFORE_PART_2": {
            "regex": r"^-- Part 2: FTC along a segment",
            "insert": "before",
        },
    },
}

# ---------------------------------------------------------------------------
# Similar-algorithm references for cross-file comparison (Agent2 retry)
# ---------------------------------------------------------------------------

# Mapping: target algorithm stem (Path(target_file).stem) -> list of reference files.
# References are similar algorithms (same archetype or structural relationship).
ALGORITHM_REFERENCES: dict[str, list[str]] = {
    "SVRGOuterLoop": [
        "Algorithms/SGD.lean",
        "Algorithms/SVRG.lean",
        "Algorithms/WeightDecaySGD.lean",
    ],
    "SVRG": ["Algorithms/SGD.lean", "Algorithms/WeightDecaySGD.lean"],
    "SGD": [],
    "WeightDecaySGD": ["Algorithms/SGD.lean"],
    "ProjectedGD": ["Algorithms/SGD.lean", "Algorithms/WeightDecaySGD.lean"],
    "SubgradientMethod": ["Algorithms/SGD.lean"],
    "ClippedSGD": ["Algorithms/SGD.lean"],
}


# Universal references: all algorithms can look these up.
# Format: (path, one-line description). Excludes Lib/Glue/Staging/* (attempt-specific).
REFERENCE_FILES_WITH_DESCRIPTIONS: list[tuple[str, str]] = [
    (
        "Lib/Glue/Probability.lean",
        "概率/积分工具: probReal_univ, integral_const, IsProbabilityMeasure, HasBoundedVariance",
    ),
    (
        "Lib/Glue/Algebra.lean",
        "范数平方展开、梯度步内积代数 (norm_sq_sgd_step, proj_nonexp_sq)",
    ),
    (
        "Lib/Glue/Measurable.lean",
        "可测性与积分复合 (AEStronglyMeasurable, integrable_norm_sq_iterate_comp)",
    ),
    (
        "Lib/Glue/Calculus.lean",
        "Hilbert 空间 FTC、线段微积分 (integral_inner_gradient_segment)",
    ),
    (
        "Lib/Layer0/ConvexFOC.lean",
        "凸/强凸一阶条件 (convex_inner_lower_bound, strong_convex_inner_lower_bound)",
    ),
    (
        "Lib/Layer0/GradientFTC.lean",
        "L-smooth 梯度二次界 (lipschitz_gradient_quadratic_bound)",
    ),
    (
        "Lib/Layer0/IndepExpect.lean",
        "期望/独立性 (expectation_inner_gradL_eq, expectation_norm_sq_gradL_bound)",
    ),
    (
        "Lib/Layer1/StochasticDescent.lean",
        "StochasticDescentHyps 结构与收敛定理",
    ),
    (
        "docs/GLUE_TRICKS.md",
        "通用证明模式 (Pattern A–G, Gap Classification, Mathlib 搜索策略)",
    ),
]


def _get_default_references(target_file: str) -> list[str]:
    """Fallback when target not in ALGORITHM_REFERENCES: use all other Algorithms/*.lean."""
    target_stem = Path(target_file).stem
    algo_dir = PROJECT_ROOT / "Algorithms"
    if not algo_dir.exists():
        return []
    refs: list[str] = []
    for p in sorted(algo_dir.glob("*.lean")):
        stem = p.stem
        if stem != target_stem:
            refs.append(str(p.relative_to(PROJECT_ROOT)))
    return refs


# Agent6 auto-route: when False, system never auto-routes to Agent6 from pattern detection.
# Agent6 is invoked only when Agent7's protocol explicitly indicates a missing glue lemma.
AGENT6_AUTO_ROUTE_ENABLED = False

# If True, after the first 3 attempts without any Agent7 call, system triggers Agent7 and
# Agent6 once before continuing to attempt 4.
FORCE_AGENT7_AGENT6_AFTER_3_ATTEMPTS = os.getenv("ORCHESTRATOR_FORCE_AGENT7_AGENT6_AFTER_3", "1") != "0"

# Known Mathlib name corrections: wrong identifier -> correct replacement.
# Applied before escalation to avoid routing trivial fixes to Agent6/Agent7.
UNKNOWN_IDENTIFIER_RENAME_MAP: dict[str, str] = {
    "pow_le_one": "Left.pow_le_one_of_le",
}

# ---------------------------------------------------------------------------
# Agent3 error patterns and escalation hints (config-driven, no hardcoding)
# Override via ORCHESTRATOR_AGENT_ERROR_PATTERNS / ORCHESTRATOR_AGENT_ESCALATION_HINTS (JSON)
# ---------------------------------------------------------------------------

_AGENT_ERROR_PATTERNS_DEFAULT: dict[str, str] = {
    "invalid_field": r"Invalid field",
    "failed_to_synthesize": r"failed to synthesize instance",
    "application_type_mismatch": r"Application type mismatch",
    "function_expected": r"Function expected",
}

_AGENT_ESCALATION_HINTS_DEFAULT: dict[str, str] = {
    "api_drift": (
        "If local fixes fail repeatedly, consider request_agent7_interface_audit "
        "for API/signature drift."
    ),
    "definition_zone": (
        "Type mismatch occurs in declaration/definition zone (before proof tactics). "
        "This usually means a called function is being applied with the wrong signature. "
        "Read the callee definition first, then patch. "
        "If local fixes fail repeatedly, consider request_agent7_interface_audit."
    ),
    "stale_agent7": (
        "If this persists, consider request_agent7_interface_audit for API/signature drift."
    ),
}


def _load_json_dict(env_key: str, default: dict[str, str]) -> dict[str, str]:
    raw = os.getenv(env_key, "")
    if not raw:
        return default.copy()
    try:
        loaded = json.loads(raw)
        return dict(loaded) if isinstance(loaded, dict) else default.copy()
    except Exception:
        return default.copy()


AGENT_ERROR_PATTERNS: dict[str, str] = _load_json_dict(
    "ORCHESTRATOR_AGENT_ERROR_PATTERNS", _AGENT_ERROR_PATTERNS_DEFAULT
)
AGENT_ESCALATION_HINTS: dict[str, str] = _load_json_dict(
    "ORCHESTRATOR_AGENT_ESCALATION_HINTS", _AGENT_ESCALATION_HINTS_DEFAULT
)

AGENT7_ROUTING_CRITERIA: list[str] = [
    "Invalid field notation (wrong dot/projection on structure)",
    "Application type mismatch / Function expected in declaration/definition zone",
    "failed to synthesize instance in def zone (before proof body)",
    "Same error line repeats with no net sorry decrease",
    "Errors oscillate across a small line set (e.g. 70/74/101/115)",
]

RETRY_LIMITS: dict[str, int] = {
    "MAX_PHASE2_APPROVAL_ROUNDS": 10,
    "MAX_PHASE3_RETRIES": 2,
    "MAX_AGENT6_TOOL_TURNS": 70,
    "MAX_AGENT6_RETRIES": 3,
    # Agent3 autonomy: Agent6 is a first-class tool, allow up to 3 calls per sorry
    "MAX_AGENT6_ESCALATIONS_PER_ATTEMPT": 3,
    "AGENT6_SECOND_ESCALATION_MIN_PROGRESS": 1,
    "AGENT6_SECOND_ESCALATION_REQUIRE_SAME_GOAL": 1,
    "AGENT6_AUTO_ROUTE_REPEAT_THRESHOLD": 2,
    "AGENT6_AUTO_ROUTE_MIN_TURN": 3,
    # Agent3 autonomy: Agent7 can be called up to 4 times per sorry
    "MAX_AGENT7_INVOCATIONS_PER_ATTEMPT": 4,
    "AGENT7_STEP_NO_PROGRESS_THRESHOLD": 2,
    # Trigger stale-error gate sooner
    "AGENT7_FORCE_STALE_LINE_THRESHOLD": 3,
    "AGENT7_FORCE_NO_PROGRESS_TURNS": 3,
    "AGENT7_FORCE_AFTER_SOFT_WARN": 1,
    "DEFINITION_ZONE_FORCE_AGENT7_AFTER_N": 2,
    # Per-sorry turn budget (used by per-sorry loop)
    "PER_SORRY_TURNS": 20,
    # Context eviction: clear Agent3 conversation history every N attempts to prevent
    # context pollution from accumulated failed attempts.
    "AGENT3_CONTEXT_EVICT_EVERY_N": 3,
    # Context eviction: clear Agent2 conversation history every N attempts and reinject
    # a distilled plan summary (math plan + best checkpoint + failed approaches blacklist).
    "AGENT2_CONTEXT_EVICT_EVERY_N": 4,
    # Agent8 Decision Hub: maximum decision ticks before escalating to Agent5.
    "AGENT8_MAX_STEPS": 8,
    # Agent8: maximum Agent3 tool turns per dispatch (simplified loop).
    "AGENT8_AGENT3_MAX_TURNS": 15,
    # Agent8 investigation phase: max read-only lookup rounds before final decision.
    "AGENT8_INVESTIGATION_TURNS": 3,
    # Agent8 context truncation constants (characters).
    "AGENT8_ERROR_CHARS": 3000,
    "AGENT8_PLAN_CHARS": 3000,
    "AGENT8_STAGING_CHARS": 2000,
    "AGENT8_HISTORY_WINDOW": 8,
    "AGENT8_A7_PROMPT_CHARS": 1500,
    "AGENT8_A2_PLAN_CHARS": 4000,
    "AGENT8_A2_ERROR_CHARS": 2000,
    "AGENT8_A2_FILE_CHARS": 6000,
    # Agent5 (diagnostician) context limits.
    "AGENT5_ERRORS_CHARS": 3000,
    "AGENT5_PLAN_CHARS": 2000,
    # Agent2 distilled summary max chars.
    "AGENT2_DISTILLED_GUIDANCE_CHARS": 5000,
    # Conservative routing: how many consecutive turns the same interface-like error
    # signature (file:line:msg-prefix) may repeat inside LOCAL_PROOF_ERROR handling
    # before the system forces escalation to DEFINITION_ZONE_ERROR / Agent7.
    # Set to 2 so Agent3 gets one genuine self-fix attempt, then we escalate.
    "CONSERVATIVE_INTERFACE_ERROR_REPEAT_THRESHOLD": 2,
    # Conservative routing: when blocked_sorry_count > 0 AND the primary error
    # belongs to the interface-like family, immediately treat as DEFINITION_ZONE_ERROR
    # instead of letting Agent3 try to patch locally.  1 = enabled, 0 = disabled.
    "CONSERVATIVE_BLOCKED_SORRY_INTERFACE_ESCALATE": 1,
    # Agent9 (strategy_planner): max LLM retries on JSON parse failure.
    "AGENT9_MAX_ROUNDS": 3,
    # Agent9: truncation limit (chars) when injecting structured plan into Agent8 context.
    "AGENT9_PLAN_CHARS": 3000,
    # Agent9: how many chars of Agent2's guidance to feed into Agent9's prompt.
    "AGENT9_GUIDANCE_CHARS": 4000,
    # Agent8 anti-loop: consecutive zero-delta ticks with same action before escalating.
    "AGENT8_NO_PROGRESS_ESCALATE_AFTER": 2,
    # Agent8 anti-loop: length of error-signature string used for loop detection.
    # Replaces the previous 40-char truncation that caused false collisions.
    "AGENT8_ERROR_SIG_FULL_LEN": 120,
}

TIMEOUTS: dict[str, int] = {
    "LEAN_BUILD_TIMEOUT": 300,
}

# ---------------------------------------------------------------------------
# Agent2 routing parameters
# ---------------------------------------------------------------------------

ROUTING_PARAMS: dict[str, int | float] = {
    # Minimum confidence Agent2 must report to allow cross-agent routing (agent7/agent6).
    # Below this threshold, orchestrator forces route_to="agent3".
    "MIN_CONFIDENCE_FOR_CROSS_AGENT_ROUTE": 0.6,
    # Maximum number of "self" (Agent2 self-revision) routes per attempt.
    "MAX_SELF_REVISIONS_PER_ATTEMPT": 1,
    # Maximum times the same (error_signature, route_to) pair may repeat before
    # the orchestrator escalates to the next level (anti-oscillation guard).
    "MAX_SAME_ROUTE_REPEAT": 2,
    # Maximum number of preemptive (orchestrator-driven, not Agent3-requested)
    # Agent7 invocations per attempt.
    "AGENT7_PREEMPTIVE_MAX_PER_ATTEMPT": 1,
}

# ---------------------------------------------------------------------------
# Agent8 Decision Hub parameters
# ---------------------------------------------------------------------------

# Number of lines above/below each error line to include in the truncated
# file context sent to Agent8.  Agent8 can request more via read-only tools.
AGENT8_FILE_WINDOW_RADIUS: int = int(os.getenv("AGENT8_FILE_WINDOW_RADIUS", "60"))

# When True, Agent8 writes detailed per-tick debug logs to the audit directory.
AGENT8_DEBUG: bool = os.getenv("AGENT8_DEBUG", "0") != "0"

# Verbosity level for Agent8 debug logs.
# 1 = decision + outcome only, 2 = +ctx summary (first 500 chars), 3 = +raw_reply truncated.
AGENT8_DEBUG_LEVEL: int = int(os.getenv("AGENT8_DEBUG_LEVEL", "1"))

# Hard trigger: if the same error_signature appears >= this many consecutive
# ticks with different actions, force human_missing_assumption.
AGENT8_HUMAN_GATE_CONSECUTIVE_THRESHOLD: int = 3

# Backward-compatible aliases (to be removed after full migration).
MAX_APPROVAL_ROUNDS = RETRY_LIMITS["MAX_PHASE2_APPROVAL_ROUNDS"]
MAX_PHASE3_RETRIES = RETRY_LIMITS["MAX_PHASE3_RETRIES"]
MAX_PROVE_RETRIES = MAX_PHASE3_RETRIES
LEAN_BUILD_TIMEOUT = TIMEOUTS["LEAN_BUILD_TIMEOUT"]
LEVERAGE_THRESHOLD = 0.5
MAX_TOKENS = 32768
