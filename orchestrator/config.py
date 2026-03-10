"""Centralized configuration for orchestrator runtime behavior."""

from __future__ import annotations

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

# ---------------------------------------------------------------------------
# API keys (loaded from .env or environment)
# ---------------------------------------------------------------------------

API_KEYS: dict[str, str] = {
    "qwen": os.getenv("QWEN_API_KEY", "sk-71231aa14faa4a319a61d4c59208f9a4"),
    "deepseek": os.getenv("DEEPSEEK_API_KEY", "sk-2f6d72eb427d44d8b96b96da7c6f9b5c"),
    "anthropic": os.getenv("ANTHROPIC_API_KEY", ""),
}

# ---------------------------------------------------------------------------
# Provider base URLs (OpenAI-compatible endpoints)
# ---------------------------------------------------------------------------

PROVIDER_URLS: dict[str, str] = {
    "qwen": "https://dashscope.aliyuncs.com/compatible-mode/v1",
    "deepseek": "https://api.deepseek.com",
}

# ---------------------------------------------------------------------------
# Per-agent provider + model configuration
# Edit this dict to reassign any agent to any provider/model.
# ---------------------------------------------------------------------------

AGENT_CONFIGS: dict[str, dict] = {
    "orchestrator":  {"provider": "qwen",     "model": "qwen3-max",     "temperature": 0.0   ,  "max_tokens": 32768},
    "planner":       {"provider": "qwen",     "model": "qwen3-max",       "temperature": 0.0,   "max_tokens": 32768},
    "sorry_closer":  {"provider": "deepseek", "model": "deepseek-reasoner", "temperature": 0.0,   "max_tokens": 32768},
    "persister":     {"provider": "qwen",     "model": "qwen3-max",          "temperature": 0.0,   "max_tokens": 32768},
    "diagnostician": {"provider": "qwen",     "model": "qwen3-max",          "temperature": 0.0,   "max_tokens": 16384},
}

# ---------------------------------------------------------------------------
# Centralized runtime controls
# ---------------------------------------------------------------------------

WHITELIST_PATHS = ["Algorithms/", "Lib/", "docs/"]
LEAN_VERIFY_PATHS = ["Algorithms/", "Lib/"]

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

RETRY_LIMITS: dict[str, int] = {
    "MAX_PHASE2_APPROVAL_ROUNDS": 10,
    "MAX_PHASE3_RETRIES": 5,
}

TIMEOUTS: dict[str, int] = {
    "LEAN_BUILD_TIMEOUT": 300,
}

# Backward-compatible aliases (to be removed after full migration).
MAX_APPROVAL_ROUNDS = RETRY_LIMITS["MAX_PHASE2_APPROVAL_ROUNDS"]
MAX_PHASE3_RETRIES = RETRY_LIMITS["MAX_PHASE3_RETRIES"]
MAX_PROVE_RETRIES = MAX_PHASE3_RETRIES
LEAN_BUILD_TIMEOUT = TIMEOUTS["LEAN_BUILD_TIMEOUT"]
LEVERAGE_THRESHOLD = 0.5
MAX_TOKENS = 32768
