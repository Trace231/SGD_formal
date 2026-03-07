"""Configuration: project paths, per-agent provider/model mapping, retry limits."""

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

# ---------------------------------------------------------------------------
# API keys (loaded from .env or environment)
# ---------------------------------------------------------------------------

API_KEYS: dict[str, str] = {
    "qwen": os.getenv("QWEN_API_KEY", ""),
    "deepseek": os.getenv("DEEPSEEK_API_KEY", ""),
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
    "orchestrator":  {"provider": "qwen",     "model": "qwen3-max",          "max_tokens": 32768},
    "planner":       {"provider": "qwen",     "model": "qwen3-max",          "max_tokens": 32768},
    "sorry_closer":  {"provider": "deepseek", "model": "deepseek-reasoner",  "max_tokens": 32768},
    "persister":     {"provider": "qwen",     "model": "qwen3-max",          "max_tokens": 32768},
    "diagnostician": {"provider": "qwen",     "model": "qwen3-max",          "max_tokens": 16384},
}

# ---------------------------------------------------------------------------
# Orchestration parameters
# ---------------------------------------------------------------------------

MAX_APPROVAL_ROUNDS = 10
MAX_PROVE_RETRIES = 10
LEVERAGE_THRESHOLD = 0.5
MAX_TOKENS = 32768
