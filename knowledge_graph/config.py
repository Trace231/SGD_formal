"""Path constants and weights loading for the knowledge graph module.

Isolation rule: does NOT import orchestrator. All paths are relative to SGD_ROOT.
"""

from __future__ import annotations

import json
from pathlib import Path

_THIS_DIR = Path(__file__).resolve().parent
SGD_ROOT = _THIS_DIR.parent

AUDITS_DIR = SGD_ROOT / "orchestrator" / "audits"
DOCS_DIR = SGD_ROOT / "docs"
ALGORITHMS_DIR = SGD_ROOT / "Algorithms"
LIB_DIR = SGD_ROOT / "Lib"
OUTPUT_DIR = _THIS_DIR / "output"
METRICS_PATH = SGD_ROOT / "orchestrator" / "metrics.json"
WEIGHTS_PATH = _THIS_DIR / "weights.json"
SEEDS_PATH = _THIS_DIR / "seeds" / "planned.json"

# Default difficulty formula weights
DEFAULT_ALPHA = 0.4
DEFAULT_BETA = 0.4
DEFAULT_GAMMA = 0.2


def load_weights() -> tuple[float, float, float]:
    """Load (alpha, beta, gamma) from weights.json if present; else use defaults."""
    if WEIGHTS_PATH.exists():
        try:
            data = json.loads(WEIGHTS_PATH.read_text(encoding="utf-8"))
            return (
                float(data.get("alpha", DEFAULT_ALPHA)),
                float(data.get("beta", DEFAULT_BETA)),
                float(data.get("gamma", DEFAULT_GAMMA)),
            )
        except (json.JSONDecodeError, TypeError):
            pass
    return DEFAULT_ALPHA, DEFAULT_BETA, DEFAULT_GAMMA
