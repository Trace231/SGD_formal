"""APOLLO decomposition helpers with bounded, fail-safe wrappers."""

from __future__ import annotations

import sys
from pathlib import Path
from typing import Any, Callable

from orchestrator.config import (
    APOLLO_LAKE_PATH,
    APOLLO_PROJECT_PATH,
    APOLLO_REPL_WORKSPACE,
    APOLLO_VERIFY_TIMEOUT,
)
from orchestrator.apollo_integration import verify_with_apollo


def _ensure_apollo_path() -> None:
    apollo_root = str(Path(APOLLO_PROJECT_PATH).resolve())
    if apollo_root not in sys.path:
        sys.path.insert(0, apollo_root)


def build_apollo_verify_callable() -> Callable[[str], dict[str, Any]]:
    """Return a APOLLO-compatible verifier(code)->result callable."""

    def _verify(code: str) -> dict[str, Any]:
        return verify_with_apollo(
            code=code,
            timeout=APOLLO_VERIFY_TIMEOUT,
            apollo_project_path=Path(APOLLO_PROJECT_PATH),
            repl_workspace=Path(APOLLO_REPL_WORKSPACE),
            lake_path=APOLLO_LAKE_PATH,
        )

    return _verify


def apply_syntax_correction(code: str) -> tuple[str, dict[str, Any]]:
    """Apply APOLLO SyntaxCorrector with non-throwing behavior."""
    try:
        _ensure_apollo_path()
        from utils.syntax_repair import SyntaxCorrector

        corrected = SyntaxCorrector(code).correct_text()
        return corrected, {"ok": True, "changed": corrected != code}
    except Exception as exc:
        return code, {"ok": False, "error": str(exc), "changed": False}


def apply_sorrify(code: str, verifier: Callable[[str], dict[str, Any]]) -> tuple[str, dict[str, Any]]:
    """Apply APOLLO Sorrifier to isolate hard error blocks."""
    try:
        _ensure_apollo_path()
        from utils.sorrify import ProofTree, Sorrifier

        pt = ProofTree(code)
        pt.parse_lean_with_dot_subcases()
        if hasattr(pt, "fix_inline_have_text"):
            pt.fix_inline_have_text()
        checker = Sorrifier(pt, verifier, pbar=False)
        sorrified = checker.verify_and_fix_tree()
        return sorrified, {"ok": True, "changed": sorrified != code}
    except Exception as exc:
        return code, {"ok": False, "error": str(exc), "changed": False}


def apply_hint_repair(code: str, verifier: Callable[[str], dict[str, Any]]) -> tuple[str, dict[str, Any]]:
    """Apply APOLLO hint-based repair, then return repaired code."""
    try:
        _ensure_apollo_path()
        from utils.hint_repair import ProofRepairer

        repaired = ProofRepairer(code, verifier, verbose=False).repair_proof()
        return repaired, {"ok": True, "changed": repaired != code}
    except Exception as exc:
        return code, {"ok": False, "error": str(exc), "changed": False}


def extract_sublemmas(code: str, verifier: Callable[[str], dict[str, Any]]) -> tuple[list[str], dict[str, Any]]:
    """Extract sub-lemmas from sorry states for downstream glue/strategy routing."""
    try:
        _ensure_apollo_path()
        from utils.extract_lemmas_from_sorry import LemmaExtractor

        lemmas = LemmaExtractor(code, verifier).get_lemmas()
        return lemmas, {"ok": True, "count": len(lemmas)}
    except Exception as exc:
        return [], {"ok": False, "error": str(exc), "count": 0}

