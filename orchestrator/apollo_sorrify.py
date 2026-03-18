"""APOLLO decomposition helpers with bounded, fail-safe wrappers."""

from __future__ import annotations

import sys
from pathlib import Path
from typing import TYPE_CHECKING, Any, Callable

from orchestrator.config import (
    APOLLO_LAKE_PATH,
    APOLLO_PROJECT_PATH,
    APOLLO_REPL_WORKSPACE,
    APOLLO_VERIFY_TIMEOUT,
    PROJECT_ROOT,
)
from orchestrator.apollo_integration import verify_with_apollo

if TYPE_CHECKING:
    from orchestrator.repl_adapter import ReplSession


def _ensure_apollo_path() -> None:
    apollo_root = str(Path(APOLLO_PROJECT_PATH).resolve())
    if apollo_root not in sys.path:
        sys.path.insert(0, apollo_root)


def build_apollo_verify_callable(
    *,
    session: "ReplSession | None" = None,
    header_env_id: int | None = None,
) -> Callable[[str], dict[str, Any]]:
    """Return a APOLLO-compatible verifier(code)->result callable."""
    session_failed = False

    def _verify(code: str) -> dict[str, Any]:
        nonlocal session_failed
        if session is not None and header_env_id is not None and not session_failed:
            try:
                return session.verify(code, env=header_env_id)
            except Exception:
                # Fall back to the one-shot verifier when the persistent REPL
                # session desynchronizes or times out.
                session_failed = True
        return verify_with_apollo(
            code=code,
            timeout=APOLLO_VERIFY_TIMEOUT,
            apollo_project_path=Path(APOLLO_PROJECT_PATH),
            repl_workspace=Path(APOLLO_REPL_WORKSPACE),
            lake_path=APOLLO_LAKE_PATH,
            project_root=Path(PROJECT_ROOT),
        )

    return _verify


def apply_syntax_correction(code: str) -> tuple[str, dict[str, Any]]:
    """Apply APOLLO SyntaxCorrector with non-throwing behavior."""
    try:
        _ensure_apollo_path()
        from utils.syntax_repair import SyntaxCorrector

        corrected = SyntaxCorrector(code).correct_text()
        return corrected, {
            "ok": True,
            "changed": corrected != code,
            "backend": "apollo_utils",
        }
    except ImportError as exc:
        # Local fallback: keep no-op semantics for reliability.
        return code, {
            "ok": False,
            "error": str(exc),
            "changed": False,
            "backend": "local_fallback",
            "reason": "missing_apollo_utils",
        }
    except Exception as exc:
        return code, {
            "ok": False,
            "error": str(exc),
            "changed": False,
            "backend": "local_fallback",
            "reason": "syntax_stage_error",
        }


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
        return sorrified, {
            "ok": True,
            "changed": sorrified != code,
            "backend": "apollo_utils",
        }
    except ImportError as exc:
        return code, {
            "ok": False,
            "error": str(exc),
            "changed": False,
            "backend": "local_fallback",
            "reason": "missing_apollo_utils",
        }
    except Exception as exc:
        return code, {
            "ok": False,
            "error": str(exc),
            "changed": False,
            "backend": "local_fallback",
            "reason": "sorrify_stage_error",
        }


def apply_hint_repair(code: str, verifier: Callable[[str], dict[str, Any]]) -> tuple[str, dict[str, Any]]:
    """Apply APOLLO hint-based repair, then return repaired code."""
    try:
        _ensure_apollo_path()
        from utils.hint_repair import ProofRepairer

        repaired = ProofRepairer(code, verifier, verbose=False).repair_proof()
        return repaired, {
            "ok": True,
            "changed": repaired != code,
            "backend": "apollo_utils",
        }
    except ImportError as exc:
        return code, {
            "ok": False,
            "error": str(exc),
            "changed": False,
            "backend": "local_fallback",
            "reason": "missing_apollo_utils",
        }
    except Exception as exc:
        return code, {
            "ok": False,
            "error": str(exc),
            "changed": False,
            "backend": "local_fallback",
            "reason": "hint_stage_error",
        }


def extract_sublemmas(code: str, verifier: Callable[[str], dict[str, Any]]) -> tuple[list[str], dict[str, Any]]:
    """Extract sub-lemmas from sorry states for downstream glue/strategy routing."""
    try:
        _ensure_apollo_path()
        from utils.extract_lemmas_from_sorry import LemmaExtractor

        lemmas = LemmaExtractor(code, verifier).get_lemmas()
        names: list[str] = []
        statements: list[str] = []
        for lemma in lemmas:
            text = str(lemma or "").strip()
            if not text:
                continue
            first_decl = next(
                (ln.strip() for ln in text.splitlines() if ln.strip().startswith(("lemma ", "theorem "))),
                "",
            )
            if first_decl:
                names.append(first_decl.split()[1].split(":")[0])
                statements.append(first_decl[:240])
            else:
                names.append("")
                statements.append(text.splitlines()[0][:240])
        return lemmas, {
            "ok": True,
            "count": len(lemmas),
            "statements": statements,
            "names": names,
        }
    except Exception as exc:
        return [], {"ok": False, "error": str(exc), "count": 0}

