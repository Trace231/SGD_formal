"""Loop helper entry points for Phase3 orchestration.

This module currently provides light wrappers and shared placeholders to keep
the split structure explicit while preserving runtime behavior in
``phase3_agent3.phase3_prove``.
"""

from __future__ import annotations


def phase3_loop_banner() -> str:
    """Return the canonical banner label used for Phase 5/7."""
    return "Phase 5/7 — Proof Fill  [Agent8]"

