"""Shared helpers for split prompt modules.

This module intentionally stays dependency-light to avoid package import cycles.
"""

def normalize_prompt_block(text: str) -> str:
    """Return text unchanged; placeholder for future shared prompt utilities."""
    return text


__all__ = ["normalize_prompt_block"]
