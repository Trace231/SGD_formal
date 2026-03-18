"""Robust model-output parsing for Lean proof candidates."""

from __future__ import annotations

import re
from dataclasses import dataclass


_LEAN_BLOCK_RE = re.compile(r"```lean4?\s*(.*?)\s*```", re.DOTALL | re.IGNORECASE)
_BY_SPLIT_RE = re.compile(r":=\s*by(.*)$", re.DOTALL)


@dataclass(frozen=True)
class ParsedCandidate:
    """Parsed model output payload."""

    payload: str
    kind: str  # "proof_body" | "full_file" | "invalid"
    reason: str


def _extract_last_lean_block(text: str) -> str | None:
    blocks = _LEAN_BLOCK_RE.findall(text)
    if not blocks:
        return None
    return blocks[-1].strip()


def parse_model_output(raw_text: str) -> ParsedCandidate:
    """Parse model output into proof-body or full-file candidate."""
    text = (raw_text or "").strip()
    if not text:
        return ParsedCandidate(payload="", kind="invalid", reason="empty_output")

    block = _extract_last_lean_block(text)
    if block:
        text = block

    # Full-file candidate: contains imports + theorem and appears complete.
    if "import " in text and ("theorem " in text or "lemma " in text):
        return ParsedCandidate(payload=text, kind="full_file", reason="full_file_block")

    # Extract body from ":= by".
    m = _BY_SPLIT_RE.search(text)
    if m:
        body = m.group(1).strip()
        if body:
            return ParsedCandidate(payload=body, kind="proof_body", reason="after_colon_eq_by")

    # If it's already tactic lines, treat as proof body.
    if any(tok in text for tok in ("intro ", "simp", "rw ", "have ", "exact ", "calc", "rfl", "aesop", "linarith")):
        return ParsedCandidate(payload=text, kind="proof_body", reason="tactic_body_heuristic")

    # A short single-line Lean expression can also be a proof body.
    if "\n" not in text and len(text) <= 200:
        return ParsedCandidate(payload=text, kind="proof_body", reason="single_line_body")

    return ParsedCandidate(payload="", kind="invalid", reason="unrecognized_format")


def indent_proof_body(body: str, spaces: int = 2) -> str:
    """Indent proof-body lines for theorem insertion."""
    indent = " " * spaces
    lines = body.splitlines() or [body]
    return "\n".join(f"{indent}{ln}" if ln.strip() else "" for ln in lines).rstrip() + "\n"

