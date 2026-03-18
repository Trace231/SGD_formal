"""Phase 4 (persist) helper utilities."""
from __future__ import annotations

import json
import re

from orchestrator.config import LIB_GLUE_ANCHORS
from orchestrator.file_io import snapshot_file

class Gate4Error(RuntimeError):
    """Raised by phase4_persist when Used-in docstring tags are absent.

    Carries ``missing`` as a structured list so the catch site never needs
    to parse a string representation.
    """

    def __init__(self, missing: list[str]) -> None:
        self.missing = missing
        super().__init__(f"[Gate 4] Missing Used-in tags: {missing}")




def _parse_persister_json(raw: str) -> list:
    """Robustly parse Agent4 JSON output.

    Tolerates:
    - prose before/after JSON
    - markdown fences
    - multiple candidate JSON snippets in one reply
    """
    text = (raw or "").strip()
    if not text:
        raise ValueError("Persister output is empty")

    # Candidate pools: full text + fenced blocks.
    candidates: list[str] = [text]
    for m in re.finditer(r"```(?:json)?\s*(.*?)\s*```", text, re.DOTALL):
        block = (m.group(1) or "").strip()
        if block:
            candidates.append(block)

    decoder = json.JSONDecoder()
    parse_errors: list[str] = []

    def _coerce_ops(obj: object) -> list | None:
        if isinstance(obj, dict):
            return [obj]
        if isinstance(obj, list):
            return obj
        return None

    # Pass 1: raw_decode from every { or [ start index.
    for cand in candidates:
        for i, c in enumerate(cand):
            if c not in ("{", "["):
                continue
            try:
                obj, _end = decoder.raw_decode(cand, i)
            except json.JSONDecodeError as exc:
                parse_errors.append(f"raw_decode@{i}: line={exc.lineno}, col={exc.colno}, {exc.msg}")
                continue
            coerced = _coerce_ops(obj)
            if coerced is not None:
                return coerced

    # Pass 2: bracket-balanced extraction fallback.
    def _extract_balanced_snippets(s: str) -> list[str]:
        snippets: list[str] = []
        for start in range(len(s)):
            ch = s[start]
            if ch not in ("{", "["):
                continue
            close = "}" if ch == "{" else "]"
            depth = 0
            in_str = False
            escape = False
            for idx in range(start, len(s)):
                cur = s[idx]
                if in_str:
                    if escape:
                        escape = False
                        continue
                    if cur == "\\":
                        escape = True
                        continue
                    if cur == '"':
                        in_str = False
                    continue
                if cur == '"':
                    in_str = True
                    continue
                if cur == ch:
                    depth += 1
                elif cur == close:
                    depth -= 1
                    if depth == 0:
                        snippets.append(s[start : idx + 1])
                        break
        return snippets

    for cand in candidates:
        for snippet in _extract_balanced_snippets(cand):
            try:
                obj = json.loads(snippet)
            except json.JSONDecodeError as exc:
                parse_errors.append(
                    f"json_loads snippet: line={exc.lineno}, col={exc.colno}, {exc.msg}"
                )
                continue
            coerced = _coerce_ops(obj)
            if coerced is not None:
                return coerced

    preview = text[:300].replace("\n", "\\n")
    detail = "; ".join(parse_errors[:3]) if parse_errors else "no parse candidates"
    raise ValueError(
        "Persister output has no parseable JSON object/array. "
        f"preview='{preview}' details={detail}"
    )


# ---------------------------------------------------------------------------
# Agent2 guided lookup helper
# ---------------------------------------------------------------------------



def _apply_lib_insert(file_path: str, anchor_id: str, content: str) -> str:
    """Insert content into a Lib/Glue file at the given anchor. Returns updated content."""
    if file_path not in LIB_GLUE_ANCHORS:
        raise ValueError(f"[Phase 4] Unknown Lib file for lib_write: {file_path}")
    anchors = LIB_GLUE_ANCHORS[file_path]
    if anchor_id not in anchors:
        raise ValueError(
            f"[Phase 4] Unknown anchor_id '{anchor_id}' for {file_path}. "
            f"Allowed: {list(anchors.keys())}"
        )
    cfg = anchors[anchor_id]
    regex = cfg["regex"]
    insert_mode = cfg.get("insert", "before")

    original = snapshot_file(file_path)
    if not original:
        raise FileNotFoundError(f"[Phase 4] Lib file does not exist: {file_path}")

    matches = list(re.finditer(regex, original, flags=re.MULTILINE))
    if not matches:
        raise ValueError(
            f"[Phase 4] Anchor regex not found in {file_path}: {regex[:50]}..."
        )
    if len(matches) > 1:
        raise ValueError(
            f"[Phase 4] Anchor matches {len(matches)} locations in {file_path}"
        )
    m = matches[0]
    insert_body = "\n\n" + content.strip() + "\n"
    if insert_mode == "before":
        insert_at = m.start()
        updated = original[:insert_at] + insert_body + original[insert_at:]
    else:
        insert_at = m.end()
        updated = original[:insert_at] + insert_body + original[insert_at:]
    return updated


