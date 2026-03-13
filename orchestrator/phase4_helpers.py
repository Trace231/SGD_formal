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
    """Robustly parse Agent4 JSON output. Strips markdown blocks, tolerates trailing text.
    Coerces a bare JSON object into a single-element list for forward compatibility."""
    text = raw.strip()
    # Step 1: Strip markdown code block if present.
    match = re.search(r'```(?:json)?\s*(.*?)\s*```', text, re.DOTALL)
    if match:
        text = match.group(1).strip()
    text = text.strip()
    if not text:
        raise ValueError("Persister output is empty")
    # Step 2: If text doesn't start with { or [, find first occurrence (Agent4 may return prose before JSON)
    start_idx = 0
    for i, c in enumerate(text):
        if c in ('{', '['):
            start_idx = i
            break
    else:
        raise ValueError("No JSON object or array found in persister output")
    # Step 3: Parse from the first { or [
    decoder = json.JSONDecoder()
    obj, _ = decoder.raw_decode(text, start_idx)
    # Step 4: Coerce bare object to list (Agent4 sometimes returns a single op as an object)
    if isinstance(obj, dict):
        obj = [obj]
    return obj


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


