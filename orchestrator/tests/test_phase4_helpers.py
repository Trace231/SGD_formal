"""Tests for robust Agent4 JSON extraction helpers."""

from orchestrator.phase4_helpers import _parse_persister_json


def test_parse_persister_json_accepts_fenced_json_array():
    raw = """Here is the patch set:
```json
[
  {"op":"doc_patch","anchor":"CATALOG_ROADMAP","content":"x"}
]
```"""
    ops = _parse_persister_json(raw)
    assert isinstance(ops, list)
    assert len(ops) == 1
    assert ops[0]["op"] == "doc_patch"


def test_parse_persister_json_accepts_prose_then_balanced_json():
    raw = (
        "I will patch docs first. "
        '[{"op":"doc_patch","anchor":"GLUE_PATTERNS","content":"abc"}] '
        "Then verify."
    )
    ops = _parse_persister_json(raw)
    assert isinstance(ops, list)
    assert ops[0]["anchor"] == "GLUE_PATTERNS"


def test_parse_persister_json_coerces_single_object_to_list():
    raw = '{"op":"algorithm_refactor","file":"Algorithms/SubgradientMethod.lean","patches":[]}'
    ops = _parse_persister_json(raw)
    assert isinstance(ops, list)
    assert len(ops) == 1
    assert ops[0]["op"] == "algorithm_refactor"

