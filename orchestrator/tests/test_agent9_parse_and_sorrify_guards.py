from __future__ import annotations

from orchestrator.apollo_sorrify import apply_sorrify
from orchestrator.phase3a_agent9 import _extract_json_payload


def test_apply_sorrify_rejects_missing_theorem_header() -> None:
    source = "def foo : Nat := 1\n"
    out, meta = apply_sorrify(source, lambda _code: {"pass": False, "complete": False})
    assert out == source
    assert meta.get("ok") is False
    assert meta.get("reason") == "missing_theorem_header"
    assert "header" in str(meta.get("error", "")).lower()


def test_extract_json_payload_accepts_fenced_and_prefixed_output() -> None:
    raw = (
        "I checked the file. Final plan below.\n"
        "```json\n"
        '{"theorems": [], "recommended_order": []}'
        "\n```"
    )
    obj = _extract_json_payload(raw)
    assert isinstance(obj, dict)
    assert obj.get("theorems") == []
    assert obj.get("recommended_order") == []


def test_run_agent9_plan_short_circuits_when_no_declarations(tmp_path) -> None:
    from orchestrator.phase3a_agent9 import run_agent9_plan

    target = tmp_path / "NoDecl.lean"
    target.write_text("def foo : Nat := 1\n", encoding="utf-8")

    out = run_agent9_plan(str(target), guidance="plan", algo_name="NoDecl")
    assert out == {}
