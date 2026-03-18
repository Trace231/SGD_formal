"""Regression tests for APOLLO-aligned Agent3 sampling/search policy."""

from orchestrator import phase3_agent8 as a8
from orchestrator import phase3_agent3 as a3


def _mk_target(tmp_path):
    target = tmp_path / "SubgradientMethod.lean"
    target.write_text("theorem t : True := by\n  trivial\n", encoding="utf-8")
    return str(target)


def test_agent8_result_score_prefers_clean_outcome():
    clean = {"exit_code": 0, "sorry_count": 0, "errors": ""}
    noisy = {"exit_code": 1, "sorry_count": 2, "errors": "Foo.lean:1:1: error: x"}
    assert a8._agent8_result_score(clean) < a8._agent8_result_score(noisy)


def test_agent8_budget_wrapper_delegates_to_agent3_kernel(monkeypatch, tmp_path):
    captured = {}

    def _fake_kernel(*args, **kwargs):
        captured["args"] = args
        captured["kwargs"] = kwargs
        return {"exit_code": 0, "sorry_count": 0, "errors": "", "candidate_id": "d1.c1"}

    monkeypatch.setattr(a3, "run_agent3_search_kernel", _fake_kernel)
    out = a8._agent8_run_agent3(_mk_target(tmp_path), "plan", "prompt", None)
    assert out["exit_code"] == 0
    assert out["candidate_id"] == "d1.c1"
    assert captured["kwargs"]["run_single_candidate"] is a8._agent8_run_agent3_single


def test_agent8_wrapper_passes_error_subtype_to_kernel(monkeypatch, tmp_path):
    seen = {}

    def _fake_kernel(*args, **kwargs):
        seen["error_subtype"] = kwargs.get("error_subtype")
        return {"exit_code": 1, "sorry_count": 1, "errors": "e"}

    monkeypatch.setattr(a3, "run_agent3_search_kernel", _fake_kernel)
    _ = a8._agent8_run_agent3(
        _mk_target(tmp_path),
        "plan",
        "prompt",
        None,
        error_subtype="proof_api_mismatch",
    )
    assert seen["error_subtype"] == "proof_api_mismatch"


def test_patch_line_span_estimator_and_limit_guard():
    small_old = "have h1 : True := by\n  trivial\n"
    small_new = "have h1 : True := by\n  simp\n"
    big_old = "\n".join([f"line{i}" for i in range(70)])
    big_new = "\n".join([f"line{i}" for i in range(70)])
    assert a8._estimate_patch_line_span(small_old, small_new) == 2
    assert a8._estimate_patch_line_span(big_old, big_new) == 70


def test_patch_decl_signature_detection():
    body_patch_old = "  rw [h]\n"
    body_patch_new = "  simp [h]\n"
    sig_patch_old = "theorem foo : True := by\n  sorry\n"
    sig_patch_new = "theorem foo : False := by\n  sorry\n"
    assert not a8._patch_touches_decl_signature(body_patch_old, body_patch_new)
    assert a8._patch_touches_decl_signature(sig_patch_old, sig_patch_new)


def test_extract_decl_signatures_tracks_signature_changes():
    before = "theorem foo : True := by\n  trivial\nlemma bar : Nat := 1\n"
    after = "theorem foo : False := by\n  trivial\nlemma bar : Nat := 1\n"
    sig_before = a8._extract_decl_signatures(before)
    sig_after = a8._extract_decl_signatures(after)
    assert sig_before != sig_after
