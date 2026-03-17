"""Regression tests for APOLLO-aligned Agent3 sampling/search policy."""

from orchestrator import phase3_agent8 as a8


def _mk_target(tmp_path):
    target = tmp_path / "SubgradientMethod.lean"
    target.write_text("theorem t : True := by\n  trivial\n", encoding="utf-8")
    return str(target)


def test_agent8_result_score_prefers_clean_outcome():
    clean = {"exit_code": 0, "sorry_count": 0, "errors": ""}
    noisy = {"exit_code": 1, "sorry_count": 2, "errors": "Foo.lean:1:1: error: x"}
    assert a8._agent8_result_score(clean) < a8._agent8_result_score(noisy)


def test_sampling_early_stops_on_clean_candidate(monkeypatch, tmp_path):
    monkeypatch.setattr(a8, "AGENT8_AGENT3_SAMPLING_ENABLED", True)
    monkeypatch.setitem(a8.RETRY_LIMITS, "AGENT8_AGENT3_SAMPLE_CANDIDATES", 3)
    monkeypatch.setitem(a8.RETRY_LIMITS, "AGENT8_AGENT3_SAMPLE_MAX_CANDIDATES", 3)
    monkeypatch.setitem(a8.RETRY_LIMITS, "AGENT8_AGENT3_SAMPLE_DEGRADE_TICKS", 2)
    monkeypatch.setitem(a8.RETRY_LIMITS, "AGENT8_AGENT3_SAMPLE_MAX_TURNS_PER_CANDIDATE", 8)

    calls: list[int] = []

    def _fake_single(*_args, **kwargs):
        idx = int(kwargs["candidate_index"])
        calls.append(idx)
        if idx == 2:
            return {"exit_code": 0, "sorry_count": 0, "errors": ""}
        return {"exit_code": 1, "sorry_count": 3, "errors": "err"}

    monkeypatch.setattr(a8, "_agent8_run_agent3_single", _fake_single)
    out = a8._agent8_run_agent3(_mk_target(tmp_path), "plan", "prompt", None)
    assert out["exit_code"] == 0
    assert out["sorry_count"] == 0
    assert calls == [1, 2]


def test_sampling_non_improving_candidates_trigger_cutoff(monkeypatch, tmp_path):
    monkeypatch.setattr(a8, "AGENT8_AGENT3_SAMPLING_ENABLED", True)
    monkeypatch.setitem(a8.RETRY_LIMITS, "AGENT8_AGENT3_SAMPLE_CANDIDATES", 3)
    monkeypatch.setitem(a8.RETRY_LIMITS, "AGENT8_AGENT3_SAMPLE_MAX_CANDIDATES", 3)
    monkeypatch.setitem(a8.RETRY_LIMITS, "AGENT8_AGENT3_SAMPLE_DEGRADE_TICKS", 1)
    monkeypatch.setitem(a8.RETRY_LIMITS, "AGENT8_AGENT3_SAMPLE_MAX_TURNS_PER_CANDIDATE", 8)

    calls: list[int] = []

    def _fake_single(*_args, **kwargs):
        calls.append(int(kwargs["candidate_index"]))
        return {"exit_code": 1, "sorry_count": 5, "errors": "same"}

    monkeypatch.setattr(a8, "_agent8_run_agent3_single", _fake_single)
    _ = a8._agent8_run_agent3(_mk_target(tmp_path), "plan", "prompt", None)
    # First sample sets baseline, second non-improving sample triggers cutoff.
    assert calls == [1, 2]


def test_sampling_disabled_falls_back_to_single_path(monkeypatch, tmp_path):
    monkeypatch.setattr(a8, "AGENT8_AGENT3_SAMPLING_ENABLED", False)
    calls: list[tuple[int, int]] = []

    def _fake_single(*_args, **kwargs):
        calls.append((int(kwargs["candidate_index"]), int(kwargs["candidate_total"])))
        return {"exit_code": 1, "sorry_count": 1, "errors": "e"}

    monkeypatch.setattr(a8, "_agent8_run_agent3_single", _fake_single)
    _ = a8._agent8_run_agent3(_mk_target(tmp_path), "plan", "prompt", None)
    assert calls == [(1, 1)]


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
