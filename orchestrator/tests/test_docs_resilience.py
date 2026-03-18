"""Regression tests for reduced-doc and missing-anchor workflows."""

from orchestrator import phase4
from orchestrator.prompts import (
    _DEFAULT_META_PROMPT_A,
    _DEFAULT_META_PROMPT_B,
    load_meta_prompt_a,
    load_meta_prompt_b,
)


class _FakeRegistry:
    def __init__(self, exc: Exception):
        self.exc = exc

    def call(self, *_args, **_kwargs):
        raise self.exc


def test_load_meta_prompts_falls_back_when_file_missing(monkeypatch):
    def _raise_file_not_found(_path):
        raise FileNotFoundError("docs/META_PROMPTS.md missing")

    monkeypatch.setattr("orchestrator.prompts.load_file", _raise_file_not_found)

    assert load_meta_prompt_a() == _DEFAULT_META_PROMPT_A.strip()
    assert load_meta_prompt_b() == _DEFAULT_META_PROMPT_B.strip()


def test_apply_doc_patch_with_fallback_skips_missing_file():
    result = phase4._apply_doc_patch_with_fallback(
        _FakeRegistry(FileNotFoundError("missing")),
        path="docs/CATALOG.md",
        anchor="^## Roadmap",
        new_content="x",
        anchor_id="CATALOG_ROADMAP",
    )

    assert result["changed"] is False
    assert result["skipped"] is True


def test_apply_doc_patch_with_fallback_skips_missing_anchor():
    result = phase4._apply_doc_patch_with_fallback(
        _FakeRegistry(ValueError("Anchor not found in docs/CATALOG.md: ^## Roadmap")),
        path="docs/CATALOG.md",
        anchor="^## Roadmap",
        new_content="x",
        anchor_id="CATALOG_ROADMAP",
    )

    assert result["changed"] is False
    assert result["skipped"] is True


def test_apply_doc_patch_with_fallback_reraises_other_value_errors():
    registry = _FakeRegistry(ValueError("new_content must be non-empty"))

    try:
        phase4._apply_doc_patch_with_fallback(
            registry,
            path="docs/CATALOG.md",
            anchor="^## Roadmap",
            new_content="x",
            anchor_id="CATALOG_ROADMAP",
        )
    except ValueError as exc:
        assert "new_content must be non-empty" in str(exc)
    else:
        raise AssertionError("expected ValueError to be re-raised")
