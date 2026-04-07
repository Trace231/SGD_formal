"""Regression tests for Gate 4 Used-in tag checking."""

from pathlib import Path

from orchestrator import verify as verify_mod
from orchestrator.verify import check_used_in_tags, extract_new_lemmas


def test_extract_new_lemmas_includes_structure(tmp_path: Path, monkeypatch):
    monkeypatch.setattr(verify_mod, "PROJECT_ROOT", tmp_path)
    target = tmp_path / "Foo.lean"
    target.write_text(
        "/-- Used in: `main` (Foo.lean, setup) -/\n"
        "structure FooSetup where\n"
        "  x : Nat\n",
        encoding="utf-8",
    )

    assert extract_new_lemmas(target) == ["FooSetup"]


def test_check_used_in_tags_accepts_structure_with_tag(tmp_path: Path, monkeypatch):
    monkeypatch.setattr(verify_mod, "PROJECT_ROOT", tmp_path)
    target = tmp_path / "Foo.lean"
    target.write_text(
        "/-- Setup object.\n"
        "Used in: `main` (Foo.lean, setup)\n"
        "-/\n"
        "structure FooSetup where\n"
        "  x : Nat\n",
        encoding="utf-8",
    )

    assert check_used_in_tags([target]) == []


def test_check_used_in_tags_flags_structure_without_tag(tmp_path: Path, monkeypatch):
    monkeypatch.setattr(verify_mod, "PROJECT_ROOT", tmp_path)
    target = tmp_path / "Foo.lean"
    target.write_text(
        "/-- Setup object. -/\n"
        "structure FooSetup where\n"
        "  x : Nat\n",
        encoding="utf-8",
    )

    assert check_used_in_tags([target]) == ["Foo.lean:FooSetup"]


def test_extract_new_lemmas_keeps_qualified_def_name(tmp_path: Path, monkeypatch):
    monkeypatch.setattr(verify_mod, "PROJECT_ROOT", tmp_path)
    target = tmp_path / "Foo.lean"
    target.write_text(
        "/-- Used in: `main` (Foo.lean, setup) -/\n"
        "structure Foo where\n"
        "  x : Nat\n\n"
        "def Foo.bar : Nat := 0\n",
        encoding="utf-8",
    )

    assert extract_new_lemmas(target) == ["Foo", "Foo.bar"]


def test_check_used_in_tags_does_not_collapse_qualified_name(tmp_path: Path, monkeypatch):
    monkeypatch.setattr(verify_mod, "PROJECT_ROOT", tmp_path)
    target = tmp_path / "Foo.lean"
    target.write_text(
        "/-- Setup object.\n"
        "Used in: `main` (Foo.lean, setup)\n"
        "-/\n"
        "structure Foo where\n"
        "  x : Nat\n\n"
        "def Foo.bar : Nat := 0\n",
        encoding="utf-8",
    )

    assert check_used_in_tags([target]) == ["Foo.lean:Foo.bar"]
