"""Regression tests for Mathlib import path validation in edit_file_patch / write_new_file."""
import pytest
from pathlib import Path

from orchestrator.tools import (
    _extract_new_mathlib_imports,
    validate_mathlib_imports,
    validate_required_import_presence,
    validate_required_imports,
)


# ---------------------------------------------------------------------------
# Unit tests: extraction helper
# ---------------------------------------------------------------------------

def test_extracts_newly_added_imports():
    old = "import Main\n"
    new = "import Main\nimport Mathlib.MeasureTheory.Measure.MeasureSpace\n"
    result = _extract_new_mathlib_imports(old, new)
    assert result == ["Mathlib.MeasureTheory.Measure.MeasureSpace"]


def test_does_not_flag_already_present_imports():
    text = "import Mathlib.MeasureTheory.Measure.MeasureSpace\n"
    result = _extract_new_mathlib_imports(text, text)
    assert result == []


def test_does_not_flag_non_mathlib_imports():
    old = "import Main\n"
    new = "import Main\nimport Lib.Glue.Algebra\n"
    result = _extract_new_mathlib_imports(old, new)
    assert result == []


# ---------------------------------------------------------------------------
# Unit tests: validator (against actual .lake package on disk)
# ---------------------------------------------------------------------------

def test_valid_mathlib_import_passes():
    """A module that actually exists should produce no errors."""
    old = ""
    new = "import Mathlib.MeasureTheory.Measure.MeasureSpace\n"
    errors = validate_mathlib_imports(old, new)
    assert errors == [], f"Unexpected errors: {errors}"


def test_nonexistent_mathlib_import_is_blocked():
    """The two historically-hallucinated imports must be caught."""
    old = ""
    new = (
        "import Mathlib.MeasureTheory.MeasureSpace\n"
        "import Mathlib.Probability.Basic\n"
    )
    errors = validate_mathlib_imports(old, new)
    modules = [e.split(":")[0].removeprefix("import ") for e in errors]
    assert "Mathlib.MeasureTheory.MeasureSpace" in modules
    assert "Mathlib.Probability.Basic" in modules


def test_error_message_contains_suggestion():
    """Error message should contain a path hint to help self-correction."""
    old = ""
    new = "import Mathlib.MeasureTheory.MeasureSpace\n"
    errors = validate_mathlib_imports(old, new)
    assert errors
    assert "search_codebase" in errors[0]


def test_no_errors_when_no_new_imports():
    errors = validate_mathlib_imports("import Main\n", "import Main\n")
    assert errors == []


# ---------------------------------------------------------------------------
# Unit tests: required import policy
# ---------------------------------------------------------------------------

def test_required_import_removal_detected():
    errors = validate_required_imports(
        rel_path="Algorithms/SubgradientMethod.lean",
        old_text="import Main\nimport Lib.Glue.Algebra\n",
        new_text="import Lib.Glue.Algebra\n",
    )
    assert errors
    assert "required import removed" in errors[0]


def test_required_import_presence_for_new_file():
    errors = validate_required_import_presence(
        rel_path="Algorithms/SubgradientMethod.lean",
        new_text="import Lib.Glue.Algebra\n",
    )
    assert errors
    assert "required import missing" in errors[0]


# ---------------------------------------------------------------------------
# Integration: edit_file_patch raises on hallucinated import
# ---------------------------------------------------------------------------

def test_edit_file_patch_blocked_on_bad_import(tmp_path, monkeypatch):
    """edit_file_patch must raise ValueError when a new import does not exist."""
    import orchestrator.tools as tools_mod

    lean_file = tmp_path / "Test.lean"
    lean_file.write_text("import Main\n", encoding="utf-8")

    # Redirect PROJECT_ROOT so _resolve_allowed_path accepts the temp file.
    monkeypatch.setattr(tools_mod, "PROJECT_ROOT", tmp_path)
    monkeypatch.setattr(tools_mod, "_READ_WRITE_ALLOWLIST", ("",))

    def _fake_resolve(path, allowlist):
        return tmp_path / Path(path).name

    monkeypatch.setattr(tools_mod, "_resolve_allowed_path", _fake_resolve)
    monkeypatch.setattr(
        tools_mod,
        "run_lean_verify",
        lambda _path: {"exit_code": 0, "error_count": 0, "errors": []},
    )

    with pytest.raises(ValueError, match="Patch blocked"):
        tools_mod.edit_file_patch(
            "Test.lean",
            "import Main\n",
            "import Main\nimport Mathlib.MeasureTheory.MeasureSpace\n",
        )


def test_edit_file_patch_allowed_on_valid_import(tmp_path, monkeypatch):
    """edit_file_patch must succeed when new import actually exists in mathlib."""
    import orchestrator.tools as tools_mod

    lean_file = tmp_path / "Test.lean"
    lean_file.write_text("import Main\n", encoding="utf-8")

    monkeypatch.setattr(tools_mod, "PROJECT_ROOT", tmp_path)
    monkeypatch.setattr(tools_mod, "_READ_WRITE_ALLOWLIST", ("",))

    def _fake_resolve(path, allowlist):
        return tmp_path / Path(path).name

    monkeypatch.setattr(tools_mod, "_resolve_allowed_path", _fake_resolve)
    monkeypatch.setattr(
        tools_mod,
        "run_lean_verify",
        lambda _path: {"exit_code": 0, "error_count": 0, "errors": []},
    )

    # Simulate that the mathlib file exists.
    fake_lean = (
        tmp_path
        / ".lake" / "packages" / "mathlib"
        / "Mathlib" / "MeasureTheory" / "Measure" / "MeasureSpace.lean"
    )
    fake_lean.parent.mkdir(parents=True)
    fake_lean.write_text("-- stub\n", encoding="utf-8")

    result = tools_mod.edit_file_patch(
        "Test.lean",
        "import Main\n",
        "import Main\nimport Mathlib.MeasureTheory.Measure.MeasureSpace\n",
    )
    assert result["replacements"] == 1


def test_edit_file_patch_blocks_removing_required_import(tmp_path, monkeypatch):
    import orchestrator.tools as tools_mod

    lean_file = tmp_path / "SubgradientMethod.lean"
    lean_file.write_text("import Main\nimport Lib.Glue.Algebra\n", encoding="utf-8")

    monkeypatch.setattr(tools_mod, "PROJECT_ROOT", tmp_path)
    monkeypatch.setattr(tools_mod, "_READ_WRITE_ALLOWLIST", ("",))
    monkeypatch.setattr(
        tools_mod,
        "_REQUIRED_IMPORTS_BY_FILE",
        {"SubgradientMethod.lean": {"import Main"}},
    )

    def _fake_resolve(path, allowlist):
        return tmp_path / Path(path).name

    monkeypatch.setattr(tools_mod, "_resolve_allowed_path", _fake_resolve)

    with pytest.raises(ValueError, match="required import guard"):
        tools_mod.edit_file_patch(
            "SubgradientMethod.lean",
            "import Main\nimport Lib.Glue.Algebra\n",
            "import Lib.Glue.Algebra\n",
        )


def test_import_change_regression_rolls_back(tmp_path, monkeypatch):
    import orchestrator.tools as tools_mod

    lean_file = tmp_path / "Test.lean"
    original = "import Main\nimport Lib.Glue.Algebra\n"
    updated = "import Main\nimport Mathlib.MeasureTheory.Measure.MeasureSpace\nimport Lib.Glue.Algebra\n"
    lean_file.write_text(original, encoding="utf-8")

    monkeypatch.setattr(tools_mod, "PROJECT_ROOT", tmp_path)
    monkeypatch.setattr(tools_mod, "_READ_WRITE_ALLOWLIST", ("",))

    def _fake_resolve(path, allowlist):
        return tmp_path / Path(path).name

    monkeypatch.setattr(tools_mod, "_resolve_allowed_path", _fake_resolve)

    fake_lean = (
        tmp_path
        / ".lake" / "packages" / "mathlib"
        / "Mathlib" / "MeasureTheory" / "Measure" / "MeasureSpace.lean"
    )
    fake_lean.parent.mkdir(parents=True)
    fake_lean.write_text("-- stub\n", encoding="utf-8")

    calls = {"n": 0}

    def _fake_verify(_path):
        calls["n"] += 1
        if calls["n"] == 1:
            return {"exit_code": 0, "error_count": 0, "errors": []}
        return {"exit_code": 1, "error_count": 9, "errors": ["unknown namespace"]}

    monkeypatch.setattr(tools_mod, "run_lean_verify", _fake_verify)

    with pytest.raises(ValueError, match="Patch rolled back"):
        tools_mod.edit_file_patch("Test.lean", original, updated)

    assert lean_file.read_text(encoding="utf-8") == original
