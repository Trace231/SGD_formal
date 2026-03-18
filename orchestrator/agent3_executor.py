"""Agent3 single-step tool execution helpers."""
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from orchestrator.config import PROJECT_ROOT
from orchestrator.file_io import load_file

@dataclass
class ExecutionResult:
    """Result envelope for each Agent3 tool execution."""

    status_code: str  # SUCCESS / ERROR / BLOCKED
    message: str
    attempt: int = 0


_SUBGRADIENT_CONTEXT = """

## Note: subdifferential symbols (Mathlib 4.28+)

`Mathlib.Analysis.Convex.Subdifferential` has been REMOVED in Mathlib 4.28.
Do NOT add `import Mathlib.Analysis.Convex.Subdifferential` — this module no longer exists.
Instead, define these symbols locally in your algorithm file, placed AFTER `end <SetupNamespace>`:

  def subdifferential (_ : Type*) (f : E → ℝ) (w : E) : Set E :=
    {g : E | ∀ y : E, f y ≥ f w + ⟪g, y - w⟫_ℝ}

  theorem mem_subdifferential_iff {f : E → ℝ} {w g : E} :
      g ∈ subdifferential ℝ f w ↔ ∀ y : E, f y ≥ f w + ⟪g, y - w⟫_ℝ := Iff.rfl

Mark these as LOCAL in symbol_manifest, NOT as VERIFIED from Mathlib.
"""

_SYMBOL_WHITELIST: frozenset[str] = frozenset()




def _execute_single_tool_and_format(
    registry: "ToolRegistry",
    tool_name: str,
    arguments: dict,
    target_file: str,
) -> tuple[str, dict | None, bool]:
    """Execute one Agent3 tool call and return a formatted result string.

    Returns (result_msg, verify_result_or_None, edited_flag).
    - result_msg   : the string to feed back to Agent3.
    - verify_result: the raw dict from run_lean_verify, or None.
    - edited_flag  : True when a write/patch tool was called.

    Error handling:
    - PermissionError → BLOCKED message; edited_flag=False.
    - ValueError (patch mismatch, etc.) → detailed error; edited_flag=False.
    - Unknown tool name → error string; edited_flag=False.
    - Any other exception → error string; edited_flag=False.
    """
    verify_result: dict | None = None
    edited = False

    try:
        result = registry.call(tool_name, **arguments)
    except KeyError as exc:
        return (
            f"## Tool error\ntool `{tool_name}` is not registered. "
            f"Available: read_file, search_in_file, edit_file_patch, write_new_file, "
            f"get_lean_goal, check_lean_have, run_lean_verify, "
            f"request_agent6_glue, request_agent2_help, request_agent7_interface_audit.\nError: {exc}\n"
            "Choose a valid tool.",
            None,
            False,
        )
    except PermissionError as exc:
        return (
            f"## Tool error — BLOCKED\n"
            f"Security violation: {exc}\n"
            "You may only edit files inside Algorithms/ or Lib/.",
            None,
            False,
        )
    except ValueError as exc:
        err_str = str(exc)
        # Surface patch-mismatch clearly so Agent3 knows to re-read the file.
        if tool_name == "edit_file_patch" and (
            "not found in target file" in err_str or "old_str not found" in err_str
        ):
            from orchestrator.file_io import load_file
            tgt_content = ""
            try:
                tgt_content = load_file(target_file)[:6000]
            except Exception:  # noqa: BLE001
                pass
            return (
                f"## Tool error — PATCH MISMATCH\n"
                f"edit_file_patch failed: the SEARCH string was not found in the file.\n"
                f"You MUST copy SEARCH verbatim from the current file (exact whitespace).\n\n"
                f"### Current file content\n```lean\n{tgt_content}\n```\n"
                "Read the file again if needed, then retry with the exact matching string.",
                None,
                False,
            )
        return (f"## Tool error\n{tool_name} failed: {err_str}", None, False)
    except Exception as exc:  # noqa: BLE001
        return (f"## Tool error\n{tool_name} raised: {exc}", None, False)

    # Success path
    if tool_name == "run_lean_verify":
        verify_result = result
        exit_code = int(result.get("exit_code", 1))
        sorry_count = int(result.get("sorry_count", 0))
        errors = result.get("errors", [])
        err_text = "\n".join(errors) if isinstance(errors, list) else str(errors)
        warnings = result.get("warnings", [])
        warn_text = "\n".join(warnings) if isinstance(warnings, list) else str(warnings)

        from orchestrator.file_io import load_file
        tgt_content = ""
        try:
            tgt_path = Path(target_file) if Path(target_file).is_absolute() else PROJECT_ROOT / target_file
            if tgt_path.exists():
                tgt_content = load_file(target_file)[:6000]
        except Exception:  # noqa: BLE001
            pass

        parts = [
            f"## run_lean_verify result",
            f"exit_code: {exit_code}  |  sorry_count: {sorry_count}",
            "",
            "### Build errors",
            "```",
            err_text[:3000] if err_text else "(none)",
            "```",
        ]
        if warn_text:
            parts += [
                "",
                "### Warnings (informational only)",
                "```",
                warn_text[:1000],
                "```",
            ]
        parts += [
            "",
            f"### Current file ({target_file})",
            "```lean",
            tgt_content or "(file does not exist)",
            "```",
        ]
        if exit_code == 0 and sorry_count == 0:
            parts += ["", "Build is CLEAN and sorry_count=0. Output done if finished."]
        result_msg = "\n".join(parts)
    elif tool_name in ("edit_file_patch", "write_new_file"):
        edited = True
        extra = ""
        if isinstance(result, dict) and tool_name == "edit_file_patch":
            _matched = str(result.get("matched_line_range", "")).strip()
            _allowed = str(result.get("allowed_line_range", "")).strip()
            _hash_before = str(result.get("file_hash_before", ""))[:12]
            _hash_after = str(result.get("file_hash_after", ""))[:12]
            if _matched or _allowed or _hash_before or _hash_after:
                extra = (
                    f"\nmatched_line_range: {_matched or '(unknown)'}"
                    f"\nallowed_line_range: {_allowed or '(none)'}"
                    f"\nfile_hash_before: {_hash_before or '(unknown)'}"
                    f"\nfile_hash_after: {_hash_after or '(unknown)'}"
                )
        result_msg = (
            f"## {tool_name} result\n"
            f"SUCCESS. File updated.{extra}\n"
            "Call run_lean_verify to check the build."
        )
    else:
        # read_file, search_in_file, overwrite_file, etc.
        if isinstance(result, dict):
            result_msg = f"## {tool_name} result\n" + "\n".join(
                f"{k}: {v}" for k, v in result.items()
            )
        elif isinstance(result, str):
            result_msg = f"## {tool_name} result\n{result}"
        else:
            result_msg = f"## {tool_name} result\n{result!r}"

    return result_msg, verify_result, edited


def _format_done_rejection(verify_result: dict, target_file: str) -> str:
    """Return feedback for when Agent3 signals done but verification is not clean."""
    exit_code = int(verify_result.get("exit_code", 1))
    sorry_count = int(verify_result.get("sorry_count", 0))
    errors = verify_result.get("errors", [])
    err_text = "\n".join(errors) if isinstance(errors, list) else str(errors)

    from orchestrator.file_io import load_file
    tgt_content = ""
    try:
        tgt_path = Path(target_file) if Path(target_file).is_absolute() else PROJECT_ROOT / target_file
        if tgt_path.exists():
            tgt_content = load_file(target_file)[:6000]
    except Exception:  # noqa: BLE001
        pass

    return "\n".join([
        "## done signal rejected — build is NOT clean",
        f"exit_code: {exit_code}  |  sorry_count: {sorry_count}",
        "",
        "### Build errors",
        "```",
        err_text[:3000] if err_text else "(none)",
        "```",
        "",
        f"### Current file ({target_file})",
        "```lean",
        tgt_content or "(file does not exist)",
        "```",
        "",
        "You signalled done but the build is not clean. Continue fixing.",
    ])


# ---------------------------------------------------------------------------
# Phase implementations
# ---------------------------------------------------------------------------

