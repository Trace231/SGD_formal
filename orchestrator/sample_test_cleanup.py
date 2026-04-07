"""Cleanup helpers for sample-test isolation runs."""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

from orchestrator.audit_logger import AuditLogger
from orchestrator.config import PROJECT_ROOT, SAMPLE_TEST_CLEANUP_SPEC


def _resolve(path: str | Path, project_root: Path = PROJECT_ROOT) -> Path:
    p = Path(path)
    return p if p.is_absolute() else (project_root / p)


def load_cleanup_spec(spec_path: str | Path | None = None, *, project_root: Path = PROJECT_ROOT) -> dict[str, Any]:
    path = _resolve(spec_path or SAMPLE_TEST_CLEANUP_SPEC, project_root=project_root)
    return json.loads(path.read_text(encoding="utf-8"))


def apply_sample_test_cleanup(
    spec_path: str | Path | None = None,
    *,
    project_root: Path = PROJECT_ROOT,
) -> dict[str, Any]:
    spec = load_cleanup_spec(spec_path, project_root=project_root)
    summary: dict[str, Any] = {
        "rewrite_files": [],
        "regex_replacements": [],
        "deleted_files": [],
        "missing_files": [],
    }

    for item in spec.get("rewrite_files", []):
        target = _resolve(item["path"], project_root=project_root)
        template = _resolve(item["template"], project_root=project_root)
        content = template.read_text(encoding="utf-8")
        target.write_text(content, encoding="utf-8")
        summary["rewrite_files"].append(str(target.relative_to(project_root)))

    for item in spec.get("regex_replacements", []):
        target = _resolve(item["path"], project_root=project_root)
        if not target.exists():
            summary["missing_files"].append(str(target.relative_to(project_root)))
            continue
        original = target.read_text(encoding="utf-8")
        updated, count = re.subn(
            item["pattern"],
            item["replacement"],
            original,
            flags=re.MULTILINE,
        )
        if updated != original:
            target.write_text(updated, encoding="utf-8")
        summary["regex_replacements"].append(
            {
                "path": str(target.relative_to(project_root)),
                "count": int(count),
            }
        )

    for glob in spec.get("delete_globs", []):
        for path in sorted(project_root.glob(glob)):
            if path.is_file():
                path.unlink(missing_ok=True)
                summary["deleted_files"].append(str(path.relative_to(project_root)))

    AuditLogger.get().log_event("sample_test_cleanup", **summary)
    return summary


if __name__ == "__main__":
    result = apply_sample_test_cleanup()
    print(json.dumps(result, indent=2, ensure_ascii=False))
