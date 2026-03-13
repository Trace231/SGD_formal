"""Phase 4 orchestration: Agent4 persists documentation (Glue + Layer 1)."""
from __future__ import annotations

import json
import re

from rich.console import Console

from orchestrator.agents import Agent, ToolRegistry
from orchestrator.audit_logger import AuditLogger
from orchestrator.config import DOC_ANCHORS, LIB_GLUE_ANCHORS, PROJECT_ROOT
from orchestrator.context_builders import (
    _collect_lib_declaration_names,
    _extract_catalog_lemma_names,
)
from orchestrator.file_io import snapshot_file
from orchestrator.git_utils import _get_modified_lean_files
from orchestrator.metrics import count_glue_tricks_sections
from orchestrator.phase4_helpers import Gate4Error, _apply_lib_insert, _parse_persister_json
from orchestrator.prompts import load_meta_prompt_b
from orchestrator.verify import check_glue_tricks_gate, check_used_in_tags

console = Console()

def phase4_persist(
    algorithm: str,
    target_file: str,
    plan: str,
    baseline_tracked: set[str],
    baseline_untracked: set[str],
) -> int:
    """Phase 4: Agent4 persists documentation (Glue + Layer 1).

    Returns new_tricks_added.
    """
    console.rule("[bold cyan]Phase 4/5 — Persist Documentation")
    registry = ToolRegistry()
    registry.register_default_tools()

    # Strict precondition: only persist after build is green and sorry is zero.
    verify_result = registry.call("run_lean_verify", target_file)
    if int(verify_result.get("exit_code", 1)) != 0 or int(verify_result.get("sorry_count", 1)) != 0:
        raise RuntimeError(
            "[Phase 4] BLOCKED: build must be green and sorry_count must be 0 "
            "before documentation persistence."
        )

    tricks_before = snapshot_file("docs/GLUE_TRICKS.md")
    tricks_sections_before = count_glue_tricks_sections()

    modified_lean_files = _get_modified_lean_files(
        baseline_tracked,
        baseline_untracked,
    )
    console.print(
        f"[cyan]\\[Phase 4] Modified Lean files detected: "
        f"{modified_lean_files or [target_file]}"
    )

    meta_b = load_meta_prompt_b()
    agent4 = Agent("persister", extra_files=modified_lean_files or [target_file])
    allowed_anchors = DOC_ANCHORS

    lib_anchor_info = "\n".join(
        f"- {f}: {list(a.keys())}" for f, a in LIB_GLUE_ANCHORS.items()
    )

    persistence_output = agent4.call(
        f"Persist the completed proof for algorithm '{algorithm}' using "
        f"Meta-Prompt B below.\n\n## Meta-Prompt B\n{meta_b}\n\n"
        f"## Approved proof plan (use this as [PROOF INPUT] for Meta-Prompt B)\n{plan}\n\n"
        f"## Modified Lean files\n"
        + "\n".join(f"- {f}" for f in (modified_lean_files or [target_file]))
        + "\n\n## Allowed doc anchor IDs\n"
        + "\n".join(f"- {k}" for k in sorted(allowed_anchors))
        + "\n\n## Lib/Glue anchor IDs (for lib_write ops)\n"
        + lib_anchor_info
    )
    console.print(
        f"[green]\\[Agent4] Persistence output generated "
        f"({len(persistence_output)} chars)."
    )

    try:
        patch_ops = _parse_persister_json(persistence_output)
    except json.JSONDecodeError as exc:
        raise RuntimeError(
            "[Phase 4] Persister returned invalid JSON. "
            f"line={exc.lineno}, col={exc.colno}, msg={exc.msg}"
        ) from exc

    if not isinstance(patch_ops, list):
        raise RuntimeError("[Phase 4] Persister output must be a JSON array.")

    patterns_from_output: list[str] = []
    catalog_patch_fragments: list[str] = []
    patch_ops_summary: list[dict] = []
    lib_write_ops: list[dict] = []
    algorithm_refactor_ops: list[dict] = []
    # Guard A: track anchors already patched in this run to prevent double-insert
    # when Agent4 emits two ops with the same anchor in one response.
    patched_anchors: set[str] = set()

    for idx, op in enumerate(patch_ops, start=1):
        if not isinstance(op, dict):
            raise RuntimeError(f"[Phase 4] patch_ops[{idx}] must be an object.")
        op_type = op.get("op", "doc_patch")

        if op_type == "doc_patch" or op_type is None:
            anchor_id = op.get("anchor")
            content = op.get("content")
            if not isinstance(anchor_id, str) or not isinstance(content, str):
                raise RuntimeError(
                    f"[Phase 4] patch_ops[{idx}] doc_patch requires 'anchor' and 'content'."
                )
            if anchor_id not in allowed_anchors:
                raise RuntimeError(
                    f"[Phase 4] patch_ops[{idx}] uses non-allowed anchor: {anchor_id}"
                )
            # Guard A: skip if this anchor was already patched earlier in this run.
            if anchor_id in patched_anchors:
                console.print(
                    f"[yellow]\\[Agent4] Skipping duplicate anchor {anchor_id} in same run"
                )
                continue
            # Guard B: for CATALOG_ALGO_LAYER, skip if algorithm section already exists.
            if anchor_id == "CATALOG_ALGO_LAYER":
                catalog_text = (PROJECT_ROOT / "docs/CATALOG.md").read_text(encoding="utf-8")
                algo_pat = (
                    rf"^## Algorithm Layer \(Layer 2\)\s+—\s+`Algorithms/{re.escape(algorithm)}\.lean`"
                )
                if re.search(algo_pat, catalog_text, re.MULTILINE):
                    console.print(
                        f"[cyan]\\[Agent4] Algorithm section already exists in CATALOG.md — skipping"
                    )
                    continue
            cfg = allowed_anchors[anchor_id]
            patch_result = registry.call(
                "apply_doc_patch",
                path=cfg["path"],
                anchor=cfg["regex"],
                new_content=content,
            )
            changed = bool(patch_result.get("changed", False))
            patch_ops_summary.append({
                "op": "doc_patch",
                "anchor": anchor_id,
                "path": cfg["path"],
                "changed": changed,
            })
            if changed:
                patched_anchors.add(anchor_id)
                console.print(
                    f"[green]\\[Agent4] Patched {cfg['path']} via anchor {anchor_id}"
                )
                if cfg["path"] == "docs/GLUE_TRICKS.md":
                    patterns_from_output.extend(re.findall(
                        r"^#{3,4}\s+Pattern[^\n]*",
                        content,
                        flags=re.MULTILINE,
                    ))
                if cfg["path"] == "docs/CATALOG.md":
                    catalog_patch_fragments.append(content)
            else:
                console.print(
                    f"[cyan]\\[Agent4] Skipped duplicate content for {cfg['path']} ({anchor_id})"
                )
        elif op_type == "lib_write":
            lib_write_ops.append(op)
        elif op_type == "algorithm_refactor":
            algorithm_refactor_ops.append(op)
        else:
            raise RuntimeError(
                f"[Phase 4] patch_ops[{idx}] unknown op: {op_type}. "
                "Allowed: doc_patch, lib_write, algorithm_refactor."
            )

    lib_snapshots: dict[str, str] = {}
    algo_snapshots: dict[str, str] = {}

    if lib_write_ops:
        console.print("[cyan]\\[Phase 4] Applying lib_write ops...")
        for idx, op in enumerate(lib_write_ops, start=1):
            file_path = op.get("file")
            anchor_id = op.get("anchor_id")
            content = op.get("content")
            if not all(isinstance(x, str) for x in (file_path, anchor_id, content)):
                raise RuntimeError(
                    f"[Phase 4] lib_write op {idx} requires file, anchor_id, content."
                )
            if file_path not in lib_snapshots:
                lib_snapshots[file_path] = snapshot_file(file_path)
            updated = _apply_lib_insert(file_path, anchor_id, content)
            registry.call("overwrite_file", path=file_path, content=updated)
            patch_ops_summary.append({
                "op": "lib_write",
                "path": file_path,
                "anchor_id": anchor_id,
            })
            console.print(f"[green]\\[Agent4] Inserted lemma into {file_path} via {anchor_id}")

        # Full-library build: catches cascade failures in algorithm files caused
        # by changes to Lib/Glue lemma signatures or new lemma insertions.
        build_result = registry.call("run_repo_verify")
        if int(build_result.get("exit_code", 1)) != 0:
            console.print("[red]\\[Phase 4] lib_write caused build failure. Rolling back...")
            for path, snap in lib_snapshots.items():
                registry.call("overwrite_file", path=path, content=snap)
            raise RuntimeError(
                "[Phase 4] Lib/refactor caused build failure. Rolled back.\n"
                + ("\n".join(build_result.get("errors", [])) or "Unknown error")
            )

    if algorithm_refactor_ops:
        console.print("[cyan]\\[Phase 4] Applying algorithm_refactor ops...")
        for idx, op in enumerate(algorithm_refactor_ops, start=1):
            file_path = op.get("file")
            patches = op.get("patches")
            if not isinstance(file_path, str) or not isinstance(patches, list):
                raise RuntimeError(
                    f"[Phase 4] algorithm_refactor op {idx} requires file and patches list."
                )
            if file_path not in algo_snapshots:
                algo_snapshots[file_path] = snapshot_file(file_path)
            for pidx, patch in enumerate(patches):
                old_str = patch.get("old_str")
                new_str = patch.get("new_str")
                if not isinstance(old_str, str) or not isinstance(new_str, str):
                    raise RuntimeError(
                        f"[Phase 4] algorithm_refactor op {idx} patch {pidx} "
                        "requires old_str and new_str."
                    )
                registry.call("edit_file_patch", path=file_path, old_str=old_str, new_str=new_str)
            patch_ops_summary.append({
                "op": "algorithm_refactor",
                "path": file_path,
                "patches_count": len(patches),
            })
            console.print(f"[green]\\[Agent4] Refactored {file_path} ({len(patches)} patch(es))")

        # Full-library build: catches cascade failures across all algorithm files,
        # not just the directly refactored ones.
        build_result = registry.call("run_repo_verify")
        if int(build_result.get("exit_code", 1)) != 0:
            console.print("[red]\\[Phase 4] algorithm_refactor caused build failure. Rolling back...")
            for path, snap in algo_snapshots.items():
                registry.call("overwrite_file", path=path, content=snap)
            raise RuntimeError(
                "[Phase 4] Algorithm refactor caused build failure. Rolled back.\n"
                + ("\n".join(build_result.get("errors", [])) or "Unknown error")
            )

    # Doc-code alignment: if CATALOG lemma status was touched, the lemmas must exist in Lib/.
    if catalog_patch_fragments:
        lib_names = _collect_lib_declaration_names()
        touched_lemmas: set[str] = set()
        for fragment in catalog_patch_fragments:
            touched_lemmas.update(_extract_catalog_lemma_names(fragment))
        missing = sorted(name for name in touched_lemmas if name not in lib_names)
        if missing:
            raise RuntimeError(
                "[Phase 4] CATALOG-Lib alignment failed. Missing Lib declarations: "
                + ", ".join(missing)
            )

    tricks_after = snapshot_file("docs/GLUE_TRICKS.md")
    tricks_sections_after = count_glue_tricks_sections()
    new_tricks = tricks_sections_after - tricks_sections_before

    # Gate 3: GLUE_TRICKS validation (BLOCKING)
    glue_changed = (tricks_before != tricks_after) or (new_tricks > 0)
    unique_patterns = sorted(set(patterns_from_output))
    gate3_ok, missing_patterns = check_glue_tricks_gate(
        tricks_before,
        tricks_after,
        unique_patterns,
    )
    if not gate3_ok:
        raise RuntimeError(
            "[Gate 3] Missing GLUE_TRICKS pattern entries: "
            + ", ".join(missing_patterns)
        )

    if glue_changed:
        console.print(
            f"[green]\\[Gate 3] GLUE_TRICKS.md updated — "
            f"{new_tricks} new pattern(s)."
        )
    else:
        console.print("[green]\\[Gate 3] No new patterns — GLUE_TRICKS.md unchanged.")

    # Gate 4: Used-in tag check — covers all modified Lean files, not just target
    modified = modified_lean_files or [target_file]
    missing = check_used_in_tags(modified)
    if missing:
        raise Gate4Error(missing)
    else:
        console.print("[green]\\[Gate 4] All Used-in tags present.")

    AuditLogger.get().add_phase4_data(patch_ops_summary)
    return new_tricks


