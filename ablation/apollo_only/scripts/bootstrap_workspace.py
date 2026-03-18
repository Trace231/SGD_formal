#!/usr/bin/env python3
"""Bootstrap an isolated APOLLO ablation workspace snapshot."""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
from datetime import datetime, timezone
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[3]


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        while True:
            chunk = f.read(1024 * 1024)
            if not chunk:
                break
            h.update(chunk)
    return h.hexdigest()


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _render_workspace_lakefile() -> str:
    return """import Lake
open Lake DSL

package sgd_apollo_ablation

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"stable"

lean_lib StochOptLib where
  roots := #[`Lib]

@[default_target]
lean_lib Main where
  leanOptions := #[⟨`autoImplicit, false⟩]
  roots := #[`Main]
  extraDepTargets := #[`StochOptLib]

lean_lib AblationAlgorithms where
  roots := #[`Algorithms.SubgradientMethod_scaffold]
  extraDepTargets := #[`Main]
"""


def bootstrap(
    *,
    source_root: Path,
    workspace_root: Path,
    repl_binary_source: Path | None,
    force: bool,
) -> dict[str, str]:
    source_root = source_root.resolve()
    workspace_root = workspace_root.resolve()

    if force and workspace_root.exists():
        shutil.rmtree(workspace_root)

    workspace_root.mkdir(parents=True, exist_ok=True)

    src_lib = source_root / "Lib"
    src_docs = source_root / "docs"
    src_main = source_root / "Main.lean"
    src_scaffold = source_root / "Algorithms" / "sorry.lean"

    if not src_lib.exists():
        raise RuntimeError(f"source_lib_missing: {src_lib}")
    if not src_docs.exists():
        raise RuntimeError(f"source_docs_missing: {src_docs}")
    if not src_main.exists():
        raise RuntimeError(f"source_main_missing: {src_main}")
    if not src_scaffold.exists():
        raise RuntimeError(f"source_scaffold_missing: {src_scaffold}")

    dst_lib = workspace_root / "Lib"
    dst_docs = workspace_root / "docs"
    dst_main = workspace_root / "Main.lean"
    dst_lakefile = workspace_root / "lakefile.lean"
    dst_scaffold = workspace_root / "Algorithms" / "SubgradientMethod_scaffold.lean"
    dst_scaffold.parent.mkdir(parents=True, exist_ok=True)

    shutil.copytree(src_lib, dst_lib, dirs_exist_ok=True)
    shutil.copytree(src_docs, dst_docs, dirs_exist_ok=True)
    shutil.copy2(src_main, dst_main)
    shutil.copy2(src_scaffold, dst_scaffold)
    _write_text(dst_lakefile, _render_workspace_lakefile())

    # Wire a local repl binary into the isolated workspace so verification can
    # run without rebuilding REPL inside the snapshot each time.
    repl_target = workspace_root / ".lake" / "build" / "bin" / "repl"
    repl_target.parent.mkdir(parents=True, exist_ok=True)
    if repl_target.exists() or repl_target.is_symlink():
        repl_target.unlink()
    repl_link_status = "missing"
    repl_source_abs = ""
    if repl_binary_source is not None:
        repl_source = repl_binary_source.resolve()
        repl_source_abs = str(repl_source)
        if repl_source.exists():
            repl_target.symlink_to(repl_source)
            repl_link_status = "linked"
        else:
            repl_link_status = "source_not_found"

    meta = {
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "source_root": str(source_root),
        "workspace_root": str(workspace_root),
        "source_scaffold_path": str(src_scaffold),
        "workspace_scaffold_path": str(dst_scaffold),
        "source_scaffold_hash": _sha256_file(src_scaffold),
        "workspace_scaffold_hash": _sha256_file(dst_scaffold),
        "source_main_hash": _sha256_file(src_main),
        "workspace_main_hash": _sha256_file(dst_main),
        "repl_link_status": repl_link_status,
        "repl_binary_source": repl_source_abs,
        "workspace_repl_path": str(repl_target),
    }
    _write_text(
        workspace_root / ".apollo_ablation_meta.json",
        json.dumps(meta, indent=2, ensure_ascii=False) + "\n",
    )
    return {
        "workspace_root": str(workspace_root),
        "workspace_scaffold": str(dst_scaffold),
        "source_scaffold_hash": meta["source_scaffold_hash"],
        "metadata_path": str(workspace_root / ".apollo_ablation_meta.json"),
    }


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Bootstrap isolated APOLLO ablation workspace.")
    parser.add_argument(
        "--source-root",
        type=str,
        default=str(PROJECT_ROOT),
        help="Source SGD_APOLLO root.",
    )
    parser.add_argument(
        "--workspace-root",
        type=str,
        default=str(PROJECT_ROOT / "ablation" / "apollo_only" / "workspace"),
        help="Target isolated workspace root.",
    )
    parser.add_argument(
        "--force",
        action="store_true",
        help="Recreate workspace from scratch.",
    )
    parser.add_argument(
        "--repl-binary-source",
        type=str,
        default=str(PROJECT_ROOT.parent / "repl428" / ".lake" / "build" / "bin" / "repl"),
        help="Existing repl binary path to link into workspace.",
    )
    return parser


def main() -> int:
    args = build_arg_parser().parse_args()
    out = bootstrap(
        source_root=Path(args.source_root),
        workspace_root=Path(args.workspace_root),
        repl_binary_source=Path(args.repl_binary_source).resolve()
        if str(args.repl_binary_source).strip()
        else None,
        force=bool(args.force),
    )
    print(json.dumps(out, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

