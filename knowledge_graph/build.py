"""CLI entry point for knowledge graph build."""

from __future__ import annotations

import argparse
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

from knowledge_graph.builder import run_build
from knowledge_graph.config import OUTPUT_DIR
from knowledge_graph.sources import parse_all, LeanUsedInParser


def _validate(recipes: dict, catalog_claims: list[tuple[str, str, str]]) -> tuple[list[str], list[str]]:
    """Run validation checks. Returns (errors, warnings)."""
    errors = []
    warnings = []
    for algo_name, recipe in recipes.items():
        mi = recipe.get("main_instruction", {})
        if not mi.get("algorithm"):
            errors.append(f"{algo_name}: main_instruction.algorithm is empty")
        if not mi.get("update_rule"):
            errors.append(f"{algo_name}: main_instruction.update_rule is empty")
        if not mi.get("proof_sketch"):
            errors.append(f"{algo_name}: main_instruction.proof_sketch is empty")
        if mi.get("archetype") not in ("A", "B"):
            errors.append(f"{algo_name}: main_instruction.archetype must be A or B (got {mi.get('archetype')})")

    STRUCTURE_FIELDS = {"wt", "ξt", "P", "η", "ν", "gradL", "gradF", "hP", "h_indep", "h_dist", "Field"}
    if catalog_claims:
        lean_parser = LeanUsedInParser()
        lean_uses = lean_parser.get_lean_uses()
        lean_refs: set[tuple[str, str]] = set()
        for (caller_file, caller_lemma), refs in lean_uses.items():
            for r in refs:
                if "Algorithms/" in str(r):
                    m = re.search(r"Algorithms/([^/\.]+)\.lean", str(r))
                    if m:
                        algo = m.group(1)
                        lean_refs.add((algo, caller_lemma))
        for algo, lemma, fpath in catalog_claims:
            if lemma in STRUCTURE_FIELDS or "`" in lemma:
                continue
            if "Main.lean" in (fpath or "") or "Mathlib" in (fpath or ""):
                continue
            if (fpath or "").startswith("Lib/") or (fpath or "").startswith("Algorithms/"):
                if (algo, lemma) not in lean_refs:
                    warnings.append(
                        f"Documentation rot: CATALOG claims {algo} uses {lemma}, "
                        f"but no Used-in reference found in Algorithms/*.lean"
                    )

    return errors, warnings


def main() -> int:
    parser = argparse.ArgumentParser(description="Build knowledge graph from SGD project.")
    parser.add_argument("--validate", action="store_true", help="Run validation after build")
    parser.add_argument("--visualize", action="store_true", help="Generate graph.html")
    args = parser.parse_args()

    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    graph_dict, recipes, curriculum = run_build()
    data = parse_all()
    catalog_claims = data["catalog"].get("hit_claims", [])

    (OUTPUT_DIR / "graph.json").write_text(
        json.dumps({"nodes": graph_dict["nodes"], "edges": graph_dict["edges"]}, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )

    recipes_payload = {
        "meta": {
            "built_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
            "algorithms_count": len(recipes),
        },
        "recipes": recipes,
    }
    (OUTPUT_DIR / "recipes.json").write_text(
        json.dumps(recipes_payload, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )

    curriculum_payload = {
        "order": [x["algorithm"] for x in curriculum],
        "items": curriculum,
    }
    (OUTPUT_DIR / "curriculum_order.json").write_text(
        json.dumps(curriculum_payload, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )

    n_algo = sum(1 for n in graph_dict["nodes"] if n.get("type") == "algorithm")
    n_glue = sum(1 for n in graph_dict["nodes"] if n.get("type") in ("glue", "layer0", "layer1"))
    print(f"Built {n_algo} algorithms, {n_glue} glue/layer nodes, curriculum order: {curriculum_payload['order']}")

    if args.validate:
        errors, warnings = _validate(recipes, catalog_claims)
        for w in warnings:
            print(f"Validation warning: {w}", file=sys.stderr)
        if errors:
            for e in errors:
                print(f"Validation error: {e}", file=sys.stderr)
            return 1
        print("Validation passed.")

    if args.visualize:
        from knowledge_graph.visualize import generate_html
        generate_html()
        print(f"Generated {OUTPUT_DIR / 'graph.html'}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
