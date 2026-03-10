"""CLI entry point: emit the next orchestrator command to run.

Usage::

    # Print the next ready-to-run command
    python -m knowledge_graph.next

    # Execute it directly
    eval "$(python -m knowledge_graph.next)"

    # Full auto-loop after a successful orchestrator run
    python -m orchestrator.main ... \\
      && python -m knowledge_graph.build \\
      && eval "$(python -m knowledge_graph.next)"

Exit codes:
    0  Command printed successfully.
    1  No unimplemented algorithm found (all done), or a recipe is incomplete.
    2  Output files missing (run `python -m knowledge_graph.build` first).
"""

from __future__ import annotations

import json
import shlex
import sys
from pathlib import Path

from knowledge_graph.config import OUTPUT_DIR


def main() -> int:
    graph_path = OUTPUT_DIR / "graph.json"
    curriculum_path = OUTPUT_DIR / "curriculum_order.json"
    recipes_path = OUTPUT_DIR / "recipes.json"

    for p in (graph_path, curriculum_path, recipes_path):
        if not p.exists():
            print(
                f"ERROR: {p.name} not found. Run `python -m knowledge_graph.build` first.",
                file=sys.stderr,
            )
            return 2

    graph = json.loads(graph_path.read_text(encoding="utf-8"))
    curriculum = json.loads(curriculum_path.read_text(encoding="utf-8"))
    recipes_payload = json.loads(recipes_path.read_text(encoding="utf-8"))
    recipes = recipes_payload.get("recipes", {})

    implemented = {
        n["id"]
        for n in graph.get("nodes", [])
        if n.get("type") == "algorithm" and n.get("status") == "implemented"
    }

    for item in curriculum.get("items", []):
        algo = item["algorithm"]
        if algo in implemented:
            continue

        recipe = recipes.get(algo)
        if not recipe:
            print(
                f"WARNING: algorithm '{algo}' is in curriculum but has no recipe. "
                "Run `python -m knowledge_graph.build` to rebuild.",
                file=sys.stderr,
            )
            continue

        mi = recipe.get("main_instruction", {})
        missing = [f for f in ("algorithm", "update_rule", "proof_sketch", "archetype") if not mi.get(f)]
        if missing:
            print(
                f"WARNING: recipe for '{algo}' is missing fields: {missing}. "
                "Edit seeds/planned.json or CATALOG.md before running.",
                file=sys.stderr,
            )
            return 1

        cmd = (
            "python -m orchestrator.main"
            f" --algorithm {shlex.quote(mi['algorithm'])}"
            f" --update-rule {shlex.quote(mi['update_rule'])}"
            f" --proof-sketch {shlex.quote(mi['proof_sketch'])}"
            f" --archetype {shlex.quote(mi['archetype'])}"
        )
        print(cmd)
        return 0

    print("All algorithms in the curriculum are already implemented.", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
