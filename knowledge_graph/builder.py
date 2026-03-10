"""Build logic: sources -> graph -> recipes -> curriculum."""

from __future__ import annotations

import json
import logging
from datetime import datetime, timezone
from pathlib import Path

from knowledge_graph.config import (
    ALGORITHMS_DIR,
    OUTPUT_DIR,
    SEEDS_PATH,
    SGD_ROOT,
)
from knowledge_graph.graph import (
    Edge,
    Node,
    compute_difficulty,
    detect_cycles,
    topological_sort,
)
from knowledge_graph.sources import parse_all

logger = logging.getLogger(__name__)


def build_graph() -> dict:
    """Build the full graph from all sources."""
    data = parse_all()
    catalog = data["catalog"]
    audits = data["audits"]
    planned = data["planned"]
    methodology = data["methodology"]

    nodes: list[Node] = []
    edges: list[Edge] = []
    node_by_id: dict[str, Node] = {}

    # 1. Algorithm nodes from catalog
    for a in catalog.get("algorithms", []):
        algo_name = a.get("algorithm", "")
        if not algo_name:
            continue
        lean_path = ALGORITHMS_DIR / f"{algo_name}.lean"
        status = "implemented" if lean_path.exists() else "planned"
        node = Node(
            id=algo_name,
            type="algorithm",
            file=a.get("file", ""),
            status=status,
            extra={
                "archetype": a.get("archetype", ""),
                "update_rule": a.get("update_rule", ""),
                "proof_sketch": a.get("proof_sketch", ""),
                "leverage": a.get("leverage", 0.0),
                "leverage_reused": a.get("leverage_reused", 0),
                "leverage_new": a.get("leverage_new", 0),
            },
        )
        nodes.append(node)
        node_by_id[algo_name] = node

    # 2. Algorithm nodes from planned (seeds)
    for algo_name, entry in planned.items():
        if algo_name in node_by_id:
            continue
        node = Node(
            id=algo_name,
            type="algorithm",
            file=f"Algorithms/{algo_name}.lean",
            status="planned",
            extra={
                "archetype": entry.get("archetype", ""),
                "update_rule": entry.get("update_rule", ""),
                "proof_sketch": entry.get("proof_sketch", ""),
                "leverage": 0.0,
            },
        )
        nodes.append(node)
        node_by_id[algo_name] = node

    # 3. Glue nodes from catalog
    glue_by_symbol: dict[str, str] = {}
    for g in catalog.get("glue", []):
        sym = g.get("symbol", "")
        file_path = g.get("file", "")
        if not sym:
            continue
        node_type = "layer0" if "Layer0" in file_path else "glue"
        if "Layer1" in file_path:
            node_type = "layer1"
        node = Node(id=sym, type=node_type, file=file_path, status="implemented")
        nodes.append(node)
        node_by_id[sym] = node
        glue_by_symbol[sym] = file_path

    # 4. Edges: algorithm -> glue from catalog
    for a in catalog.get("algorithms", []):
        algo = a.get("algorithm", "")
        for g in a.get("glue_used", []):
            sym = g.get("symbol", "")
            if sym and algo in node_by_id:
                planned_status = "planned" if node_by_id[algo].status == "planned" else "implemented"
                edges.append(Edge(
                    source=algo,
                    target=sym,
                    type="uses",
                    reason=g.get("file", ""),
                    status=planned_status,
                ))

    # 5. Edges from planned
    for algo_name, entry in planned.items():
        for g in entry.get("glue_required", []):
            sym = g.get("symbol", "") if isinstance(g, dict) else ""
            if sym and algo_name in node_by_id:
                edges.append(Edge(
                    source=algo_name,
                    target=sym,
                    type="uses",
                    reason=g.get("reason", "") if isinstance(g, dict) else "",
                    status="planned",
                ))

    # 6. depends_on: algorithm -> algorithm (from shared glue)
    algo_ids = {n.id for n in nodes if n.type == "algorithm"}
    for e in edges:
        if e.type == "uses" and e.source in algo_ids and e.target in node_by_id:
            glue_node = node_by_id[e.target]
            if glue_node.type in ("glue", "layer1", "layer0"):
                pass  # algorithm uses glue; no algorithm-to-algorithm from this

    # 7. Cycle detection
    cycles = detect_cycles(edges, algo_ids)
    if cycles:
        logger.warning("Cycle detected in algorithm dependencies: %s", cycles)
        for cycle in cycles:
            if len(cycle) >= 2:
                edges = [x for x in edges if not (x.type == "depends_on" and x.source == cycle[0] and x.target == cycle[1])]
                break

    # 8. Topological sort for depth
    depth_map = topological_sort(nodes, edges)
    max_algo_depth = max(depth_map.values()) if depth_map else 0
    for n in nodes:
        if n.type == "algorithm" and n.id in depth_map:
            n.depth = 3 + depth_map[n.id]
        elif n.type == "layer0":
            n.depth = 0
        elif n.type == "glue":
            n.depth = 1
        elif n.type == "layer1":
            n.depth = 2

    # 9. Difficulty from audits
    for n in nodes:
        if n.type != "algorithm":
            continue
        algo_runs = audits.get(n.id, [])
        leverage = n.extra.get("leverage", 0.0)
        retries = 0
        lib_coverage = None
        if algo_runs:
            latest = algo_runs[-1]
            retries = latest.get("retry_count", 0)
        n.difficulty_score = compute_difficulty(leverage, retries, lib_coverage)

    # 10. Prerequisites and similar_to
    for n in nodes:
        if n.type != "algorithm":
            continue
        used_glue = set()
        for e in edges:
            if e.source == n.id and e.type == "uses":
                used_glue.add(e.target)
        n.extra["depends_on"] = list(used_glue)
        n.extra["depended_by"] = [
            e.source for e in edges
            if e.target == n.id and e.type == "uses" and e.source in algo_ids
        ]
        n.extra["prerequisites"] = []
        n.extra["similar_to"] = []

    # Build output dict
    return {
        "nodes": [n.to_dict() for n in nodes],
        "edges": [e.to_dict() for e in edges],
        "_node_by_id": node_by_id,
        "_edges": edges,
        "_nodes": nodes,
    }


def build_recipes(graph_data: dict) -> dict:
    """Build recipe cards for each algorithm."""
    node_by_id = graph_data.get("_node_by_id", {})
    nodes = graph_data.get("_nodes", [])
    edges = graph_data.get("_edges", [])

    from knowledge_graph.sources import parse_all
    data = parse_all()
    catalog = data["catalog"]
    planned = data["planned"]
    methodology = data["methodology"]

    algo_map = {a["algorithm"]: a for a in catalog.get("algorithms", [])}

    recipes = {}
    for n in nodes:
        if n.type != "algorithm":
            continue
        algo_name = n.id
        catalog_entry = algo_map.get(algo_name, {})
        planned_entry = planned.get(algo_name, {})

        meth = methodology.get(algo_name, {})
        update_rule = (
            catalog_entry.get("update_rule")
            or planned_entry.get("update_rule", "")
            or meth.get("output", "")
        )
        proof_sketch = (
            catalog_entry.get("proof_sketch")
            or planned_entry.get("proof_sketch", "")
            or meth.get("method", "")
        )
        archetype = catalog_entry.get("archetype") or planned_entry.get("archetype", "")

        glue_required = []
        for e in edges:
            if e.source == algo_name and e.type == "uses":
                target_node = node_by_id.get(e.target)
                fpath = (target_node.file if target_node else "") or e.reason
                glue_required.append({
                    "symbol": e.target,
                    "file": fpath or e.reason,
                    "reason": e.reason,
                    "step": e.step or None,
                })

        difficulty = n.difficulty_score
        leverage = n.extra.get("leverage", 0.0)
        retries = 0
        for a in data["audits"].get(algo_name, []):
            retries = max(retries, a.get("retry_count", 0))

        recipes[algo_name] = {
            "main_instruction": {
                "algorithm": algo_name,
                "update_rule": update_rule,
                "proof_sketch": proof_sketch,
                "archetype": archetype or "A",
            },
            "glue_required": glue_required,
            "difficulty": {
                "score": round(difficulty, 4),
                "sources": {"leverage": leverage, "retries": retries, "lib_coverage": None},
                "estimated_retries": max(1, retries + 1),
            },
            "assumptions": {
                "primary": planned_entry.get("assumptions_primary", {}),
                "alternatives": planned_entry.get("assumptions_alternatives", []),
            },
            "graph_position": {
                "depends_on": n.extra.get("depends_on", []),
                "depended_by": n.extra.get("depended_by", []),
                "depth": n.depth,
                "prerequisites": n.extra.get("prerequisites", []),
                "similar_to": n.extra.get("similar_to", []),
            },
        }

    return recipes


def build_curriculum_order(graph_data: dict) -> list[dict]:
    """Build curriculum order sorted by difficulty."""
    nodes = graph_data.get("_nodes", [])
    algo_nodes = [n for n in nodes if n.type == "algorithm"]
    algo_nodes.sort(key=lambda n: (n.difficulty_score, n.depth))


    depth_by_id = {n.id: n.depth for n in algo_nodes}
    ordered = []
    for n in algo_nodes:
        prereqs = n.extra.get("prerequisites", [])
        prereq_depths = [depth_by_id.get(p, 0) for p in prereqs if p in depth_by_id]
        satisfied = all(depth_by_id.get(n.id, 0) >= d for d in prereq_depths) if prereq_depths else True

        ordered.append({
            "algorithm": n.id,
            "difficulty_score": round(n.difficulty_score, 4),
            "depth": n.depth,
            "prerequisites_satisfied": satisfied,
        })

    return ordered


def run_build() -> tuple[dict, dict, list]:
    """Run full build and return (graph_dict, recipes_dict, curriculum_list)."""
    graph_data = build_graph()
    graph_dict = {
        "nodes": graph_data["nodes"],
        "edges": graph_data["edges"],
    }
    recipes = build_recipes(graph_data)
    curriculum = build_curriculum_order(graph_data)
    return graph_dict, recipes, curriculum
