"""Node/edge types and difficulty formula for the knowledge graph."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any

from knowledge_graph.config import load_weights


@dataclass
class Node:
    """Graph node with id, type, and optional metadata."""

    id: str
    type: str  # algorithm | glue | layer1 | layer0
    file: str = ""
    status: str = "implemented"  # implemented | planned
    depth: int = 0
    difficulty_score: float = 0.0
    extra: dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> dict[str, Any]:
        d = {"id": self.id, "type": self.type, "status": self.status, "depth": self.depth}
        if self.file:
            d["file"] = self.file
        if self.difficulty_score > 0:
            d["difficulty_score"] = round(self.difficulty_score, 4)
        d.update(self.extra)
        return d


@dataclass
class Edge:
    """Graph edge with source, target, type, and optional metadata."""

    source: str
    target: str
    type: str  # uses | depends_on | similar_to
    reason: str = ""
    step: str = ""
    status: str = "implemented"  # implemented | planned

    def to_dict(self) -> dict[str, Any]:
        d = {"source": self.source, "target": self.target, "type": self.type}
        if self.reason:
            d["reason"] = self.reason
        if self.step:
            d["step"] = self.step
        if self.status != "implemented":
            d["status"] = self.status
        return d


def compute_difficulty(
    leverage: float,
    retries: int,
    lib_coverage: float | None,
) -> float:
    """Compute difficulty score from leverage, retries, and lib_coverage."""
    alpha, beta, gamma = load_weights()
    term1 = alpha * (1.0 - leverage) if leverage >= 0 else alpha
    term2 = beta * min(1.0, retries / 5.0) if retries >= 0 else 0.0
    term3 = gamma * (1.0 - (lib_coverage or 0.0)) if lib_coverage is not None else 0.0
    return term1 + term2 + term3


def detect_cycles(edges: list[Edge], node_ids: set[str]) -> list[list[str]]:
    """Detect cycles in the directed graph. Returns list of cycles (each cycle as list of node ids)."""
    adj: dict[str, list[str]] = {n: [] for n in node_ids}
    for e in edges:
        if e.type == "depends_on" and e.source in node_ids and e.target in node_ids:
            adj[e.source].append(e.target)

    cycles: list[list[str]] = []
    color: dict[str, int] = {}  # 0=white, 1=gray, 2=black
    parent: dict[str, str] = {}
    for n in node_ids:
        color[n] = 0

    def dfs(u: str, stack: list[str]) -> bool:
        color[u] = 1
        stack.append(u)
        for v in adj[u]:
            if color[v] == 1:
                cycle = stack[stack.index(v) :] + [v]
                cycles.append(cycle)
                return True
            if color[v] == 0 and dfs(v, stack):
                return True
        stack.pop()
        color[u] = 2
        return False

    for n in node_ids:
        if color[n] == 0:
            dfs(n, [])
    return cycles


def topological_sort(nodes: list[Node], edges: list[Edge]) -> dict[str, int]:
    """Assign depth to algorithm nodes via topological sort. Returns {node_id: depth}."""
    algo_ids = {n.id for n in nodes if n.type == "algorithm"}
    deps: dict[str, set[str]] = {a: set() for a in algo_ids}
    for e in edges:
        if e.type == "depends_on" and e.source in algo_ids and e.target in algo_ids:
            deps[e.source].add(e.target)

    depth_map: dict[str, int] = {}
    remaining = set(algo_ids)

    def get_depth(n: str) -> int:
        if n in depth_map:
            return depth_map[n]
        deps_n = deps.get(n, set()) & remaining
        if not deps_n:
            depth_map[n] = 0
            return 0
        depth_map[n] = 1 + max(get_depth(d) for d in deps_n)
        return depth_map[n]

    for n in algo_ids:
        get_depth(n)
    return depth_map
