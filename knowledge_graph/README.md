# Knowledge Graph Organizer

Isolated module that parses SGD project data (read-only), constructs a dependency graph, and outputs algorithm recipe cards for the orchestrator command line.

## Usage

```bash
# From SGD project root
python -m knowledge_graph.build
```

### Flags

- `--validate`: Run validation (recipe fields, cross-source consistency). Exit code 1 on failure.
- `--visualize`: Generate `output/graph.html` after build.

## Output

| File | Description |
|------|-------------|
| `output/graph.json` | Nodes and edges (algorithms, glue, layer0, layer1) |
| `output/recipes.json` | Recipe cards per algorithm (main_instruction, glue_required, difficulty, assumptions, graph_position) |
| `output/curriculum_order.json` | Algorithms sorted by difficulty |
| `output/graph.html` | D3.js visualization (with `--visualize`) |

## Recipe Schema

Each recipe contains:

- `main_instruction`: `algorithm`, `update_rule`, `proof_sketch`, `archetype` (for orchestrator CLI)
- `glue_required`: List of `{symbol, file, reason, step}`
- `difficulty`: `score`, `sources`, `estimated_retries`
- `assumptions`: `primary`, `alternatives`
- `graph_position`: `depends_on`, `depended_by`, `depth`, `prerequisites`, `similar_to`

## Planned Algorithms (seeds)

Add `seeds/planned.json` to define algorithms not yet in CATALOG:

```json
{
  "ClippedSGD": {
    "algorithm": "ClippedSGD",
    "update_rule": "w_{t+1} = w_t - η·clip_G(gradL(w_t, ξ_t))",
    "proof_sketch": "Bounded oracle by construction; reuse SGD convex rate with hasBoundedVariance_of_pointwise_bound",
    "archetype": "B",
    "glue_required": [
      {"symbol": "hasBoundedVariance_of_pointwise_bound", "file": "Lib/Glue/Probability.lean", "reason": "..."}
    ],
    "assumptions_primary": {"bounded": "‖clip_G(gradL w s)‖ ≤ G"}
  }
}
```

## Weights

Optional `weights.json` for difficulty formula:

```json
{
  "alpha": 0.4,
  "beta": 0.4,
  "gamma": 0.2
}
```

`difficulty_score = α*(1-leverage) + β*min(1, retries/5) + γ*(1-lib_coverage)`

## Isolation

This module does NOT import `orchestrator`. All data is read via `pathlib` from the SGD project.
