# SGD Catalog

This catalog is intentionally minimal for sample-test runs.
It keeps only the SGD baseline record plus the anchor sections that the
orchestrator still knows how to patch.

## Algorithm Layer (Layer 2) — `Algorithms/SGD.lean`

### SGD

`Algorithms/SGD.lean` is the baseline algorithm record retained in this
sample-test profile.

## Roadmap & Dependency Tree

| Algorithm | Status | Depends On | Notes |
|-----------|--------|------------|-------|
| SGD | Complete | Lib.Layer1.StochasticDescent | Baseline smooth convex/non-convex |

This section is intentionally minimal. In the reduced-doc configuration, the
orchestrator may append short algorithm notes here, but missing or stale
entries must not block a run.
