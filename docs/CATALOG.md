# SGD Catalog

This catalog is intentionally minimal for documentation-ablation runs.
It keeps only a compact SGD record plus the anchor sections that the
orchestrator still knows how to patch.

## Algorithm Layer (Layer 2) — `Algorithms/SGD.lean`

## Algorithm Layer (Layer 2) — `Algorithms/SubgradientMethod.lean`

### SubgradientMethod

`Algorithms/SubgradientMethod.lean` implements stochastic subgradient descent for convex non-smooth optimization.

**Setup structure**: `SubgradientSetup` — contains `w₀`, `η : ℕ → ℝ`, `gradL`, `ξ : ℕ → Ω → S`, `P`, measurability/independence hypotheses. **Critical**: NO `gradF` field (non-smooth objective has no gradient).

**Process**: `SubgradientSetup.process` — recursive definition `w_{t+1} = w_t - η_t • gradL(w_t, ξ_t)`.

**Bridge lemmas**: Uses `norm_sq_sgd_step` (Lib/Glue/Algebra.lean) for per-step norm expansion.

**Convergence theorem**: `subgradient_convergence_convex`
- **Assumptions**: Primitive subgradient inequality `∀ w s y, f y ≥ f w + ⟪gradL w s, y - w⟫_ℝ`; uniform oracle bound `∀ w s, ‖gradL w s‖ ≤ G`; constant stepsize `η_t = η`.
- **Result**: `(1/T) * ∑_{t=0}^{T-1} (E[f(w_t)] - f(w*)) ≤ ‖w₀ - w*‖² / (2ηT) + ηG²/2`
- **Proof structure**: (1) Pointwise norm expansion via `norm_sq_sgd_step`; (2) Derive `f(w_t) - f(w*) ≤ ⟪g_t, w_t - w*⟫` from primitive subgradient inequality; (3) Substitute into expansion; (4) Integrate + linearity; (5) Variance bound via `integral_mono` + `integral_const` from uniform oracle bound; (6) Telescope sum; (7) Algebraic rearrangement.

**Call chains**: `norm_sq_sgd_step` → pointwise bound → integral_mono → telescoping sum.

**Hit Report**: Pattern A (pointwise bound → integral bound) applied inline; no new glue lemmas extracted (existing `hasBoundedVariance_of_pointwise_bound` covers oracle-level bound).

**Leverage score**: 3 — Archetype B proof demonstrates Layer 1 bypass for non-smooth objectives; primitive subgradient inequality avoids abstract subdifferential machinery.


### SGD

`Algorithms/SGD.lean` is the baseline algorithm record kept in this reduced
setup. Follow-on Phase 4 insertions are allowed to append after this anchor.

## Roadmap & Dependency Tree

## Roadmap & Dependency Tree

| Algorithm | Status | Depends On | Notes |
|-----------|--------|------------|-------|
| SGD | Complete | Lib.Layer1.StochasticDescent | Baseline smooth convex/non-convex |
| SubgradientMethod | Complete | Lib.Glue.Algebra.norm_sq_sgd_step, Lib.Glue.Probability.integral_norm_sq_gradL_comp_of_pointwise_bound | Non-smooth convex; Archetype B (Layer 1 bypass via primitive subgradient inequality) |


## Roadmap & Dependency Tree

| Algorithm | Status | Depends On | Notes |
|-----------|--------|------------|-------|
| SGD | Complete | Lib.Layer1.StochasticDescent | Baseline smooth convex/non-convex |
| SubgradientMethod | Complete | Lib.Glue.Algebra.norm_sq_sgd_step | Non-smooth convex; Archetype B (Layer 1 bypass via primitive subgradient inequality) |


This section is intentionally minimal. In the reduced-doc configuration, the
orchestrator may append short algorithm notes here, but missing or stale
entries must not block a run.
