# SGD Methodology

This file is intentionally minimal for reduced-documentation experiments.

## 2. Stub-Probe Protocol

### Completed Algorithms

| Algorithm | Layer | Archetype | Method Note | Reuse Stats |
|-----------|-------|-----------|-------------|-------------|
| SGD | 2 | A (Layer 1) | Standard smooth convex/non-convex via `StochasticDescentHyps` | Uses 3 Layer 1 meta-theorems |
| SubgradientMethod | 2 | B (Layer 1 bypass) | Non-smooth convex via primitive subgradient inequality `∀ w s y, f y ≥ f w + ⟪gradL w s, y - w⟫_ℝ`; variance bound via `integral_norm_sq_gradL_comp_of_pointwise_bound` | Uses `norm_sq_sgd_step`; reuses Pattern A glue lemma |

### Next Recommended Probe

1. **Projected Subgradient Method** — extend SubgradientMethod with projection operator; reuse `proj_nonexp_sq` from `Lib/Glue/Algebra.lean`.
2. **Diminishing stepsize analysis** — replace constant `η` with `η_t = O(1/√t)`; requires telescoping sum variant.
3. **High-probability bounds** — add concentration inequalities for non-smooth setting.


## Minimal Roadmap

SGD and SubgradientMethod are the documented baselines in this profile.

### Completed Algorithms

| Algorithm | Layer | Archetype | Method Note | Reuse Stats |
|-----------|-------|-----------|-------------|-------------|
| SGD | 2 | A (Layer 1) | Standard smooth convex/non-convex via `StochasticDescentHyps` | Uses 3 Layer 1 meta-theorems |
| SubgradientMethod | 2 | B (Layer 1 bypass) | Non-smooth convex via primitive subgradient inequality `∀ w s y, f y ≥ f w + ⟪gradL w s, y - w⟫_ℝ` | Uses `norm_sq_sgd_step`; variance bound derived inline |

### Next Recommended Probe

1. **Projected Subgradient Method** — extend SubgradientMethod with projection operator; reuse `proj_nonexp_sq` from `Lib/Glue/Algebra.lean`.
2. **Diminishing stepsize analysis** — replace constant `η` with `η_t = O(1/√t)`; requires telescoping sum variant.
3. **High-probability bounds** — add concentration inequalities for non-smooth setting.


Use the SGD baseline as the reference proof shape:

1. Keep the algorithm file buildable.
2. Prefer direct Lean verification over prose-heavy planning.
3. Treat documentation as optional runtime context, not a correctness dependency.

## Minimal Roadmap

SGD is the only retained documented baseline in this profile.
