# StochOptLib Theorem Index

Compact, searchable list of all Layer 1 theorems and key definitions.
Maintained by Agent4 (archivist) — append new rows whenever a new Layer1 entry is added.

---

## Layer 1 — `Lib/Layer1/StochasticDescent.lean`

### Predicates / Definitions

| Name | Kind | Summary |
|------|------|---------|
| `IsUnbiased'` | `def` (Prop) | `E[gradL(w, ξ)] = gradF(w)` for all `w` |
| `HasBoundedVariance'` | `def` (Prop) | `E[‖gradL(w,ξ)‖²] ≤ σ²` for all `w` |
| `IsLSmooth'` | `def` (Prop) | `‖gradF(w) - gradF(v)‖ ≤ L‖w-v‖` (L-smoothness) |
| `IsGradientOf'` | `def` (Prop) | `gradF` is the gradient of `f` |
| `IsMinimizer'` | `def` (Prop) | `f(wStar) = inf f` |
| `StochasticDescentHyps` | `structure` | Bundled probabilistic/measurability hypotheses for one SGD step: `P, ν, wt, ξt, gradL, gradF, η` plus independence, distribution, measurability, unbiasedness fields |

### Lemmas / Theorems

| Name | Kind | Hypotheses (key) | Conclusion | Used in |
|------|------|------------------|-----------|---------|
| `descent_lemma'` | `lemma` | `IsLSmooth'`, gradient bound | `f(w - η·g) ≤ f(w) - η‖g‖² + L/2·η²‖g‖²` (descent lemma for smooth f) | internal |
| `stochastic_descent_nonconvex'` | `theorem` | `IsGradientOf'`, `IsLSmooth'`, `HasBoundedVariance'`, unbiasedness | `E[‖∇f(wₜ)‖²] ≤ (E[‖wₜ−w*‖²] − E[‖wₜ₊₁−w*‖²]) / (ηL) + η·σ²` (non-convex) | `Algorithms/SGD.lean` |
| `stochastic_descent_convex'` | `theorem` | `IsGradientOf'`, `ConvexOn`, `HasBoundedVariance'` | `E[‖wₜ₊₁−w*‖²] ≤ E[‖wₜ−w*‖²] − 2η(E[f(wₜ)]−f*) + η²σ²` | `Algorithms/SGD.lean` (`one_step_progress_convex`) |
| `stochastic_descent_strongly_convex'` | `theorem` | `IsGradientOf'`, `StrongConvexOn`, `HasBoundedVariance'` | `E[‖wₜ₊₁−w*‖²] ≤ (1−ημ)·E[‖wₜ−w*‖²] + η²σ²` | `Algorithms/SGD.lean` (`one_step_progress_sc`) |
| `stochastic_subgradient_convex'` | `theorem` | `hsubgrad_ineq : ∀ w, f(w*) ≥ f(w) + ⟪gradF(w), w*−w⟫`, `HasBoundedVariance'` | Same conclusion as `stochastic_descent_convex'` but **no smoothness needed** | `Algorithms/SubgradientMethod.lean` (`subgradient_convergence_convex_v2`) |

---

## Glue Library — `Lib/Glue/`

Key glue lemmas used across multiple algorithm files:

| Name | File | Summary |
|------|------|---------|
| `norm_sq_sgd_step` | `Lib/Glue/Algebra.lean` | `‖w − η·g − w*‖² = ‖w−w*‖² − 2η⟪w−w*, g⟫ + η²‖g‖²` (norm expansion) |
| `expectation_inner_gradL_eq` | `Lib/Layer0/IndepExpect.lean` | Unbiasedness + independence → `E[⟪h(wt), gradL(wt,ξt)⟫] = E[⟪h(wt), gradF(wt)⟫]` |
| `expectation_norm_sq_gradL_bound` | `Lib/Layer0/IndepExpect.lean` | `E[‖gradL(wt,ξt)‖²] ≤ σ²` (variance bound for stochastic iterates) |
| `convex_inner_lower_bound` | `Lib/Layer0/ConvexFOC.lean` | `f(v) ≥ f(w) + ⟪∇f(w), v−w⟫` (FOC for smooth convex f) |
| `strong_convex_inner_lower_bound` | `Lib/Layer0/ConvexFOC.lean` | `f(v) ≥ f(w) + ⟪∇f(w), v−w⟫ + μ/2·‖v−w‖²` (FOC for strongly convex f) |

---

## How to use this index

- **Agent2 (planner)**: Check this index before planning; if a theorem covers your setting, cite it in the leverage prediction.
- **Agent3 (sorry_closer)**: If you need a Layer1 theorem, look it up here first. Only add new Layer1 entries (Archetype B) when no existing theorem suffices.
- **Agent4 (archivist)**: After each run, append new rows to the appropriate table for any new theorems/defs added.
