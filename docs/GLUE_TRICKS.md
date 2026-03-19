# Glue Tricks

This file is intentionally reduced for ablation testing.

## Section 3 — Standard Proof Patterns

### Pattern A: Pointwise Bound → Bounded Variance (Two-Layer Design)

**Description**: Derive `∫ ‖gradL(wt(ω), ξt(ω))‖² ∂P ≤ G²` from uniform oracle bound `∀ w s, ‖gradL w s‖ ≤ G`.

**Lean template**:
```lean
have h_pointwise : ∀ ω, ‖gradL (wt ω) (ξt ω)‖ ^ 2 ≤ G ^ 2 := by
  intro ω
  exact pow_le_pow_left₀ (norm_nonneg _) (hbounded (wt ω) (ξt ω)) 2
have h_var : ∫ ω, ‖gradL (wt ω) (ξt ω)‖ ^ 2 ∂P ≤ G ^ 2 :=
  integral_norm_sq_gradL_comp_of_pointwise_bound
    hgL hmeas_wt hmeas_ξt hbounded h_int_sq
```

**Used in**: `SubgradientMethod.subgradient_convergence_convex` (variance bound step).

**Note**: For oracle-level bound `∀ w, ∫ s, ‖gradL w s‖² ∂ν ≤ G²`, use existing `hasBoundedVariance_of_pointwise_bound` from `Lib/Glue/Probability.lean`.


## Section 3 — Standard Proof Patterns

### Pattern A: Pointwise Bound → Bounded Variance (Two-Layer Design)

**Description**: Derive `∫ ‖gradL(wt(ω), ξt(ω))‖² ∂P ≤ G²` from uniform oracle bound `∀ w s, ‖gradL w s‖ ≤ G`.

**Lean template**:
```lean
have h_pointwise : ∀ ω, ‖gradL (wt ω) (ξt ω)‖ ^ 2 ≤ G ^ 2 := by
  intro ω
  exact pow_le_pow_left₀ (norm_nonneg _) (hbounded (wt ω) (ξt ω)) 2
have h_var : ∫ ω, ‖gradL (wt ω) (ξt ω)‖ ^ 2 ∂P ≤ G ^ 2 := by
  have h_mono : ∫ ω, ‖gradL (wt ω) (ξt ω)‖ ^ 2 ∂P ≤ ∫ ω, (G ^ 2 : ℝ) ∂P :=
    integral_mono h_int_sq (integrable_const (G ^ 2)) h_pointwise
  rw [integral_const, probReal_univ] at h_mono
  exact h_mono
```

**Used in**: `SubgradientMethod.subgradient_convergence_convex` (variance bound step).

**Note**: For oracle-level bound `∀ w, ∫ s, ‖gradL w s‖² ∂ν ≤ G²`, use existing `hasBoundedVariance_of_pointwise_bound` from `Lib/Glue/Probability.lean`.


No persistent pattern catalog is retained in the SGD-only docs profile.
If Agent4 discovers a truly reusable pattern, it may append a short entry
below this anchor, but the absence of extra sections must not be treated as
a failure.
