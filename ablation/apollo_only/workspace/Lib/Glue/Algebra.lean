import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Inner Product Algebra Primitives for Gradient Steps (Glue Infrastructure)

Layer: Glue (pure math patches; no optimization or stochastic content)

These lemmas address a Gap Level 3 (form mismatch): Mathlib has the individual components
(`norm_sub_sq_real`, `inner_smul_right`, `norm_smul`), but no single named form covering
the norm-squared expansion of a gradient descent step.

Exported:
1. `norm_sq_sgd_step` — `‖(w − η•g) − w*‖² = ‖w − w*‖² − 2η⟨w−w*, g⟩ + η²‖g‖²`
   Used in: `stochastic_descent_convex'`, `stochastic_descent_strongly_convex'`
2. `inner_neg_smul_eq` — `⟪x, −(η•g)⟫ = −(η · ⟪x, g⟫)`
   Used in: `descent_lemma'` (non-convex pointwise bound)
3. `norm_neg_smul_sq` — `‖−(η•g)‖² = η² · ‖g‖²`
   Used in: `descent_lemma'` (non-convex pointwise bound)
4. `proj_nonexp_sq` — `‖proj x − w*‖² ≤ ‖x − w*‖²` when proj is non-expansive and proj(w*)=w*
   Used in: `pgd_convergence_convex_v2` (Algorithms/ProjectedGD.lean, Step 1 — projection bound)

Used by: `Lib.Layer1.StochasticDescent`.
-/

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- ============================================================================
-- Norm-squared expansion of a gradient step
-- ============================================================================

/-- Norm-squared expansion for a gradient descent step (shifted form).

Layer: Glue | Gap: Level 3 (form mismatch — no named form in Mathlib)
Technique: `abel` to match signs, then `norm_sub_sq_real` + `inner_smul_right` + `ring`
Proof steps:
  [L3: abel — rewrite (w − η•g) − w* as (w − w*) − η•g]
  [L0: norm_sub_sq_real — expand ‖a − b‖² = ‖a‖² − 2⟨a,b⟩ + ‖b‖²]
  [L3: inner_smul_right + norm_smul + mul_pow + sq_abs + ring]
Used in: `stochastic_descent_convex'`, `stochastic_descent_strongly_convex'`

`‖(w − η • g) − w*‖² = ‖w − w*‖² − 2η · ⟪w − w*, g⟫ + η² · ‖g‖²` -/
theorem norm_sq_sgd_step (w g wStar : E) (η : ℝ) :
    ‖(w - η • g) - wStar‖ ^ 2 =
      ‖w - wStar‖ ^ 2 - 2 * η * ⟪w - wStar, g⟫_ℝ + η ^ 2 * ‖g‖ ^ 2 := by
  have heq : (w - η • g) - wStar = (w - wStar) - η • g := by abel
  rw [heq, norm_sub_sq_real]
  simp [inner_smul_right, norm_smul, mul_pow, sq_abs]; ring

-- ============================================================================
-- Inner product and norm helpers for the non-convex step
-- ============================================================================

/-- Inner product with a negated smul: `⟪x, −(η • g)⟫ = −(η · ⟪x, g⟫)`.

Layer: Glue | Gap: Level 3 (composition of `inner_neg_right` + `inner_smul_right`)
Used in: `descent_lemma'` (non-convex pointwise bound in `StochasticDescent.lean`) -/
theorem inner_neg_smul_eq (x g : E) (η : ℝ) :
    ⟪x, -(η • g)⟫_ℝ = -(η * ⟪x, g⟫_ℝ) := by
  rw [inner_neg_right, inner_smul_right, mul_comm]

/-- Norm-squared of a negated smul: `‖−(η • g)‖² = η² · ‖g‖²`.

Layer: Glue | Gap: Level 3 (composition of `norm_neg` + `norm_smul` + `sq_abs`)
Used in: `descent_lemma'` (non-convex pointwise bound in `StochasticDescent.lean`) -/
theorem norm_neg_smul_sq (g : E) (η : ℝ) :
    ‖-(η • g)‖ ^ 2 = η ^ 2 * ‖g‖ ^ 2 := by
  rw [norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- Squared-distance contraction under a non-expansive projection with fixed point.

Layer: Glue | Gap: Level 2 (non-expansive norm bound lifted to squared norm form)
Used in: `Projected GD convex convergence` (Algorithms/ProjectedGD.lean, Step 1 — projection bound)

If `proj` is non-expansive and `wStar` is a fixed point of `proj`, then
`‖proj x - wStar‖² ≤ ‖x - wStar‖²`. -/
theorem proj_nonexp_sq (proj : E → E)
    (h : ∀ x y, ‖proj x - proj y‖ ≤ ‖x - y‖)
    (x wStar : E) (hproj_wStar : proj wStar = wStar) :
    ‖proj x - wStar‖ ^ 2 ≤ ‖x - wStar‖ ^ 2 := by
  have hw : wStar = proj wStar := hproj_wStar.symm
  calc
    ‖proj x - wStar‖ ^ 2 = ‖proj x - proj wStar‖ ^ 2 := by
      exact congrArg (fun z => ‖proj x - z‖ ^ 2) hw
    _ ≤ ‖x - wStar‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (h x wStar) 2
