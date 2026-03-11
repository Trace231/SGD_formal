import Lib.Layer0.GradientFTC
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Strong
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# First-Order Conditions for Convex and Strongly Convex Functions (Layer 0 Infrastructure)

Layer: 0 (pure math tools, no stochastic content)

Mathlib has `ConvexOn`, `StrongConvexOn`, and scalar FOC (`ConvexOn.le_slope_of_hasDerivAt`),
but lacks the multivariate first-order conditions for Hilbert spaces connected to `HasGradientAt`.

This file provides:
1. `convex_first_order_condition`: f(y) ≥ f(x) + ⟪∇f(x), y−x⟫
   Gap type: Level 1 (completely missing for Hilbert spaces in Mathlib).
2. `strong_convex_first_order_condition`: f(y) ≥ f(x) + ⟪∇f(x), y−x⟫ + μ/2·‖y−x‖²
   Gap type: Level 1 (completely missing), with Level 3 sub-step for gradient computation.
3. Corollaries `convex_inner_lower_bound` and `strong_convex_inner_lower_bound` for minimizers.

Triggered by: SGD convex and strongly convex convergence theorems.
-/

open MeasureTheory Set
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- ============================================================================
-- Part 1: Convex first-order condition
-- ============================================================================

/-- First-order condition for convex functions (multivariate, Hilbert space).

Layer: 0 | Gap: Level 1 (result absent from Mathlib for Hilbert spaces)
Technique: line-segment reduction to scalar — compose f with AffineMap.lineMap,
  apply scalar FOC `ConvexOn.le_slope_of_hasDerivAt`, identify derivative via
  `hasDerivAt_comp_lineSegment`.
Proof steps:
  [L3: g = f ∘ AffineMap.lineMap (form matching via ext+simp+abel)]
  [L0: ConvexOn.comp_affineMap]
  [L2: hasDerivAt_comp_lineSegment + simp at t=0]
  [L0: ConvexOn.le_slope_of_hasDerivAt]
  [L0: simp + linarith to conclude]
Used in: `strong_convex_first_order_condition`, `convex_inner_lower_bound`

If `f : E → ℝ` is convex on `Set.univ` and has gradient `gradF` everywhere, then
`f(y) ≥ f(x) + ⟪∇f(x), y − x⟫` for all `x, y`. -/
theorem convex_first_order_condition
    {f : E → ℝ} {gradF : E → E}
    (hconv : ConvexOn ℝ univ f)
    (hgrad : ∀ w, HasGradientAt f (gradF w) w)
    (x y : E) :
    f x + ⟪gradF x, y - x⟫_ℝ ≤ f y := by
  by_cases hxy : x = y
  · simp [hxy]
  · set d := y - x
    set g := fun t : ℝ => f (x + t • d)
    have hg_conv : ConvexOn ℝ univ g := by
      have : g = f ∘ (AffineMap.lineMap x (d + x)) := by
        ext t
        simp only [g, Function.comp_def, AffineMap.lineMap_apply_module']
        congr 1; abel
      rw [this]; exact hconv.comp_affineMap _
    have hg_deriv : HasDerivAt g (⟪gradF x, d⟫_ℝ) 0 := by
      have := hasDerivAt_comp_lineSegment hgrad x d 0
      simp only [zero_smul, add_zero] at this; exact this
    have hslope := hg_conv.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) zero_lt_one hg_deriv
    simp only [g, one_smul, zero_smul, add_zero, slope_def_field, sub_zero, div_one] at hslope
    have hxd : x + d = y := by show x + (y - x) = y; abel
    rw [hxd] at hslope
    linarith

-- ============================================================================
-- Part 2: Strong convexity first-order condition
-- ============================================================================

/-- First-order condition for strongly convex functions (multivariate, Hilbert space).

Layer: 0 | Gap: Level 1 (result absent from Mathlib for Hilbert spaces)
Technique: reduce to convex FOC via `strongConvexOn_iff_convex` (h = f − μ/2·‖·‖²),
  compute ∇h via `hasStrictFDerivAt_norm_sq`, apply `convex_first_order_condition`,
  recover result via norm algebraic identity.
Proof steps:
  [L0: strongConvexOn_iff_convex]
  [L3: gradient of h: hasStrictFDerivAt_norm_sq + CLM form matching via convert+simp]
  [dep: convex_first_order_condition applied to h]
  [L0: norm_sub_sq_real + inner_sub_right + linarith]
Used in: `strong_convex_inner_lower_bound`

If `f : E → ℝ` is `μ`-strongly convex and has gradient `gradF` everywhere, then
`f(y) ≥ f(x) + ⟪∇f(x), y − x⟫ + μ/2 · ‖y − x‖²`. -/
theorem strong_convex_first_order_condition
    {f : E → ℝ} {gradF : E → E} {μ : ℝ}
    (hsc : StrongConvexOn univ μ f)
    (hgrad : ∀ w, HasGradientAt f (gradF w) w)
    (x y : E) :
    f x + ⟪gradF x, y - x⟫_ℝ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  set h := fun w : E => f w - μ / 2 * ‖w‖ ^ 2
  have hh_conv : ConvexOn ℝ univ h := strongConvexOn_iff_convex.mp hsc
  have hh_grad : ∀ w, HasGradientAt h (gradF w - μ • w) w := by
    intro w
    rw [hasGradientAt_iff_hasFDerivAt]
    have hf := (hgrad w).hasFDerivAt
    have hnorm : HasFDerivAt (fun v => μ / 2 * ‖v‖ ^ 2) (μ • innerSL ℝ w) w := by
      have h1 := (hasStrictFDerivAt_norm_sq w).hasFDerivAt.const_smul (μ / 2)
      have h2 : (μ / 2) • (2 • innerSL ℝ w : E →L[ℝ] ℝ) = μ • innerSL ℝ w := by
        ext v
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul,
                    innerSL_apply_apply, two_nsmul, ContinuousLinearMap.add_apply]
        ring
      rw [h2] at h1; exact h1
    have hsub := hf.sub hnorm
    convert hsub using 1
    ext v
    simp [InnerProductSpace.toDual_apply_apply]
  have hh_foc := convex_first_order_condition hh_conv hh_grad x y
  simp only [h, inner_sub_left, inner_smul_left, RCLike.conj_to_real] at hh_foc
  have hnorm := norm_sub_sq_real y x
  have hinner : ⟪x, y - x⟫_ℝ = ⟪x, y⟫_ℝ - ⟪x, x⟫_ℝ := inner_sub_right x y x
  have hself := real_inner_self_eq_norm_sq x
  have hcomm := real_inner_comm x y
  have key : μ * ⟪x, y - x⟫_ℝ =
      μ / 2 * ‖y‖ ^ 2 - μ / 2 * ‖y - x‖ ^ 2 - μ / 2 * ‖x‖ ^ 2 := by
    rw [hinner, hself, hnorm, hcomm]; ring
  linarith

-- ============================================================================
-- Part 3: Corollaries for minimizers
-- ============================================================================

/-- Convex lower bound on inner product with gradient at a minimizer.

Layer: 0 | Gap: Level 1 corollary
Proof steps: [dep: convex_first_order_condition at (w, wStar)] [L0: inner_neg_right + linarith]
Used in: `one_step_progress_convex` (Algorithms/SGD.lean, Step 4)

For a convex function, `⟪∇f(w), w − w*⟫ ≥ f(w) − f(w*)`. -/
theorem convex_inner_lower_bound
    {f : E → ℝ} {gradF : E → E}
    (hconv : ConvexOn ℝ univ f)
    (hgrad : ∀ w, HasGradientAt f (gradF w) w)
    (w wStar : E) :
    f w - f wStar ≤ ⟪gradF w, w - wStar⟫_ℝ := by
  have h := convex_first_order_condition hconv hgrad w wStar
  rw [show wStar - w = -(w - wStar) from by abel, inner_neg_right] at h
  linarith

/-- Strong convex lower bound on inner product with gradient at a minimizer.

Layer: 0 | Gap: Level 1 corollary
Proof steps: [dep: strong_convex_first_order_condition at (w, wStar)] [L0: norm_neg + linarith]
Used in: `one_step_progress_sc` (Algorithms/SGD.lean, Step 4) — produces contraction factor (1−ημ)

For a μ-strongly convex function with minimizer `w*`:
`⟪∇f(w), w − w*⟫ ≥ μ/2 · ‖w − w*‖²`. -/
theorem strong_convex_inner_lower_bound
    {f : E → ℝ} {gradF : E → E} {μ : ℝ} {wStar : E}
    (hsc : StrongConvexOn univ μ f)
    (hgrad : ∀ w, HasGradientAt f (gradF w) w)
    (hmin : ∀ w, f wStar ≤ f w)
    (w : E) :
    μ / 2 * ‖w - wStar‖ ^ 2 ≤ ⟪gradF w, w - wStar⟫_ℝ := by
  have h := strong_convex_first_order_condition hsc hgrad w wStar
  rw [show wStar - w = -(w - wStar) from by abel, inner_neg_right,
      show ‖-(w - wStar)‖ = ‖w - wStar‖ from norm_neg _] at h
  linarith [hmin w]

/-- Gradient norm bound under strong convexity + smoothness: ‖∇f(w)‖ ≤ L‖w − w*‖.
Layer: 0 | Gap: Level 3 (direct consequence of Lipschitz gradient + Fermat)
Used in: SVRG outer loop convergence (Algorithms/SVRGOuterLoop.lean, Step 3 — variance conversion) -/
theorem strongly_convex_gradient_norm_bound
    {f : E → ℝ} {gradF : E → E} {L : NNReal} {wStar : E}
    (hsmooth : LipschitzWith L gradF)
    (hmin : ∀ w, f wStar ≤ f w)
    (hgrad : ∀ w, HasGradientAt f (gradF w) w)
    (w : E) :
    ‖gradF w‖ ≤ (L : ℝ) * ‖w - wStar‖ := by
  have h_grad_wStar : gradF wStar = 0 := by
    -- Global minimizer → local minimizer: f wStar ≤ f y holds for all y,
    -- so it holds eventually in any filter, in particular 𝓝 wStar.
    have hloc : IsLocalMin f wStar := Filter.Eventually.of_forall hmin
    -- Fermat: fderiv at local minimizer is zero
    have hzero : innerSL ℝ (gradF wStar) = 0 :=
      hloc.hasFDerivAt_eq_zero (hgrad wStar).hasFDerivAt
    -- innerSL v = 0 as CLM ⟹ ⟪v, v⟫ = 0 ⟹ v = 0
    have hself : ⟪gradF wStar, gradF wStar⟫_ℝ = 0 := by
      have := congr_fun (congrArg DFunLike.coe hzero) (gradF wStar)
      simpa [innerSL_apply] using this
    exact inner_self_eq_zero.mp hself
  calc ‖gradF w‖ = ‖gradF w - gradF wStar‖ := by rw [h_grad_wStar, sub_zero]
    _ ≤ (L : ℝ) * ‖w - wStar‖ := by
        have h := hsmooth.dist_le_mul w wStar
        rwa [dist_eq_norm, dist_eq_norm] at h
