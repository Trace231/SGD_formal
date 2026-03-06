import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Hilbert-Space Calculus Primitives (Glue Infrastructure)

Layer: Glue (pure math patches; no optimization or stochastic content)

These lemmas address the gap between Mathlib's scalar calculus and the Hilbert-space
gradient forms needed in stochastic optimization proofs.

Gap type: Level 3 (form mismatch) throughout — Mathlib has scalar FTC and chain rules,
but not their Hilbert-gradient specializations.

Exported:
1. `hasDerivAt_comp_lineSegment` — derivative of `f ∘ line_segment` as inner product.
2. `integral_inner_gradient_segment` — Hilbert-space FTC along a line segment.
3. `integral_inner_gradient_segment'` — point-to-point variant of (2).
4. `integral_id_zero_one` — `∫₀¹ t dt = 1/2` (needed for the L-smooth bound).

Used by: `Lib.Layer0.GradientFTC`, `Lib.Layer0.ConvexFOC`.
-/

open MeasureTheory Set NNReal
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- ============================================================================
-- Part 1: Derivative of f composed with a line segment
-- ============================================================================

/-- Derivative of f composed with a line segment parametrization.

Layer: Glue | Gap: Level 3 (form mismatch)
Technique: gradient-to-derivative bridge via `InnerProductSpace.toDual_apply_apply`
Proof steps: [L0: hasFDerivAt] [L0: hasDerivAt chain rule] [L3: toDual rewrite]
Used in: `integral_inner_gradient_segment`, `convex_first_order_condition`

If `f : E → ℝ` has gradient `gradF w` at every `w`, then the composition
`φ(t) = f(x + t • d)` has derivative `⟪gradF(x + t • d), d⟫` at every `t ∈ ℝ`. -/
theorem hasDerivAt_comp_lineSegment
    {f : E → ℝ} {gradF : E → E}
    (hgrad : ∀ w, HasGradientAt f (gradF w) w)
    (x d : E) (t : ℝ) :
    HasDerivAt (fun t => f (x + t • d)) (⟪gradF (x + t • d), d⟫_ℝ) t := by
  have hfderiv := (hgrad (x + t • d)).hasFDerivAt
  have hline : HasDerivAt (fun s => x + s • d) ((1 : ℝ) • d) t := by
    exact (hasDerivAt_id t).smul_const d |>.const_add x
  have hcomp := hfderiv.comp_hasDerivAt t (hline.congr_deriv (one_smul _ _))
  simp only [Function.comp_def] at hcomp
  rwa [InnerProductSpace.toDual_apply_apply] at hcomp

-- ============================================================================
-- Part 2: FTC along a segment (gradient form)
-- ============================================================================

/-- Fundamental theorem of calculus along a line segment (gradient form).

Layer: Glue | Gap: Level 3 (form mismatch)
Technique: reduce to scalar FTC via `hasDerivAt_comp_lineSegment`
Proof steps: [dep: hasDerivAt_comp_lineSegment] [L3: continuity of inner product composition]
             [L0: intervalIntegral.integral_eq_sub_of_hasDerivAt]
Used in: `lipschitz_gradient_quadratic_bound`, `convex_first_order_condition`

If `f : E → ℝ` has gradient `gradF w` at every `w`, and `gradF` is continuous, then
`f(x + d) - f(x) = ∫ t in 0..1, ⟪gradF(x + t • d), d⟫`. -/
theorem integral_inner_gradient_segment
    {f : E → ℝ} {gradF : E → E}
    (hgrad : ∀ w, HasGradientAt f (gradF w) w)
    (hcont : Continuous gradF)
    (x d : E) :
    ∫ t in (0 : ℝ)..1, ⟪gradF (x + t • d), d⟫_ℝ = f (x + d) - f x := by
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t => f (x + t • d)) (⟪gradF (x + t • d), d⟫_ℝ) t :=
    fun t _ => hasDerivAt_comp_lineSegment hgrad x d t
  have hcont_inner : Continuous (fun t : ℝ => ⟪gradF (x + t • d), d⟫_ℝ) :=
    Continuous.inner
      (hcont.comp (continuous_const.add ((continuous_id : Continuous (id : ℝ → ℝ)).smul continuous_const)))
      continuous_const
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hcont_inner.continuousOn.intervalIntegrable]
  simp only [one_smul, zero_smul, add_zero]

/-- Variant: `f(y) - f(x) = ∫ t in 0..1, ⟪gradF(x + t • (y - x)), y - x⟫`.

Layer: Glue | Gap: Level 3 (form mismatch) -/
theorem integral_inner_gradient_segment'
    {f : E → ℝ} {gradF : E → E}
    (hgrad : ∀ w, HasGradientAt f (gradF w) w)
    (hcont : Continuous gradF)
    (x y : E) :
    ∫ t in (0 : ℝ)..1, ⟪gradF (x + t • (y - x)), y - x⟫_ℝ = f y - f x := by
  rw [integral_inner_gradient_segment hgrad hcont x (y - x)]
  congr 1; abel

-- ============================================================================
-- Part 3: ∫₀¹ t dt = 1/2
-- ============================================================================

/-- `∫ t in 0..1, id t = 1/2`.

Layer: Glue | Gap: Level 3 (scalar FTC applied to `t ↦ t`)
Used in: `lipschitz_gradient_quadratic_bound` (final step of the L-smooth bound). -/
theorem integral_id_zero_one : ∫ x in (0 : ℝ)..1, id x = (1 : ℝ) / 2 := by
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s => s ^ 2 / 2) (id t) t := by
    intro t _
    show HasDerivAt (fun s => s ^ 2 / 2) t t
    have h1 : HasDerivAt (fun s => s ^ 2) (↑2 * t ^ (2 - 1)) t := hasDerivAt_pow 2 t
    have h2 := h1.div_const (2 : ℝ)
    convert h2 using 1; simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (continuous_id.continuousOn.intervalIntegrable)]
  norm_num
