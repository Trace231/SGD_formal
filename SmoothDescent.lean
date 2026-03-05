import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Data.NNReal.Defs

/-!
# L-Smooth Descent Infrastructure

Missing Mathlib infrastructure for SGD convergence proofs:

1. `integral_inner_gradient_segment`: Fundamental theorem of calculus along a line segment
   for functions `f : E → ℝ` with known gradient, expressed as an inner product integral.

2. `lipschitz_gradient_quadratic_bound`: The classical L-smooth quadratic upper bound:
   if `∇f` is `L`-Lipschitz, then `f(y) ≤ f(x) + ⟪∇f(x), y - x⟫ + L/2 · ‖y - x‖²`.
-/

open MeasureTheory Set NNReal
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- ============================================================================
-- Part 1: Composing HasGradientAt with a line segment
-- ============================================================================

/-- If `f : E → ℝ` has gradient `gradF w` at every `w`, then the composition
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

/-- **Fundamental theorem of calculus along a line segment (gradient form).**

If `f : E → ℝ` has gradient `gradF w` at every `w`, and `gradF` is continuous, then
`f(x + d) - f(x) = ∫ t in 0..1, ⟪gradF(x + t • d), d⟫`.

This is the key infrastructure lemma missing from Mathlib. -/
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

/-- Variant: `f(y) - f(x) = ∫ t in 0..1, ⟪gradF(x + t • (y - x)), y - x⟫`. -/
theorem integral_inner_gradient_segment'
    {f : E → ℝ} {gradF : E → E}
    (hgrad : ∀ w, HasGradientAt f (gradF w) w)
    (hcont : Continuous gradF)
    (x y : E) :
    ∫ t in (0 : ℝ)..1, ⟪gradF (x + t • (y - x)), y - x⟫_ℝ = f y - f x := by
  rw [integral_inner_gradient_segment hgrad hcont x (y - x)]
  congr 1; abel

-- ============================================================================
-- Part 3: L-smooth quadratic upper bound
-- ============================================================================

omit [CompleteSpace E] in
private theorem inner_gradient_diff_le
    {gradF : E → E} {L : ℝ≥0}
    (hlip : LipschitzWith L gradF)
    (x d : E) {t : ℝ} (ht : 0 ≤ t) :
    ⟪gradF (x + t • d) - gradF x, d⟫_ℝ ≤ (L : ℝ) * t * ‖d‖ ^ 2 := by
  calc ⟪gradF (x + t • d) - gradF x, d⟫_ℝ
      ≤ ‖gradF (x + t • d) - gradF x‖ * ‖d‖ := real_inner_le_norm _ _
    _ ≤ (L : ℝ) * ‖(x + t • d) - x‖ * ‖d‖ := by
        gcongr
        have := hlip.dist_le_mul (x + t • d) x
        rwa [dist_eq_norm, dist_eq_norm] at this
    _ = (L : ℝ) * t * ‖d‖ ^ 2 := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht]; ring

private theorem integral_id_zero_one : ∫ x in (0 : ℝ)..1, id x = (1 : ℝ) / 2 := by
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

/-- **L-smooth quadratic upper bound.**

If `∇f` is `L`-Lipschitz (i.e., `f` is L-smooth), then for all `x, d`:
`f(x + d) ≤ f(x) + ⟪∇f(x), d⟫ + L/2 · ‖d‖²`. -/
theorem lipschitz_gradient_quadratic_bound
    {f : E → ℝ} {gradF : E → E} {L : ℝ≥0}
    (hgrad : ∀ w, HasGradientAt f (gradF w) w)
    (hcont : Continuous gradF)
    (hlip : LipschitzWith L gradF)
    (x d : E) :
    f (x + d) ≤ f x + ⟪gradF x, d⟫_ℝ + (L : ℝ) / 2 * ‖d‖ ^ 2 := by
  have key := integral_inner_gradient_segment hgrad hcont x d
  rw [eq_comm, sub_eq_iff_eq_add] at key
  rw [key]
  suffices h : ∫ t in (0 : ℝ)..1, ⟪gradF (x + t • d), d⟫_ℝ ≤
      ⟪gradF x, d⟫_ℝ + (L : ℝ) / 2 * ‖d‖ ^ 2 by linarith
  have hsplit : ∀ t : ℝ, ⟪gradF (x + t • d), d⟫_ℝ =
      ⟪gradF x, d⟫_ℝ + ⟪gradF (x + t • d) - gradF x, d⟫_ℝ := by
    intro t; rw [← inner_add_left, add_sub_cancel]
  simp_rw [hsplit]
  have hcont_remainder : Continuous (fun t : ℝ => ⟪gradF (x + t • d) - gradF x, d⟫_ℝ) :=
    Continuous.inner
      ((hcont.comp (continuous_const.add
        ((continuous_id : Continuous (id : ℝ → ℝ)).smul continuous_const))).sub continuous_const)
      continuous_const
  rw [intervalIntegral.integral_add intervalIntegrable_const
    (hcont_remainder.intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul]
  gcongr
  have hcont_bound : Continuous (fun t : ℝ => (L : ℝ) * t * ‖d‖ ^ 2) :=
    (continuous_const.mul (continuous_id : Continuous (id : ℝ → ℝ))).mul continuous_const
  calc ∫ t in (0 : ℝ)..1, ⟪gradF (x + t • d) - gradF x, d⟫_ℝ
      ≤ ∫ t in (0 : ℝ)..1, (L : ℝ) * t * ‖d‖ ^ 2 := by
        apply intervalIntegral.integral_mono_on zero_le_one
          (hcont_remainder.intervalIntegrable _ _) (hcont_bound.intervalIntegrable _ _)
        intro t ht
        simp only [mem_Icc] at ht
        exact inner_gradient_diff_le hlip x d ht.1
    _ = (L : ℝ) / 2 * ‖d‖ ^ 2 := by
        have hrw : (fun t : ℝ => (L : ℝ) * t * ‖d‖ ^ 2) =
            (fun t : ℝ => (L : ℝ) * ‖d‖ ^ 2 * t) := by ext t; ring
        rw [hrw, show (fun t : ℝ => (↑L : ℝ) * ‖d‖ ^ 2 * t) =
            (fun t : ℝ => ((↑L : ℝ) * ‖d‖ ^ 2) * (id t)) from by ext; simp [id]]
        rw [intervalIntegral.integral_const_mul, integral_id_zero_one]; ring

/-- **L-smooth quadratic upper bound (point-to-point form).**

`f(y) ≤ f(x) + ⟪∇f(x), y - x⟫ + L/2 · ‖y - x‖²` -/
theorem lipschitz_gradient_quadratic_bound'
    {f : E → ℝ} {gradF : E → E} {L : ℝ≥0}
    (hgrad : ∀ w, HasGradientAt f (gradF w) w)
    (hcont : Continuous gradF)
    (hlip : LipschitzWith L gradF)
    (x y : E) :
    f y ≤ f x + ⟪gradF x, y - x⟫_ℝ + (L : ℝ) / 2 * ‖y - x‖ ^ 2 := by
  have h := lipschitz_gradient_quadratic_bound hgrad hcont hlip x (y - x)
  rwa [add_sub_cancel] at h
