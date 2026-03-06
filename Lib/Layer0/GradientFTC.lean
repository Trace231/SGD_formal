import Lib.Glue.Calculus
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Data.NNReal.Defs

/-!
# Gradient FTC and L-Smooth Quadratic Bound (Layer 0 Infrastructure)

Layer: 0 (pure math tools, no stochastic content)

This file provides the L-smooth quadratic upper bound, building on the Hilbert-space
FTC primitives in `Lib.Glue.Calculus`.

`lipschitz_gradient_quadratic_bound`: The classical L-smooth quadratic upper bound.
Gap type: Level 2+3 composite (FTC composition + Lipschitz integral estimate).
The FTC reduction steps live in `Lib.Glue.Calculus`; this file handles only the
Lipschitz integral estimate layer.

Triggered by: `descent_lemma'` in `Lib.Layer1.StochasticDescent`.
-/

open MeasureTheory Set NNReal
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- ============================================================================
-- Private helpers for the Lipschitz integral estimate
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

-- ============================================================================
-- L-smooth quadratic upper bound
-- ============================================================================

/-- L-smooth quadratic upper bound.

Layer: 0 | Gap: Level 2+3 composite
Technique: FTC (Lib.Glue.Calculus) + Cauchy-Schwarz + Lipschitz integral estimate
Proof steps: [dep: integral_inner_gradient_segment (Lib.Glue.Calculus)]
             [L0: inner_add_left split]
             [L0: integral_add]
             [L2: real_inner_le_norm + LipschitzWith.dist_le_mul]
             [dep: integral_id_zero_one (Lib.Glue.Calculus)]
Used in: `descent_lemma'` (Lib.Layer1.StochasticDescent)

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
        rw [hrw, show (fun t : ℝ => ((↑L : ℝ) * ‖d‖ ^ 2) * t) =
            (fun t : ℝ => ((↑L : ℝ) * ‖d‖ ^ 2) * (id t)) from by ext; simp [id]]
        rw [intervalIntegral.integral_const_mul, integral_id_zero_one]; ring

/-- L-smooth quadratic upper bound (point-to-point form).

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
