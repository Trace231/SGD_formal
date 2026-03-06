import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.NNReal.Defs
import Lib.Glue.Probability

/-!
# Measurability and Integrability Infrastructure (Glue)

Layer: Glue (measure-theoretic tools for stochastic optimization)

This file provides measurability and integrability lemmas that bridge the gap
between Mathlib's infrastructure and the specific compositions needed in SGD
convergence proofs.

## Main results

* `measurable_of_lsmooth` — Lipschitz → measurable (proved)
* `integrable_lsmooth_comp_measurable` — Lipschitz composition preserves integrability (proved)
* `integrable_norm_sq_gradL_comp` — squared gradient norm is integrable (delegates to Probability.lean)
* `integrable_inner_gradL_comp` — inner product with gradient is integrable (proved)
* `integrable_norm_sq_iterate_comp` — squared distance to optimum is integrable (proved)
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {S : Type*} [MeasurableSpace S]
variable {Ω : Type*} [MeasurableSpace Ω]

-- ============================================================================
-- 1. Measurability of gradF from L-smoothness
-- ============================================================================

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
/-- A Lipschitz (L-smooth) function is measurable.

Layer: Glue | Gap: Level 2 (LipschitzWith → Continuous → Measurable chain)
Closes: `by sorry` for `Measurable setup.gradF` in `sgd_to_hyps` (Algorithms/SGD.lean) -/
theorem measurable_of_lsmooth {gradF : E → E} {L : NNReal}
    (hsmooth : LipschitzWith L gradF) : Measurable gradF :=
  hsmooth.continuous.measurable

-- ============================================================================
-- 2. Integrability of Lipschitz function composed with integrable random variable
-- ============================================================================

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
/-- If `f` is Lipschitz and `wt` is integrable, then `f ∘ wt` is integrable
(on a finite measure space).

Layer: Glue | Gap: Level 2 (composition missing)
Proof: Lipschitz gives linear growth `|f(x)| ≤ |f(0)| + K·‖x‖`. The RHS is integrable
  from `integrable_const` (finite measure) + `Integrable.norm.const_mul`.
Closes: `h_int_ft` and `h_int_ft1` in convergence theorems (Algorithms/SGD.lean) -/
theorem integrable_lsmooth_comp_measurable
    {f : E → ℝ} {K : NNReal} {P : Measure Ω} [IsFiniteMeasure P] {wt : Ω → E}
    (hlip : LipschitzWith K f) (hmeas : Measurable wt) (hint : Integrable wt P) :
    Integrable (fun ω => f (wt ω)) P := by
  have hf_meas : AEStronglyMeasurable (fun ω => f (wt ω)) P :=
    (hlip.continuous.measurable.comp hmeas).aestronglyMeasurable
  have h_dom : Integrable (fun ω => ‖f 0‖ + (K : ℝ) * ‖wt ω‖) P :=
    (integrable_const ‖f 0‖).add (hint.norm.const_mul (K : ℝ))
  apply Integrable.mono h_dom hf_meas
  refine Filter.Eventually.of_forall fun ω => ?_
  have h_lip := hlip.dist_le_mul (wt ω) 0
  rw [Real.dist_eq, dist_zero_right] at h_lip
  calc ‖f (wt ω)‖
      = ‖(f (wt ω) - f 0) + f 0‖ := by ring_nf
    _ ≤ ‖f (wt ω) - f 0‖ + ‖f 0‖ := norm_add_le _ _
    _ ≤ (K : ℝ) * ‖wt ω‖ + ‖f 0‖ := by rw [Real.norm_eq_abs]; linarith
    _ = ‖f 0‖ + (K : ℝ) * ‖wt ω‖ := by ring
    _ ≤ ‖‖f 0‖ + (K : ℝ) * ‖wt ω‖‖ := Real.le_norm_self _

-- ============================================================================
-- 3. Integrability of ‖gradL(wt, ξt)‖²
-- ============================================================================

/-- The squared norm of the stochastic gradient is integrable.

Layer: Glue | Gap: Level 2 (Fubini + independence chain)
Delegates to `integrable_norm_sq_of_bounded_var` from `Lib.Glue.Probability`.
Closes: `h_int_sq` sorry in all three convergence theorems (Algorithms/SGD.lean) -/
theorem integrable_norm_sq_gradL_comp
    {gradL : E → S → E} {σ : ℝ}
    {P : Measure Ω} {ν : Measure S} [IsProbabilityMeasure P] [IsProbabilityMeasure ν]
    {wt : Ω → E} {ξt : Ω → S}
    (hgL : Measurable (Function.uncurry gradL))
    (hmeas_wt : Measurable wt) (hmeas_ξt : Measurable ξt)
    (h_indep : IndepFun wt ξt P) (h_dist : Measure.map ξt P = ν)
    (hvar_int : ∀ w, Integrable (fun s => ‖gradL w s‖ ^ 2) ν)
    (hvar_bound : ∀ w, ∫ s, ‖gradL w s‖ ^ 2 ∂ν ≤ σ ^ 2) :
    Integrable (fun ω => ‖gradL (wt ω) (ξt ω)‖ ^ 2) P :=
  integrable_norm_sq_of_bounded_var hgL hmeas_wt hmeas_ξt h_indep h_dist hvar_int hvar_bound

-- ============================================================================
-- 4. Integrability of inner product ⟪h(wt), gradL(wt, ξt)⟫
-- ============================================================================

omit [CompleteSpace E] in
/-- The inner product of a measurable vector field with the stochastic gradient is integrable.

Layer: Glue | Gap: Level 2 (composition missing)
Proof: Both `h ∘ wt` and `gradL(wt, ξt)` have integrable squared norms, so
  `integrable_inner_of_sq_integrable` (from Probability.lean) applies.
Closes: `h_int_inner` sorry in all three convergence theorems (Algorithms/SGD.lean) -/
theorem integrable_inner_gradL_comp
    {gradL : E → S → E} {h : E → E}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {wt : Ω → E} {ξt : Ω → S}
    (hgL : Measurable (Function.uncurry gradL))
    (hh_meas : Measurable h) (hmeas_wt : Measurable wt) (hmeas_ξt : Measurable ξt)
    (hint_h_sq : Integrable (fun ω => ‖h (wt ω)‖ ^ 2) P)
    (hint_sq : Integrable (fun ω => ‖gradL (wt ω) (ξt ω)‖ ^ 2) P) :
    Integrable (fun ω => ⟪h (wt ω), gradL (wt ω) (ξt ω)⟫_ℝ) P :=
  integrable_inner_of_sq_integrable
    ((hh_meas.comp hmeas_wt).aestronglyMeasurable)
    ((hgL.comp (hmeas_wt.prodMk hmeas_ξt)).aestronglyMeasurable)
    hint_h_sq hint_sq

-- ============================================================================
-- 5. Integrability of ‖wt − w*‖²
-- ============================================================================

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E] in
/-- The squared distance of an L²-integrable random variable from a constant is integrable.

Layer: Glue | Gap: Level 2 (composition missing)
Proof: `‖wt − c‖² ≤ 2·‖wt‖² + 2·‖c‖²` (parallelogram bound), and both terms are
  integrable (the squared norm by hypothesis, the constant on a finite measure space).
Closes: `h_int_norm_sq` sorry in convex and strongly convex convergence theorems -/
theorem integrable_norm_sq_iterate_comp
    {P : Measure Ω} [IsFiniteMeasure P] {wt : Ω → E} {wStar : E}
    (hmeas : AEStronglyMeasurable wt P)
    (hint_sq : Integrable (fun ω => ‖wt ω‖ ^ 2) P) :
    Integrable (fun ω => ‖wt ω - wStar‖ ^ 2) P := by
  have h_dom : Integrable (fun ω => 2 * ‖wt ω‖ ^ 2 + 2 * ‖wStar‖ ^ 2) P :=
    (hint_sq.const_mul 2).add (integrable_const (2 * ‖wStar‖ ^ 2))
  have h_norm_meas : AEStronglyMeasurable (fun ω => ‖wt ω - wStar‖) P :=
    (hmeas.sub aestronglyMeasurable_const).norm
  have h_meas : AEStronglyMeasurable (fun ω => ‖wt ω - wStar‖ ^ 2) P := by
    have := h_norm_meas.mul h_norm_meas
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    show ‖wt ω - wStar‖ * ‖wt ω - wStar‖ = ‖wt ω - wStar‖ ^ 2
    ring
  apply Integrable.mono h_dom h_meas
  refine Filter.Eventually.of_forall fun ω => ?_
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]
  rw [abs_of_nonneg (by positivity)]
  have h1 : ‖wt ω - wStar‖ ≤ ‖wt ω‖ + ‖wStar‖ := norm_sub_le (wt ω) wStar
  have h1_sq : ‖wt ω - wStar‖ ^ 2 ≤ (‖wt ω‖ + ‖wStar‖) ^ 2 :=
    sq_le_sq' (by linarith [norm_nonneg (wt ω - wStar)]) h1
  nlinarith [sq_nonneg (‖wt ω‖ - ‖wStar‖)]
