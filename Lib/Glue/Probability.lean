import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Probability and Integrability Infrastructure (Glue)

Layer: Glue (general-purpose probability and integrability tools)

This file provides integrability lemmas that bridge the gap between Mathlib's
pointwise measure-theoretic infrastructure and the composed integrability
conditions required by stochastic optimization proofs.

## Main results

* `integrable_inner_of_sq_integrable` — inner product integrability from L² bounds
* `integrable_norm_sq_of_bounded_var` — ‖gradL(wt,ξt)‖² integrability from bounded variance

## Gap taxonomy

All gaps here are Level 2 (composition missing):
- Mathlib has Cauchy-Schwarz, AM-GM, `Integrable.mono`, but not the composed
  "inner product of two L²-integrable random vectors" pattern.
- Mathlib has Fubini + independence + integral_map, but not the composed
  "bounded variance implies finite second moment under joint distribution" pattern.
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {S : Type*} [MeasurableSpace S]
variable {Ω : Type*} [MeasurableSpace Ω]

-- ============================================================================
-- Lemma 1: Inner product integrability from squared norm integrability
-- ============================================================================

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- If `‖u‖²` and `‖v‖²` are both integrable, then `⟪u, v⟫` is integrable.

Layer: Glue | Gap: Level 2 (composition missing)
Proof: By Cauchy-Schwarz, `|⟪u,v⟫| ≤ ‖u‖·‖v‖`. By AM-GM, `‖u‖·‖v‖ ≤ (‖u‖²+‖v‖²)/2`.
The dominating function `(‖u‖²+‖v‖²)/2` is integrable, so apply `Integrable.mono`.
Closes: `h_int_inner` and `h_int_gF_inner` sorrys (via specialization). -/
theorem integrable_inner_of_sq_integrable
    {P : Measure Ω}
    {u v : Ω → E}
    (hu_meas : AEStronglyMeasurable u P) (hv_meas : AEStronglyMeasurable v P)
    (hu_sq : Integrable (fun ω => ‖u ω‖ ^ 2) P)
    (hv_sq : Integrable (fun ω => ‖v ω‖ ^ 2) P) :
    Integrable (fun ω => ⟪u ω, v ω⟫_ℝ) P := by
  apply Integrable.mono (hu_sq.add hv_sq) (hu_meas.inner hv_meas)
  refine Filter.Eventually.of_forall fun ω => ?_
  rw [Real.norm_eq_abs]
  calc |⟪u ω, v ω⟫_ℝ|
      ≤ ‖u ω‖ * ‖v ω‖ := abs_real_inner_le_norm (u ω) (v ω)
    _ ≤ ‖u ω‖ ^ 2 + ‖v ω‖ ^ 2 := by nlinarith [sq_nonneg (‖u ω‖ - ‖v ω‖)]
    _ = ‖(fun ω => ‖u ω‖ ^ 2 + ‖v ω‖ ^ 2) ω‖ := by
        simp [Real.norm_eq_abs, abs_of_nonneg (by positivity : ‖u ω‖ ^ 2 + ‖v ω‖ ^ 2 ≥ 0)]

-- ============================================================================
-- Lemma 2: Squared norm of stochastic gradient is integrable (from bounded variance)
-- ============================================================================

/-- If `E_ν[‖gradL(w,·)‖²] ≤ σ²` for all w (with pointwise integrability),
and `wt ⊥ ξt` with `map(ξt)P = ν`, then `‖gradL(wt(ω), ξt(ω))‖²` is
integrable w.r.t. P.

Layer: Glue | Gap: Level 2 (Fubini + independence + change-of-variables)
Proof strategy:
  1. Independence → joint distribution = product measure
  2. `integrable_map_measure` → reduce to product measure integrability
  3. `integrable_prod_iff` → split into inner + outer conditions
  4. Inner: pointwise integrability from `hvar_int`
  5. Outer: bounded function on probability space from `hvar_bound`

Design note: The signature takes separate `hvar_int` and `hvar_bound`
arguments (rather than importing `HasBoundedVariance'`) to avoid circular
module dependencies. Callers with `HasBoundedVariance'` pass `.1` and `.2`. -/
theorem integrable_norm_sq_of_bounded_var
    {gradL : E → S → E} {σ : ℝ}
    {P : Measure Ω} {ν : Measure S} [IsProbabilityMeasure P] [IsProbabilityMeasure ν]
    {wt : Ω → E} {ξt : Ω → S}
    (hgL : Measurable (Function.uncurry gradL))
    (hmeas_wt : Measurable wt) (hmeas_ξt : Measurable ξt)
    (h_indep : IndepFun wt ξt P)
    (h_dist : Measure.map ξt P = ν)
    (hvar_int : ∀ w, Integrable (fun s => ‖gradL w s‖ ^ 2) ν)
    (hvar_bound : ∀ w, ∫ s, ‖gradL w s‖ ^ 2 ∂ν ≤ σ ^ 2) :
    Integrable (fun ω => ‖gradL (wt ω) (ξt ω)‖ ^ 2) P := by
  have h_joint_meas : AEMeasurable (fun ω => (wt ω, ξt ω)) P :=
    (hmeas_wt.prodMk hmeas_ξt).aemeasurable
  have h_f_meas : Measurable (fun p : E × S => ‖gradL p.1 p.2‖ ^ 2) :=
    hgL.norm.pow_const 2
  have h_prod_eq : P.map (fun ω => (wt ω, ξt ω)) = (P.map wt).prod ν := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hmeas_wt.aemeasurable
        hmeas_ξt.aemeasurable).mp h_indep, h_dist]
  haveI : IsProbabilityMeasure (P.map wt) :=
    Measure.isProbabilityMeasure_map hmeas_wt.aemeasurable
  suffices h_prod :
      Integrable (fun p : E × S => ‖gradL p.1 p.2‖ ^ 2) ((P.map wt).prod ν) by
    have h_on_map : Integrable (fun p : E × S => ‖gradL p.1 p.2‖ ^ 2)
        (P.map (fun ω => (wt ω, ξt ω))) := h_prod_eq ▸ h_prod
    exact (integrable_map_measure h_f_meas.aestronglyMeasurable h_joint_meas).mp h_on_map
  rw [integrable_prod_iff h_f_meas.aestronglyMeasurable]
  exact ⟨
    Filter.Eventually.of_forall fun w => hvar_int w,
    Integrable.mono (integrable_const (σ ^ 2))
      (h_f_meas.norm.aestronglyMeasurable.integral_prod_right)
      (Filter.Eventually.of_forall fun w => by
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _),
            abs_of_nonneg (sq_nonneg σ)]
        exact (integral_mono (hvar_int w).norm (integrable_const _)
          fun s => by simp [Real.norm_eq_abs, abs_of_nonneg (by positivity)]).trans
          (hvar_bound w))
  ⟩
