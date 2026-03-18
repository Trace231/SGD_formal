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

ARCHITECTURAL INVARIANT: This file MUST NOT import any file under `Lib/Layer1/`.
All return types must use expanded forms rather than Layer 1 predicates such as
`HasBoundedVariance'`. See `hasBoundedVariance_of_pointwise_bound` for the
established pattern (expanded ∀ w, Integrable ∧ ∫ ≤ G²).

## Main results

* `integrable_inner_of_sq_integrable` — inner product integrability from L² bounds
* `integrable_norm_sq_of_bounded_var` — ‖gradL(wt,ξt)‖² integrability from bounded variance
* `integrable_sq_norm_of_pointwise_bound` — L² integrability + Bochner bound from pointwise norm bound (atomic, any NormedAddCommGroup)
* `hasBoundedVariance_of_pointwise_bound` — bounded-variance wrapper for optimization-vocabulary callers
* `svrg_variance_reduction` — SVRG variance-reduction inequality (finite-sum / uniform-sampling form)

## Gap taxonomy

All gaps here are Level 2 (composition missing):
- Mathlib has Cauchy-Schwarz, AM-GM, `Integrable.mono`, but not the composed
  "inner product of two L²-integrable random vectors" pattern.
- Mathlib has Fubini + independence + integral_map, but not the composed
  "bounded variance implies finite second moment under joint distribution" pattern.
- Mathlib has `Integrable.mono` + `integral_mono` + `integral_const`, but not the
  composed "pointwise constant bound implies L²-integrability and Bochner bound" pattern.
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
      ((h_f_meas.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable)
      (Filter.Eventually.of_forall fun w => by
        have h_eq :
            (∫ y, ‖‖gradL (w, y).1 (w, y).2‖ ^ 2‖ ∂ν) = ∫ s, ‖gradL w s‖ ^ 2 ∂ν := by
          refine integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro y
          have hnorm : ‖‖gradL w y‖ ^ 2‖ = ‖gradL w y‖ ^ 2 := by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖gradL w y‖)]
          simp [hnorm]
        have h_nonneg : 0 ≤ ∫ y, ‖‖gradL (w, y).1 (w, y).2‖ ^ 2‖ ∂ν := by
          refine integral_nonneg ?_
          intro y
          positivity
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h_nonneg, abs_of_nonneg (sq_nonneg σ), h_eq]
        exact hvar_bound w)
  ⟩




/-- If `f : S → β` is pointwise bounded by `G`, then `fun s => ‖f s‖ ^ 2` is
integrable and its Bochner integral is at most `G ^ 2`.

Layer: Glue | Gap: Level 2 (composition missing)
Technique: `Integrable.mono` with constant domination, `integral_mono`, `integral_const`,
`pow_le_pow_left₀`.

This is the atomic, optimization-vocabulary-free form. The only requirement on
`β` is `NormedAddCommGroup`. For the optimization-specific wrapper that speaks
in terms of a stochastic gradient oracle `gradL : E → S → E`, see
`hasBoundedVariance_of_pointwise_bound`. -/
theorem integrable_sq_norm_of_pointwise_bound
    {β : Type*} [NormedAddCommGroup β]
    {f : S → β} {G : ℝ} {ν : Measure S} [IsProbabilityMeasure ν]
    (hf_meas : AEStronglyMeasurable f ν)
    (hbounded : ∀ s, ‖f s‖ ≤ G) :
    Integrable (fun s => ‖f s‖ ^ 2) ν ∧ ∫ s, ‖f s‖ ^ 2 ∂ν ≤ G ^ 2 := by
  have hbound : ∀ s, ‖‖f s‖ ^ 2‖ ≤ ‖G ^ 2‖ := fun s => by
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (sq_nonneg G)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbounded s) 2
  have hint : Integrable (fun s => ‖f s‖ ^ 2) ν :=
    Integrable.mono (integrable_const (G ^ 2)) (hf_meas.norm.pow 2)
      (Filter.Eventually.of_forall hbound)
  constructor
  · exact hint
  · calc
      ∫ s, ‖f s‖ ^ 2 ∂ν
        ≤ ∫ s, G ^ 2 ∂ν := integral_mono hint (integrable_const _)
            (fun s => pow_le_pow_left₀ (norm_nonneg _) (hbounded s) 2)
      _ = G ^ 2 := by simp [integral_const, probReal_univ]

/-- From a uniform pointwise oracle bound `‖gradL w s‖ ≤ G`, derive the
bounded-variance property: for every `w`, `fun s => ‖gradL w s‖ ^ 2` is
integrable and its Bochner integral is at most `G ^ 2`.

This is a thin optimization-vocabulary wrapper over
`integrable_sq_norm_of_pointwise_bound`. The return type is intentionally kept
in expanded form (rather than `HasBoundedVariance' gradL ν G`) to avoid
importing `Lib.Layer1`, which would create a circular module dependency.
Callers holding `HasBoundedVariance' gradL ν G` can use this directly because
Lean unfolds the definition during type-checking.

Layer: Glue | Gap: Level 2 (composition missing)
Used in: `Subgradient convex convergence` (Algorithms/SubgradientMethod.lean, Step deriving hvar)
Used in: any algorithm with a uniformly bounded stochastic oracle (clipped SGD, etc.) -/
theorem hasBoundedVariance_of_pointwise_bound
    {gradL : E → S → E} {G : ℝ} {ν : Measure S} [IsProbabilityMeasure ν]
    (hgL_meas : Measurable (Function.uncurry gradL))
    (hbounded : ∀ w s, ‖gradL w s‖ ≤ G) :
    ∀ w, Integrable (fun s => ‖gradL w s‖ ^ 2) ν ∧ ∫ s, ‖gradL w s‖ ^ 2 ∂ν ≤ G ^ 2 :=
  fun w => integrable_sq_norm_of_pointwise_bound
    ((hgL_meas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (fun s => hbounded w s)

/-- SVRG variance-reduction inequality (finite-sum / uniform-sampling form).

This version is aligned with finite-sum SVRG assumptions:
* samples are drawn from a finite index set `S`,
* expectation under `ν` matches a uniform average over `S`,
* a per-sample bound on the SVRG oracle norm is available.

Used in: `SVRG inner-loop strongly-convex convergence`
(`Algorithms/SVRG.lean`, derivation of effective variance bound) -/
theorem svrg_variance_reduction
    {gradL : E → S → E} {gradF : E → E} {f : E → ℝ}
    {ν : Measure S} {L : NNReal} {wTilde wStar : E} {fStar : ℝ}
    [Fintype S] [Nonempty S]
    (h_unif : ∀ g : S → ℝ, Integrable g ν →
      ∫ s, g s ∂ν = (1 / (Fintype.card S : ℝ)) * ∑ s : S, g s)
    (h_int_oracle : ∀ w : E, Integrable
      (fun s => ‖gradL w s - gradL wTilde s + gradF wTilde‖ ^ 2) ν)
    (h_pointwise_oracle : ∀ s : S, ∀ w : E,
      ‖gradL w s - gradL wTilde s + gradF wTilde‖ ^ 2
        ≤ 4 * (L : ℝ) * (f w - fStar) + 2 * ‖gradF wTilde - gradF wStar‖ ^ 2) :
    ∀ w : E,
      ∫ s, ‖gradL w s - gradL wTilde s + gradF wTilde‖ ^ 2 ∂ν
        ≤ 4 * (L : ℝ) * (f w - fStar) + 2 * ‖gradF wTilde - gradF wStar‖ ^ 2 := by
  intro w
  have h_card_ne_zero : (Fintype.card S : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos_iff.mpr inferInstance))
  have h_avg :
      ∫ s, ‖gradL w s - gradL wTilde s + gradF wTilde‖ ^ 2 ∂ν =
        (1 / (Fintype.card S : ℝ)) *
          ∑ s : S, ‖gradL w s - gradL wTilde s + gradF wTilde‖ ^ 2 :=
    h_unif _ (h_int_oracle w)
  have h_sum_le :
      (∑ s : S, ‖gradL w s - gradL wTilde s + gradF wTilde‖ ^ 2)
        ≤ ∑ s : S, (4 * (L : ℝ) * (f w - fStar) + 2 * ‖gradF wTilde - gradF wStar‖ ^ 2) := by
    refine Finset.sum_le_sum ?_
    intro s _
    exact h_pointwise_oracle s w
  have h_oracle_var :
      ∫ s, ‖gradL w s - gradL wTilde s + gradF wTilde‖ ^ 2 ∂ν
        ≤ 4 * (L : ℝ) * (f w - fStar) + 2 * ‖gradF wTilde - gradF wStar‖ ^ 2 := by
    have h_sum_const :
        (∑ s : S, (4 * (L : ℝ) * (f w - fStar) + 2 * ‖gradF wTilde - gradF wStar‖ ^ 2)) =
          (Fintype.card S : ℝ) *
            (4 * (L : ℝ) * (f w - fStar) + 2 * ‖gradF wTilde - gradF wStar‖ ^ 2) := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring
    calc
      ∫ s, ‖gradL w s - gradL wTilde s + gradF wTilde‖ ^ 2 ∂ν
          = (1 / (Fintype.card S : ℝ)) *
              ∑ s : S, ‖gradL w s - gradL wTilde s + gradF wTilde‖ ^ 2 := h_avg
      _ ≤ (1 / (Fintype.card S : ℝ)) *
            ∑ s : S, (4 * (L : ℝ) * (f w - fStar) + 2 * ‖gradF wTilde - gradF wStar‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h_sum_le (by positivity)
      _ = (1 / (Fintype.card S : ℝ)) *
            ((Fintype.card S : ℝ) *
              (4 * (L : ℝ) * (f w - fStar) + 2 * ‖gradF wTilde - gradF wStar‖ ^ 2)) := by
            simp [h_sum_const]
      _ = ((1 / (Fintype.card S : ℝ)) * (Fintype.card S : ℝ)) *
            (4 * (L : ℝ) * (f w - fStar) + 2 * ‖gradF wTilde - gradF wStar‖ ^ 2) := by
            ring
      _ = 4 * (L : ℝ) * (f w - fStar) + 2 * ‖gradF wTilde - gradF wStar‖ ^ 2 := by
            field_simp [h_card_ne_zero]
  calc
    ∫ s, ‖gradL w s - gradL wTilde s + gradF wTilde‖ ^ 2 ∂ν
        ≤ 4 * (L : ℝ) * (f w - fStar) + 2 * ‖gradF wTilde - gradF wStar‖ ^ 2 := h_oracle_var
