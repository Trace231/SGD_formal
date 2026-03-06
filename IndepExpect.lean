import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Independence and Expectation Infrastructure for SGD

Key measure-theoretic lemmas connecting independence structure of SGD
with expectation calculations needed for convergence proofs.

## Main results

* `expectation_norm_sq_gradL_bound` — Bounded variance transfer from ν to P
* `expectation_inner_gradL_eq` — The "unbiased cross-term" identity

These formalize the "take expectation" step in textbook SGD proofs.
Both proofs use the chain:
  integral_map → IndepFun→product measure → integral_prod (Fubini) → pointwise bound/unbiasedness
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {S : Type*} [MeasurableSpace S]
variable {Ω : Type*} [MeasurableSpace Ω]

-- ============================================================================
-- Phase 1: Bounded variance transfer
-- ============================================================================

/-- **Bounded variance transfer**: E_P[‖∇L(wₜ, ξₜ)‖²] ≤ σ².

If `E_ν[‖∇L(w, s)‖²] ≤ σ²` for all `w`, then by independence of `wt` and `ξt`,
Fubini, and the pushforward distribution, `E_P[‖∇L(wₜ, ξₜ)‖²] ≤ σ²`.

Proof chain: integral_map → IndepFun→product measure → integral_prod → hvar → integral_const. -/
theorem expectation_norm_sq_gradL_bound
    {gradL : E → S → E} {σ : ℝ}
    {P : Measure Ω} {ν : Measure S} [IsProbabilityMeasure P]
    {wt : Ω → E} {ξt : Ω → S}
    (hvar : ∀ w, ∫ s, ‖gradL w s‖ ^ 2 ∂ν ≤ σ ^ 2)
    (h_indep : IndepFun wt ξt P)
    (h_dist : Measure.map ξt P = ν)
    (h_wt_meas : Measurable wt)
    (h_ξt_meas : Measurable ξt)
    (hgL : Measurable (Function.uncurry gradL))
    (h_int : Integrable (fun ω => ‖gradL (wt ω) (ξt ω)‖ ^ 2) P) :
    ∫ ω, ‖gradL (wt ω) (ξt ω)‖ ^ 2 ∂P ≤ σ ^ 2 := by
  -- Auxiliary facts
  have h_joint_meas : AEMeasurable (fun ω => (wt ω, ξt ω)) P :=
    (h_wt_meas.prodMk h_ξt_meas).aemeasurable
  have h_f_meas : Measurable (fun p : E × S => ‖gradL p.1 p.2‖ ^ 2) :=
    hgL.norm.pow_const 2
  -- Independence gives product measure equality
  have h_prod_eq : P.map (fun ω => (wt ω, ξt ω)) = (P.map wt).prod ν := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map h_wt_meas.aemeasurable
        h_ξt_meas.aemeasurable).mp h_indep, h_dist]
  -- ν is a probability measure (pushforward of P)
  haveI h_prob_ν : IsProbabilityMeasure ν :=
    h_dist ▸ Measure.isProbabilityMeasure_map h_ξt_meas.aemeasurable
  -- Integrability w.r.t. product measure
  have h_int_prod : Integrable (fun p : E × S => ‖gradL p.1 p.2‖ ^ 2) ((P.map wt).prod ν) := by
    have h1 : Integrable (fun p : E × S => ‖gradL p.1 p.2‖ ^ 2)
        (P.map (fun ω => (wt ω, ξt ω))) :=
      (integrable_map_measure h_f_meas.aestronglyMeasurable h_joint_meas).mpr h_int
    rwa [h_prod_eq] at h1
  -- P.map wt is a probability measure
  haveI h_prob_wt : IsProbabilityMeasure (P.map wt) :=
    Measure.isProbabilityMeasure_map h_wt_meas.aemeasurable
  -- Main calculation
  calc ∫ ω, ‖gradL (wt ω) (ξt ω)‖ ^ 2 ∂P
      = ∫ p : E × S, ‖gradL p.1 p.2‖ ^ 2 ∂P.map (fun ω => (wt ω, ξt ω)) :=
          (integral_map h_joint_meas h_f_meas.aestronglyMeasurable).symm
    _ = ∫ p : E × S, ‖gradL p.1 p.2‖ ^ 2 ∂(P.map wt).prod ν := by
          rw [h_prod_eq]
    _ = ∫ w : E, ∫ s : S, ‖gradL w s‖ ^ 2 ∂ν ∂P.map wt :=
          integral_prod _ h_int_prod
    _ ≤ ∫ _ : E, σ ^ 2 ∂P.map wt := by
          apply integral_mono h_int_prod.integral_prod_left (integrable_const _)
          intro w; exact hvar w
    _ = σ ^ 2 := by
          simp [integral_const, probReal_univ]

-- ============================================================================
-- Phase 2b: Unbiased cross-term identity
-- ============================================================================

/-- **Unbiased cross-term identity**.

For `wₜ` independent of `ξₜ` with `E_ν[∇L(w,·)] = ∇f(w)`:
`E[⟪h(wₜ), ∇L(wₜ, ξₜ)⟫] = E[⟪h(wₜ), ∇f(wₜ)⟫]`

Proof: integral_map → IndepFun→product measure → Bochner Fubini →
       integral_inner (pull h(w) out) → unbiasedness → integral_map back. -/
theorem expectation_inner_gradL_eq
    {gradL : E → S → E} {gradF : E → E}
    {P : Measure Ω} {ν : Measure S} [IsProbabilityMeasure P]
    {wt : Ω → E} {ξt : Ω → S}
    (hunb : ∀ w, ∫ s, gradL w s ∂ν = gradF w)
    (h_indep : IndepFun wt ξt P)
    (h_dist : Measure.map ξt P = ν)
    (h : E → E)
    (h_wt_meas : Measurable wt)
    (h_ξt_meas : Measurable ξt)
    (hgL : Measurable (Function.uncurry gradL))
    (hh_meas : Measurable h)
    (hgF_meas : Measurable gradF)
    (h_intL : ∀ w, Integrable (gradL w) ν)
    (h_int : Integrable (fun ω => ⟪h (wt ω), gradL (wt ω) (ξt ω)⟫_ℝ) P) :
    ∫ ω, ⟪h (wt ω), gradL (wt ω) (ξt ω)⟫_ℝ ∂P =
      ∫ ω, ⟪h (wt ω), gradF (wt ω)⟫_ℝ ∂P := by
  -- Auxiliary facts
  have h_joint_meas : AEMeasurable (fun ω => (wt ω, ξt ω)) P :=
    (h_wt_meas.prodMk h_ξt_meas).aemeasurable
  -- Measurability of the inner product integrand (w,s) ↦ ⟪h w, gradL w s⟫
  -- Use: ⟪·,·⟫ is continuous, and h∘fst and uncurry gradL are measurable
  have h_inner_cont : Measurable (fun q : E × E => ⟪q.1, q.2⟫_ℝ) :=
    continuous_inner.measurable
  have h_f_meas : Measurable (fun p : E × S => ⟪h p.1, gradL p.1 p.2⟫_ℝ) :=
    h_inner_cont.comp ((hh_meas.comp measurable_fst).prodMk hgL)
  -- Independence gives product measure equality
  have h_prod_eq : P.map (fun ω => (wt ω, ξt ω)) = (P.map wt).prod ν := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map h_wt_meas.aemeasurable
        h_ξt_meas.aemeasurable).mp h_indep, h_dist]
  -- ν is a probability measure (pushforward of P)
  haveI h_prob_ν : IsProbabilityMeasure ν :=
    h_dist ▸ Measure.isProbabilityMeasure_map h_ξt_meas.aemeasurable
  -- Integrability of inner product w.r.t. product measure
  have h_int_prod :
      Integrable (fun p : E × S => ⟪h p.1, gradL p.1 p.2⟫_ℝ) ((P.map wt).prod ν) := by
    have h1 : Integrable (fun p : E × S => ⟪h p.1, gradL p.1 p.2⟫_ℝ)
        (P.map (fun ω => (wt ω, ξt ω))) :=
      (integrable_map_measure h_f_meas.aestronglyMeasurable h_joint_meas).mpr h_int
    rwa [h_prod_eq] at h1
  -- P.map wt is a probability measure
  haveI : IsProbabilityMeasure (P.map wt) :=
    Measure.isProbabilityMeasure_map h_wt_meas.aemeasurable
  -- LHS rewritten via product measure and Fubini, then simplified
  have lhs_eq : ∫ ω, ⟪h (wt ω), gradL (wt ω) (ξt ω)⟫_ℝ ∂P =
      ∫ w : E, ⟪h w, gradF w⟫_ℝ ∂P.map wt := by
    rw [show ∫ ω, ⟪h (wt ω), gradL (wt ω) (ξt ω)⟫_ℝ ∂P =
        ∫ p : E × S, ⟪h p.1, gradL p.1 p.2⟫_ℝ ∂P.map (fun ω => (wt ω, ξt ω)) from
          (integral_map h_joint_meas h_f_meas.aestronglyMeasurable).symm,
      h_prod_eq, integral_prod _ h_int_prod]
    -- After Fubini: ∫ w, (∫ s, ⟪h w, gradL w s⟫ ∂ν) ∂(P.map wt)
    -- Use integral_inner to pull h(w) out, then unbiasedness
    congr 1; ext w
    rw [integral_inner (h_intL w) (h w), hunb w]
  -- RHS rewritten via integral_map
  have rhs_eq : ∫ ω, ⟪h (wt ω), gradF (wt ω)⟫_ℝ ∂P =
      ∫ w : E, ⟪h w, gradF w⟫_ℝ ∂P.map wt := by
    have h_rhs_meas : Measurable (fun w : E => ⟪h w, gradF w⟫_ℝ) :=
      h_inner_cont.comp (hh_meas.prodMk hgF_meas)
    exact (integral_map h_wt_meas.aemeasurable h_rhs_meas.aestronglyMeasurable).symm
  rw [lhs_eq, rhs_eq]
