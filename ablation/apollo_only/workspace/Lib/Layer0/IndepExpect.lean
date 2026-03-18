import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Independence and Expectation Infrastructure (Layer 0 Infrastructure)

Layer: 0 (pure probability/measure theory tools, no optimization content)

Mathlib has `IndepFun`, `integral_prod` (Fubini), and `integral_map`, but lacks a
practical composition that says "when X ⊥ Y, E_P[f(X,Y)] = E_X[E_Y[f(x,Y)]]"
in a form usable for stochastic optimization proofs.

This file provides the two key "take expectation" lemmas needed for SGD convergence:
1. `expectation_norm_sq_gradL_bound`: bounded variance transfer from ν to P.
   Gap type: Level 2 (composition of IndepFun + Fubini + integral_mono).
2. `expectation_inner_gradL_eq`: unbiased cross-term identity.
   Gap type: Level 2 (same chain + `integral_inner` to extract the direction vector).

Both proofs follow the same pattern:
  integral_map → IndepFun → product measure → integral_prod (Fubini)
  → pointwise property → integral_map back

Triggered by: all three SGD convergence theorems (non-convex, convex, strongly convex).
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {S : Type*} [MeasurableSpace S]
variable {Ω : Type*} [MeasurableSpace Ω]

-- ============================================================================
-- Part 1: Bounded variance transfer
-- ============================================================================

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
/-- Bounded variance transfer from sample distribution ν to probability space P.

Layer: 0 | Gap: Level 2 (composition missing)
Technique: IndepFun → product measure (indepFun_iff_map_prod_eq_prod_map_map) →
  Fubini (integral_prod) → pointwise hvar → integral_const
Proof steps:
  [L2: h_prod_eq via indepFun_iff_map_prod_eq_prod_map_map + h_dist]
  [L2: h_int_prod via integrable_map_measure + rwa h_prod_eq]
  [L0: integral_map (change of variables)]
  [L0: integral_prod (Fubini)]
  [L2: integral_mono + hvar pointwise]
  [L3: integral_const + probReal_univ]
Used in: `stochastic_descent_nonconvex`, `one_step_progress_convex`,
  `one_step_progress_sc` (Algorithms/SGD.lean, Step 5 — bounded variance step)

If `E_ν[‖gradL w s‖²] ≤ σ²` for all `w`, and `wt ⊥ ξt` with `map(ξt)P = ν`, then
`E_P[‖gradL(wt, ξt)‖²] ≤ σ²`. -/
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
  have h_joint_meas : AEMeasurable (fun ω => (wt ω, ξt ω)) P :=
    (h_wt_meas.prodMk h_ξt_meas).aemeasurable
  have h_f_meas : Measurable (fun p : E × S => ‖gradL p.1 p.2‖ ^ 2) :=
    hgL.norm.pow_const 2
  have h_prod_eq : P.map (fun ω => (wt ω, ξt ω)) = (P.map wt).prod ν := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map h_wt_meas.aemeasurable
        h_ξt_meas.aemeasurable).mp h_indep, h_dist]
  haveI h_prob_ν : IsProbabilityMeasure ν :=
    h_dist ▸ Measure.isProbabilityMeasure_map h_ξt_meas.aemeasurable
  have h_int_prod : Integrable (fun p : E × S => ‖gradL p.1 p.2‖ ^ 2) ((P.map wt).prod ν) := by
    have h1 : Integrable (fun p : E × S => ‖gradL p.1 p.2‖ ^ 2)
        (P.map (fun ω => (wt ω, ξt ω))) :=
      (integrable_map_measure h_f_meas.aestronglyMeasurable h_joint_meas).mpr h_int
    rwa [h_prod_eq] at h1
  haveI h_prob_wt : IsProbabilityMeasure (P.map wt) :=
    Measure.isProbabilityMeasure_map h_wt_meas.aemeasurable
  calc ∫ ω, ‖gradL (wt ω) (ξt ω)‖ ^ 2 ∂P
      = ∫ p : E × S, ‖gradL p.1 p.2‖ ^ 2 ∂P.map (fun ω => (wt ω, ξt ω)) :=
          (integral_map h_joint_meas h_f_meas.aestronglyMeasurable).symm
    _ = ∫ p : E × S, ‖gradL p.1 p.2‖ ^ 2 ∂(P.map wt).prod ν := by rw [h_prod_eq]
    _ = ∫ w : E, ∫ s : S, ‖gradL w s‖ ^ 2 ∂ν ∂P.map wt := integral_prod _ h_int_prod
    _ ≤ ∫ _ : E, σ ^ 2 ∂P.map wt := by
          apply integral_mono h_int_prod.integral_prod_left (integrable_const _)
          intro w; exact hvar w
    _ = σ ^ 2 := by simp [integral_const, probReal_univ]

-- ============================================================================
-- Part 2: Unbiased cross-term identity
-- ============================================================================

/-- Unbiased cross-term identity: replace stochastic gradient with true gradient in expectation.

Layer: 0 | Gap: Level 2 (composition missing)
Technique: same IndepFun → product measure → Fubini chain as Part 1, with the
  key extra step `integral_inner` to extract the direction h(w) from the inner product
  integral, then apply unbiasedness `hunb`.
Proof steps:
  [L2: same h_prod_eq, h_int_prod setup as expectation_norm_sq_gradL_bound]
  [L0: integral_map (LHS to product measure)]
  [L0: integral_prod (Fubini)]
  [L2: integral_inner (h_intL w) (h w) — pulls h(w) out of inner product integral]
  [L0: hunb w — unbiasedness replaces ∫ gradL with gradF]
  [L0: integral_map (RHS back to P)]
Design note: `h : E → E` is a free parameter, making this lemma reusable for
  both non-convex (h = gradF) and convex/strongly convex (h = fun w => w − wStar) cases.
Used in: `stochastic_descent_nonconvex`, `one_step_progress_convex`,
  `one_step_progress_sc` (Algorithms/SGD.lean, Step 4 — unbiasedness step)

For `wt ⊥ ξt` and `E_ν[gradL w ·] = gradF w`:
`E[⟪h(wt), gradL(wt, ξt)⟫] = E[⟪h(wt), gradF(wt)⟫]`. -/
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
  have h_joint_meas : AEMeasurable (fun ω => (wt ω, ξt ω)) P :=
    (h_wt_meas.prodMk h_ξt_meas).aemeasurable
  have h_inner_cont : Measurable (fun q : E × E => ⟪q.1, q.2⟫_ℝ) :=
    continuous_inner.measurable
  have h_f_meas : Measurable (fun p : E × S => ⟪h p.1, gradL p.1 p.2⟫_ℝ) :=
    h_inner_cont.comp ((hh_meas.comp measurable_fst).prodMk hgL)
  have h_prod_eq : P.map (fun ω => (wt ω, ξt ω)) = (P.map wt).prod ν := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map h_wt_meas.aemeasurable
        h_ξt_meas.aemeasurable).mp h_indep, h_dist]
  haveI h_prob_ν : IsProbabilityMeasure ν :=
    h_dist ▸ Measure.isProbabilityMeasure_map h_ξt_meas.aemeasurable
  have h_int_prod :
      Integrable (fun p : E × S => ⟪h p.1, gradL p.1 p.2⟫_ℝ) ((P.map wt).prod ν) := by
    have h1 : Integrable (fun p : E × S => ⟪h p.1, gradL p.1 p.2⟫_ℝ)
        (P.map (fun ω => (wt ω, ξt ω))) :=
      (integrable_map_measure h_f_meas.aestronglyMeasurable h_joint_meas).mpr h_int
    rwa [h_prod_eq] at h1
  haveI : IsProbabilityMeasure (P.map wt) :=
    Measure.isProbabilityMeasure_map h_wt_meas.aemeasurable
  have lhs_eq : ∫ ω, ⟪h (wt ω), gradL (wt ω) (ξt ω)⟫_ℝ ∂P =
      ∫ w : E, ⟪h w, gradF w⟫_ℝ ∂P.map wt := by
    rw [show ∫ ω, ⟪h (wt ω), gradL (wt ω) (ξt ω)⟫_ℝ ∂P =
        ∫ p : E × S, ⟪h p.1, gradL p.1 p.2⟫_ℝ ∂P.map (fun ω => (wt ω, ξt ω)) from
          (integral_map h_joint_meas h_f_meas.aestronglyMeasurable).symm,
      h_prod_eq, integral_prod _ h_int_prod]
    congr 1; ext w
    rw [integral_inner (h_intL w) (h w), hunb w]
  have rhs_eq : ∫ ω, ⟪h (wt ω), gradF (wt ω)⟫_ℝ ∂P =
      ∫ w : E, ⟪h w, gradF w⟫_ℝ ∂P.map wt := by
    have h_rhs_meas : Measurable (fun w : E => ⟪h w, gradF w⟫_ℝ) :=
      h_inner_cont.comp (hh_meas.prodMk hgF_meas)
    exact (integral_map h_wt_meas.aemeasurable h_rhs_meas.aestronglyMeasurable).symm
  rw [lhs_eq, rhs_eq]
