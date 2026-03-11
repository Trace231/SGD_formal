import Algorithms.SVRG
import Lib.Glue.Probability
import Lib.Layer0.ConvexFOC
import Lib.Layer0.GradientFTC
import Main
import Lib.Glue.Staging.SVRGOuterLoop

/-!
# SVRG Outer-Loop Convergence (Strongly Convex Case)

Layer: 2 (concrete algorithm proof) | Archetype: B (multi-epoch composition ≠ single SGD step)

This file formalizes the outer-loop convergence of SVRG under finite-sum assumptions.
Critical innovations:
- Epoch-local inner-loop process parameterized by epoch-start state
- Dual integrability hypotheses for Archetype B pattern (GLUE_TRICKS §4b)
- Variance reduction integration via `svrg_variance_reduction` (finite-sum specific)
- Outer-loop contraction recurrence with explicit bias accumulation term

Design notes:
- `hvar` references BASE oracle `setup.toSGDSetup.gradL` (Convention 5 Resolution A)
- All new lemmas include Convention 4 `Used in:` tags
- Finite-sum assumption `[Fintype S] [Nonempty S]` required for `svrg_variance_reduction`
- Verification target: this file only (glue lemma `svrg_variance_reduction` assumed available per library state)
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {S : Type*} [MeasurableSpace S] [Fintype S] [Nonempty S]  -- Finite-sum requirement
variable {Ω : Type*} [MeasurableSpace Ω]

namespace SVRGSetup

variable (setup : SVRGSetup E S Ω)

/-- Outer-loop process: epoch-start states `w_k`. Each epoch runs `m` inner steps.
Used in: `SVRG outer-loop strongly convex convergence` (Algorithms/SVRGOuterLoop.lean, main recursion) -/
noncomputable def outerProcess (m : ℕ) : ℕ → Ω → E
  | 0 => fun _ => setup.toSGDSetup.w₀
  | k + 1 => fun ω =>
      let w_k := outerProcess m k ω
      let gradLTilde := setup.toSGDSetup.gradF w_k
      (sgdProcess w_k setup.toSGDSetup.η (setup.svrgOracle w_k gradLTilde)
        (fun t => setup.toSGDSetup.ξ (k * m + t)) m) ω

/-- Epoch contraction: E[‖w_{k+1}−w*‖²] ≤ ρ·E[‖w_k−w*‖²] + bias_term.
Core composition: inner-loop theorem + variance reduction + strong convexity bounds.
Used in: `SVRG outer-loop strongly convex convergence` (Algorithms/SVRGOuterLoop.lean, induction step) -/
theorem svrg_epoch_contraction (m : ℕ) (k : ℕ) {L : NNReal} {μ σ ρ η : ℝ} 
    [IsProbabilityMeasure setup.toSGDSetup.P]
    (hρ : ρ = (1 - η * μ) ^ m + 4 * η * (L : ℝ) ^ 2 / μ)
    (wStar : E) (f : E → ℝ) (hgrad : IsGradientOf f setup.toSGDSetup.gradF)
    (hsmooth : IsLSmooth setup.toSGDSetup.gradF L) (hsc : StrongConvexOn Set.univ μ f)
    (hvar : HasBoundedVariance setup.toSGDSetup.gradL setup.sampleDist σ)
    (hunb : IsUnbiased setup.toSGDSetup.gradL setup.toSGDSetup.gradF setup.sampleDist)
    (hmin : IsMinimizer f wStar) (hη_pos : 0 < η) (hημ : η * μ < 1)
    (hgL : Measurable (Function.uncurry setup.toSGDSetup.gradL))
    (h_intL_base : ∀ w, Integrable (setup.toSGDSetup.gradL w) setup.sampleDist)
    (h_int_norm_sq_k : Integrable (fun ω => ‖outerProcess m k ω - wStar‖ ^ 2) setup.toSGDSetup.P)
    (h_int_norm_sq_k1 : Integrable (fun ω => ‖outerProcess m (k + 1) ω - wStar‖ ^ 2) setup.toSGDSetup.P) :
    ∫ ω, ‖outerProcess m (k + 1) ω - wStar‖ ^ 2 ∂setup.toSGDSetup.P ≤
      ρ * ∫ ω, ‖outerProcess m k ω - wStar‖ ^ 2 ∂setup.toSGDSetup.P + 
      η * σ ^ 2 / μ := by
  -- Deferred: requires conditional expectation + svrg_variance_reduction composition
  -- This is the key Archetype B pattern: random snapshot w_k requires law of total expectation
  sorry

/-- **Outer-loop strongly convex convergence** (Archetype B).
Final rate matches standard SVRG analysis: linear contraction with variance accumulation term.
Used in: none (final algorithm theorem) -/
theorem svrg_convergence_outer_strongly_convex
    (setup : SVRGSetup E S Ω) (f : E → ℝ) {L : NNReal} {μ σ η : ℝ} (wStar : E)
    (m K : ℕ) (hm : 0 < m) (hK : 0 < K)
    (hgrad : IsGradientOf f setup.toSGDSetup.gradF)
    (hsmooth : IsLSmooth setup.toSGDSetup.gradF L)
    (hsc : StrongConvexOn Set.univ μ f)
    (hvar : HasBoundedVariance setup.toSGDSetup.gradL setup.sampleDist σ)  -- Base oracle only (Convention 5)
    (hunb : IsUnbiased setup.toSGDSetup.gradL setup.toSGDSetup.gradF setup.sampleDist)
    (hmin : IsMinimizer f wStar)
    (h_sample_prob : IsProbabilityMeasure setup.sampleDist)
    (hμ_pos : 0 < μ) (hη_pos : 0 < η) (hημ : η * μ < 1) (hη : ∀ t, setup.toSGDSetup.η t = η)
    (hgL : Measurable (Function.uncurry setup.toSGDSetup.gradL))
    (h_intL_base : ∀ w, Integrable (setup.toSGDSetup.gradL w) setup.sampleDist) :
    ∫ ω, ‖outerProcess m K ω - wStar‖ ^ 2 ∂setup.toSGDSetup.P ≤
      (1 - η * μ) ^ (m * K) * ‖setup.toSGDSetup.w₀ - wStar‖ ^ 2 + 
      η * σ ^ 2 / (μ * (1 - (1 - η * μ) ^ m)) := by
  haveI := setup.toSGDSetup.hP
  have hη_nonneg : 0 ≤ 1 - η * μ := by linarith
  -- Induction on K (number of epochs)
  induction K with
  | zero =>
      -- K = 0: outerProcess m 0 = w₀
      simp only [outerProcess]
      have h_init : ∫ ω, ‖(fun _ => setup.toSGDSetup.w₀) ω - wStar‖ ^ 2 ∂setup.toSGDSetup.P =
          ‖setup.toSGDSetup.w₀ - wStar‖ ^ 2 := by
        simp [integral_const, probReal_univ]
      rw [h_init]
      have h_nonneg : 0 ≤ η * σ ^ 2 / (μ * (1 - (1 - η * μ) ^ m)) := by
        apply div_nonneg
        · apply mul_nonneg; linarith; positivity
        · apply mul_nonneg; linarith [hμ_pos]
          have : (1 - η * μ) ^ m ≤ 1 := pow_le_one (by linarith) (by linarith [hημ])
          linarith
      linarith
  | succ K ih =>
      -- K + 1: apply epoch contraction + induction hypothesis
      set ρ := (1 - η * μ) ^ m + 4 * η * (L : ℝ) ^ 2 / μ with hρ_def
      have h_contr : ∫ ω, ‖outerProcess m (K + 1) ω - wStar‖ ^ 2 ∂setup.toSGDSetup.P ≤
          ρ * ∫ ω, ‖outerProcess m K ω - wStar‖ ^ 2 ∂setup.toSGDSetup.P + η * σ ^ 2 / μ := by
        -- Apply epoch contraction theorem (requires additional hypotheses)
        sorry
      -- Chain with induction hypothesis and simplify geometric series
      sorry

end SVRGSetup
