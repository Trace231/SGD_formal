import Algorithms.SVRG
import Mathlib.Algebra.Field.GeomSum

/-!
# SVRG Outer Loop — Epoch-Level Convergence Analysis

Layer: 2 (concrete algorithm proofs built on inner-loop analysis)

This file formalizes the macro-level SVRG dynamics across K epochs, where each
epoch runs m inner steps with a fixed snapshot, then updates the snapshot to
the epoch endpoint.

## Mathematical structure

**Update rule (outer loop):**
$$w_{k+1} = \text{svrgProcess}(w_k, \eta, w_k, \nabla F(w_k), \xi_{\text{epoch}}(k), m)$$

**Proof chain:**
1. Inner epoch contraction (from `svrg_convergence_inner_strongly_convex`)
2. Variance reduction bound (from `svrg_variance_reduction`)
3. Gradient norm → distance conversion (from `strongly_convex_gradient_norm_bound`)
4. Telescope over K epochs → geometric series closed form

## Archetype: B

The outer loop has a novel two-level structure:
- **Inner epoch**: Archetype A (reduces to plain SGD via `effectiveSGDSetup`)
- **Outer loop**: Archetype B (snapshot update creates iterate-dependent variance)

This requires **dual integrability** per GLUE_TRICKS.md Section 4b.
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

-- ============================================================================
-- Type parameters (file-level context)
-- ============================================================================

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {S : Type*} [MeasurableSpace S]
variable {Ω : Type*} [MeasurableSpace Ω]

-- ============================================================================
-- Section 1: SVRG Outer Loop Setup Structure
-- ============================================================================

/-- SVRG outer-loop setup: extends inner-loop setup with epoch-level sampling.

Used in: `SVRG outer loop` (Algorithms/SVRGOuterLoop.lean, structure definition) -/
structure SVRGOuterSetup
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E]
    (S : Type*) [MeasurableSpace S]
    (Ω : Type*) [MeasurableSpace Ω] where
  toSVRGSetup : SVRGSetup E S Ω
  m : ℕ
  hm_pos : 0 < m
  -- Epoch-level sampling: ξ_epoch(k, j, ω) for epoch k, inner step j
  epochStream : ℕ → ℕ → Ω → S
  h_epoch_meas : ∀ k j, Measurable (epochStream k j)
  -- Independence across epochs (each epoch's sample stream is independent)
  h_epoch_indep : ∀ k₁ k₂, k₁ ≠ k₂ →
    ∀ j₁ j₂, IndepFun (epochStream k₁ j₁) (epochStream k₂ j₂) toSVRGSetup.toSGDSetup.P
  -- Identical distribution within and across epochs
  h_epoch_ident : ∀ k j, IdentDistrib (epochStream k j) (toSVRGSetup.toSGDSetup.ξ 0)
    toSVRGSetup.toSGDSetup.P toSVRGSetup.toSGDSetup.P

namespace SVRGOuterSetup

/-- Epoch-indexed iterate: `outerProcess k ω` is the snapshot at epoch k.

Used in: `SVRG outer loop` (Algorithms/SVRGOuterLoop.lean, epoch iterate definition) -/
noncomputable def outerProcess (setup : SVRGOuterSetup E S Ω) : ℕ → Ω → E
  | 0, ω => setup.toSVRGSetup.toSGDSetup.w₀
  | k + 1, ω =>
      let w_k := outerProcess setup k ω
      let gradF_wk := setup.toSVRGSetup.toSGDSetup.gradF w_k
      setup.toSVRGSetup.svrgProcess w_k gradF_wk setup.m ω

omit [SecondCountableTopology E] in
@[simp] theorem outerProcess_zero (setup : SVRGOuterSetup E S Ω) :
    outerProcess setup 0 = fun _ => setup.toSVRGSetup.toSGDSetup.w₀ := rfl

omit [SecondCountableTopology E] in
@[simp] theorem outerProcess_succ (setup : SVRGOuterSetup E S Ω) (k : ℕ) :
    outerProcess setup (k + 1) = fun ω =>
      setup.toSVRGSetup.svrgProcess (outerProcess setup k ω)
        (setup.toSVRGSetup.toSGDSetup.gradF (outerProcess setup k ω))
        setup.m ω := rfl

-- ============================================================================
-- Section 2: Measurability and Independence Infrastructure
-- ============================================================================

/-- Measurability of epoch iterates.

Used in: `SVRG outer loop` (Algorithms/SVRGOuterLoop.lean, Step 4 — measurability bridge) -/
theorem outerProcess_measurable
    (setup : SVRGOuterSetup E S Ω)
    (hgL : Measurable (Function.uncurry setup.toSVRGSetup.toSGDSetup.gradL))
    (hgF : Measurable setup.toSVRGSetup.toSGDSetup.gradF) (k : ℕ) :
    Measurable (outerProcess setup k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
      have h_wk_meas : Measurable (outerProcess setup k) := ih
      have h_gradF_wk_meas : Measurable (fun ω => setup.toSVRGSetup.toSGDSetup.gradF (outerProcess setup k ω)) :=
        hgF.comp h_wk_meas
      -- BRIDGE LEMMA NEEDED: svrgProcess_measurable_random_snapshot
      sorry

/-- Independence of epoch k iterate from epoch k samples.

Used in: `SVRG outer loop` (Algorithms/SVRGOuterLoop.lean, Step 4 — independence bridge) -/
theorem outerProcess_indepFun_epoch
    (setup : SVRGOuterSetup E S Ω)
    (hgL : Measurable (Function.uncurry setup.toSVRGSetup.toSGDSetup.gradL))
    (hgF : Measurable setup.toSVRGSetup.toSGDSetup.gradF) (k : ℕ) :
    ∀ j, IndepFun (outerProcess setup k) (setup.epochStream k j) setup.toSVRGSetup.toSGDSetup.P := by
  intro j
  sorry

-- ============================================================================
-- Section 3: Epoch Contraction Factor
-- ============================================================================

/-- Epoch contraction factor: ρ = (1-ημ)^m + η·(variance terms)/μ.

Used in: `SVRG outer loop` (Algorithms/SVRGOuterLoop.lean, contraction factor definition) -/
noncomputable def epochContractionFactor (η μ : ℝ) (L : NNReal) (m : ℕ) : ℝ :=
  (1 - η * μ) ^ m + η * (4 * (L : ℝ) ^ 2 / μ + 2 * (L : ℝ) ^ 2) / μ

-- ============================================================================
-- Section 4: Main Outer-Loop Convergence Theorem
-- ============================================================================

/-- SVRG outer-loop convergence: epoch-to-epoch contraction telescoped over K epochs.

Used in: `SVRG outer loop` (Algorithms/SVRGOuterLoop.lean, Step 6 — main convergence theorem) -/
theorem svrg_outer_convergence
    (setup : SVRGOuterSetup E S Ω) (f : E → ℝ) {L : NNReal} {μ σ η : ℝ} (wStar : E)
    (hgrad : IsGradientOf f setup.toSVRGSetup.toSGDSetup.gradF)
    (hsmooth : IsLSmooth setup.toSVRGSetup.toSGDSetup.gradF L)
    (hsc : StrongConvexOn Set.univ μ f)
    (hvar : HasBoundedVariance setup.toSVRGSetup.toSGDSetup.gradL setup.toSVRGSetup.sampleDist σ)
    (hunb : IsUnbiased setup.toSVRGSetup.toSGDSetup.gradL setup.toSVRGSetup.toSGDSetup.gradF setup.toSVRGSetup.sampleDist)
    (hmin : IsMinimizer f wStar)
    (h_sample_prob : IsProbabilityMeasure setup.toSVRGSetup.sampleDist)
    (hμ_pos : 0 < μ) (hη_pos : 0 < η) (hη_L : η ≤ 1 / (2 * (L : ℝ)))
    (hημ : η * μ < 1)
    (K : ℕ) (hK_pos : 0 < K)
    (hgL : Measurable (Function.uncurry setup.toSVRGSetup.toSGDSetup.gradL))
    (hgF : Measurable setup.toSVRGSetup.toSGDSetup.gradF)
    (h_intL : ∀ w, Integrable (setup.toSVRGSetup.toSGDSetup.gradL w) setup.toSVRGSetup.sampleDist)
    (h_int_epoch_end : ∀ k, Integrable (fun ω => ‖outerProcess setup k ω - wStar‖ ^ 2)
      setup.toSVRGSetup.toSGDSetup.P)
    (h_int_snapshot : ∀ k, Integrable (fun ω =>
      ‖setup.toSVRGSetup.svrgProcess (outerProcess setup k ω)
        (setup.toSVRGSetup.toSGDSetup.gradF (outerProcess setup k ω))
        setup.m ω - wStar‖ ^ 2) setup.toSVRGSetup.toSGDSetup.P) :
    ∫ ω, ‖outerProcess setup K ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.toSGDSetup.P ≤
      (epochContractionFactor η μ L setup.m) ^ K * ‖setup.toSVRGSetup.toSGDSetup.w₀ - wStar‖ ^ 2 := by
  haveI := setup.toSVRGSetup.toSGDSetup.hP
  set ρ := epochContractionFactor η μ L setup.m with hρ_def
  
  have h_epoch_contract : ∀ k < K,
      ∫ ω, ‖outerProcess setup (k + 1) ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.toSGDSetup.P ≤
        ρ * ∫ ω, ‖outerProcess setup k ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.toSGDSetup.P := by
    intro k hk
    sorry
  
  have h_telescope :
      ∫ ω, ‖outerProcess setup K ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.toSGDSetup.P ≤
        ρ ^ K * ‖setup.toSVRGSetup.toSGDSetup.w₀ - wStar‖ ^ 2 := by
    induction K with
    | zero =>
      simp only [outerProcess_zero setup, pow_zero, one_mul]
      rw [integral_const, smul_eq_mul, probReal_univ, one_mul]
    | succ K ih =>
        have h_contract := h_epoch_contract K (Nat.lt_succ_self K)
        calc ∫ ω, ‖outerProcess setup (K + 1) ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.toSGDSetup.P
            ≤ ρ * ∫ ω, ‖outerProcess setup K ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.toSGDSetup.P := h_contract
          _ ≤ ρ * (ρ ^ K * ‖setup.toSVRGSetup.toSGDSetup.w₀ - wStar‖ ^ 2) := by
              gcongr
          _ = ρ ^ (K + 1) * ‖setup.toSVRGSetup.toSGDSetup.w₀ - wStar‖ ^ 2 := by
              ring
  
  exact h_telescope

end SVRGOuterSetup
