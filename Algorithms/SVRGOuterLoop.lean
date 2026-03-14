import Algorithms.SVRG
import Lib.Glue.Probability

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {S : Type*} [MeasurableSpace S]
variable {Ω : Type*} [MeasurableSpace Ω]

/-!
# SVRG Outer Loop — Epoch Telescoping Convergence Proofs

Layer: 2 (concrete algorithm proofs built on Layer 1 meta-theorems)

This file provides the outer-loop infrastructure for SVRG with random snapshot
updates (Archetype B). Unlike the inner loop (which reduces to plain SGD via
snapshot freeze), the outer loop requires explicit epoch telescoping because
the snapshot `wTilde` updates every `m` steps.

## Archetype Classification

- **Macro level (outer loop):** Archetype B — periodic snapshot updates every m steps
- **Micro level (inner epoch):** Archetype A — snapshot freeze reduces to plain SGD

## Main definitions

* `SVRGOuterSetup` — Extends `SVRGSetup` with epoch parameters `m` and `K`
* `svrgOuterProcess` — Recursive epoch iteration: `w_{k+1} = svrgProcess w_k (gradF w_k) m`
* `epoch_contraction_lemma` — One-epoch contraction bound
* `svrgOuter_convergence_strongly_convex` — Outer-loop convergence via epoch telescoping
-/

-- ============================================================================
-- Section 1: SVRGOuterSetup Structure
-- ============================================================================

/-- SVRG outer-loop setup: extends `SVRGSetup` with epoch parameters and gradient properties.

Used in: SVRG outer loop (Algorithms/SVRGOuterLoop.lean, main setup structure) -/
structure SVRGOuterSetup
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E]
    (S : Type*) [MeasurableSpace S]
    (Ω : Type*) [MeasurableSpace Ω] where
  toSVRGSetup : SVRGSetup E S Ω
  m : ℕ
  K : ℕ

namespace SVRGOuterSetup

variable (setup : SVRGOuterSetup E S Ω)
variable {L : NNReal} {μ σ σeff η : ℝ}

/-- Sample distribution inherited from the base setup.

Used in: SVRG outer loop (Algorithms/SVRGOuterLoop.lean, distribution access) -/
noncomputable def sampleDist : Measure S :=
  setup.toSVRGSetup.sampleDist

/-- SVRG outer-loop process: recursive epoch iteration.

Update rule: `w_{k+1} = svrgProcess w_k (gradF w_k) m`
where each epoch runs `m` inner steps with fixed snapshot `wTilde = w_k`.

Used in: SVRG outer loop (Algorithms/SVRGOuterLoop.lean, main iterate definition) -/
noncomputable def svrgOuterProcess (setup : SVRGOuterSetup E S Ω) : ℕ → Ω → E
  | 0 => fun _ => setup.toSVRGSetup.toSGDSetup.w₀
  | k + 1 =>
      fun ω =>
        let w_k := svrgOuterProcess setup k
        let gradFTilde := setup.toSVRGSetup.toSGDSetup.gradF (w_k ω)
        setup.toSVRGSetup.svrgProcess (w_k ω) gradFTilde setup.m ω

omit [SecondCountableTopology E] in
@[simp] theorem process_zero :
    svrgOuterProcess setup 0 = fun _ => setup.toSVRGSetup.toSGDSetup.w₀ := rfl

-- ============================================================================
-- Section 2: Measurability Infrastructure
-- ============================================================================

/-- Measurability of each outer-loop iterate.

Used in: SVRG outer loop (Algorithms/SVRGOuterLoop.lean, bridge construction — iterate measurability) -/
theorem svrgOuterProcess_measurable
    (hgL : Measurable (Function.uncurry setup.toSVRGSetup.toSGDSetup.gradL))
    (k : ℕ) :
    Measurable (svrgOuterProcess setup k) := by
  sorry

/-- Adaptedness of SVRG outer process to `sgdFiltration`.

Used in: SVRG outer loop (Algorithms/SVRGOuterLoop.lean, filtration argument) -/
theorem svrgOuterProcess_adapted
    (hgL : Measurable (Function.uncurry setup.toSVRGSetup.toSGDSetup.gradL)) :
    Adapted (sgdFiltration setup.toSVRGSetup.toSGDSetup.ξ setup.toSVRGSetup.toSGDSetup.hξ_meas)
      (fun k => svrgOuterProcess setup k) := by
  sorry

/-- Independence of `svrgOuterProcess k` and samples within epoch k.

Used in: SVRG outer loop (Algorithms/SVRGOuterLoop.lean, independence argument) -/
lemma svrgOuterProcess_indepFun_xi_epoch
    (hgL : Measurable (Function.uncurry setup.toSVRGSetup.toSGDSetup.gradL))
    (k : ℕ) :
    IndepFun (svrgOuterProcess setup k) (setup.toSVRGSetup.toSGDSetup.ξ (k * setup.m)) setup.toSVRGSetup.toSGDSetup.P := by
  sorry

-- ============================================================================
-- Section 3: Epoch Contraction Lemma
-- ============================================================================

/-- One-epoch contraction bound for SVRG outer loop.

For epoch k, with snapshot wTilde = w_k:
  E[‖w_{k+1} − w*‖²] ≤ (1 − ημ)^m · E[‖w_k − w*‖²] + η·σ_eff²/μ

where σ_eff² is bounded via variance reduction.

Used in: SVRG outer loop (Algorithms/SVRGOuterLoop.lean, svrgOuter_convergence_strongly_convex — epoch telescoping base) -/
theorem epoch_contraction_lemma
    (f : E → ℝ) (wStar : E)
    (hgrad : IsGradientOf f setup.toSVRGSetup.toSGDSetup.gradF)
    (hsmooth : IsLSmooth setup.toSVRGSetup.toSGDSetup.gradF L)
    (hsc : StrongConvexOn Set.univ μ f)
    (hvar_inner : HasBoundedVariance setup.toSVRGSetup.toSGDSetup.gradL setup.sampleDist σ)
    (hunb : IsUnbiased setup.toSVRGSetup.toSGDSetup.gradL setup.toSVRGSetup.toSGDSetup.gradF setup.sampleDist)
    (hmin : IsMinimizer f wStar)
    (hμ_pos : 0 < μ) (hη_pos : 0 < η) (hημ : η * μ < 1)
    (hη : ∀ t, setup.toSVRGSetup.toSGDSetup.η t = η)
    (k : ℕ) (hk : k < setup.K)
    (h_int_norm_sq : Integrable (fun ω => ‖svrgOuterProcess setup (k + 1) ω - wStar‖ ^ 2) setup.toSVRGSetup.toSGDSetup.P)
    (h_int_virtual : Integrable (fun ω => ‖setup.toSVRGSetup.svrgProcess (svrgOuterProcess setup k ω) (setup.toSVRGSetup.toSGDSetup.gradF (svrgOuterProcess setup k ω)) setup.m ω - wStar‖ ^ 2) setup.toSVRGSetup.toSGDSetup.P)
    (hσeff : σeff ^ 2 = 4 * (L : ℝ) * (∫ ω, f (svrgOuterProcess setup k ω) ∂setup.toSVRGSetup.toSGDSetup.P - f wStar) +
      2 * ‖setup.toSVRGSetup.toSGDSetup.gradF (svrgOuterProcess setup k ω) - setup.toSVRGSetup.toSGDSetup.gradF wStar‖ ^ 2) :
    ∫ ω, ‖svrgOuterProcess setup (k + 1) ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.toSGDSetup.P ≤
      (1 - η * μ) ^ setup.m * ∫ ω, ‖svrgOuterProcess setup k ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.toSGDSetup.P +
      η * σeff ^ 2 / μ := by
  sorry

-- ============================================================================
-- Section 4: Outer Loop Convergence Theorem
-- ============================================================================

/-- Outer-loop SVRG convergence under strong convexity.

Main convergence theorem:
  E[‖w_K − w*‖²] ≤ (1 − ημ)^(m·K) · ‖w₀ − w*‖² + σ² / (m·μ²)

Proof: Induction on K epochs, using `epoch_contraction_lemma` for the step case.

Used in: SVRG outer loop (Algorithms/SVRGOuterLoop.lean, main convergence theorem) -/
theorem svrgOuter_convergence_strongly_convex
    (f : E → ℝ) (wStar : E)
    (hgrad : IsGradientOf f setup.toSVRGSetup.toSGDSetup.gradF)
    (hsmooth : IsLSmooth setup.toSVRGSetup.toSGDSetup.gradF L)
    (hsc : StrongConvexOn Set.univ μ f)
    (hvar_inner : HasBoundedVariance setup.toSVRGSetup.toSGDSetup.gradL setup.sampleDist σ)
    (hunb : IsUnbiased setup.toSVRGSetup.toSGDSetup.gradL setup.toSVRGSetup.toSGDSetup.gradF setup.sampleDist)
    (hmin : IsMinimizer f wStar)
    (hμ_pos : 0 < μ) (hη_pos : 0 < η) (hημ : η * μ < 1)
    (hη : ∀ t, setup.toSVRGSetup.toSGDSetup.η t = η)
    (h_int_norm_sq : ∀ k ≤ setup.K, Integrable (fun ω => ‖svrgOuterProcess setup k ω - wStar‖ ^ 2) setup.toSVRGSetup.toSGDSetup.P)
    (h_int_virtual : ∀ k < setup.K, Integrable (fun ω => ‖setup.toSVRGSetup.svrgProcess (svrgOuterProcess setup k ω) (setup.toSVRGSetup.toSGDSetup.gradF (svrgOuterProcess setup k ω)) setup.m ω - wStar‖ ^ 2) setup.toSVRGSetup.toSGDSetup.P) :
    ∫ ω, ‖svrgOuterProcess setup setup.K ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.toSGDSetup.P ≤
      (1 - η * μ) ^ (setup.m * setup.K) * ‖setup.toSVRGSetup.toSGDSetup.w₀ - wStar‖ ^ 2 +
      σ ^ 2 / (setup.m * μ ^ 2) := by
  sorry

end SVRGOuterSetup
