import Algorithms.SVRG
import Lib.Glue.Staging.SVRGOuterLoop

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {S : Type*} [MeasurableSpace S]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- SVRG outer-loop setup: manages epoch-to-epoch snapshot updates.

The outer loop runs for `numEpochs` epochs. Each epoch:
1. Computes the full gradient at the snapshot point `wTilde_k`
2. Runs the inner SVRG loop for `innerIters` iterations
3. Sets the next snapshot to the final inner iterate

Used in: `svrg_outer_convergence_strongly_convex` (Algorithms/SVRGOuterLoop.lean, main theorem) -/
structure SVRGOuterSetup
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E]
    (S : Type*) [MeasurableSpace S]
    (Ω : Type*) [MeasurableSpace Ω] where
  innerSetup : SVRGSetup E S Ω
  numEpochs : ℕ
  innerIters : ℕ

namespace SVRGOuterSetup

/-- Snapshot sequence: `outerSnapshot setup k` is the snapshot at epoch `k`.

Defined recursively:
- `outerSnapshot setup 0 = w₀` (initial point)
- `outerSnapshot setup (k+1) = innerLoopResult k (innerIters - 1)` (final inner iterate)

Used in: `svrg_outer_convergence_strongly_convex` (Algorithms/SVRGOuterLoop.lean, main theorem) -/
noncomputable def outerSnapshot (setup : SVRGOuterSetup E S Ω) : ℕ → Ω → E
  | 0 => fun _ => setup.innerSetup.toSGDSetup.w₀
  | k + 1 => fun ω =>
      let wTilde := outerSnapshot setup k ω
      let gradLTilde := setup.innerSetup.toSGDSetup.gradF wTilde
      setup.innerSetup.svrgProcess wTilde gradLTilde setup.innerIters ω

/-- Precomputed full gradient at snapshot for epoch `k`.

`outerGradLTilde setup k ω = gradF (outerSnapshot setup k ω)`

Used in: `svrg_outer_convergence_strongly_convex` (Algorithms/SVRGOuterLoop.lean, main theorem) -/
noncomputable def outerGradLTilde (setup : SVRGOuterSetup E S Ω) : ℕ → Ω → E
  | k => fun ω => setup.innerSetup.toSGDSetup.gradF (outerSnapshot setup k ω)

/-- Outer-loop process: `outerProcess setup k t ω` is the iterate at epoch `k`, inner step `t`.

For epoch `k`, we run the inner SVRG loop with snapshot `outerSnapshot setup k` and
precomputed gradient `outerGradLTilde setup k`.

Used in: `svrg_outer_convergence_strongly_convex` (Algorithms/SVRGOuterLoop.lean, main theorem) -/
noncomputable def outerProcess (setup : SVRGOuterSetup E S Ω) : ℕ → ℕ → Ω → E
  | k, t => fun ω =>
      let wTilde := outerSnapshot setup k ω
      let gradLTilde := outerGradLTilde setup k ω
      setup.innerSetup.svrgProcess wTilde gradLTilde t ω

/-- Measurability of outer snapshot sequence.

Used in: `svrg_outer_convergence_strongly_convex` (Algorithms/SVRGOuterLoop.lean, measurability argument) -/
theorem outerSnapshot_measurable
    (setup : SVRGOuterSetup E S Ω)
    (hgL : Measurable (Function.uncurry setup.innerSetup.toSGDSetup.gradL))
    (hgF : Measurable setup.innerSetup.toSGDSetup.gradF)
    (k : ℕ) :
    Measurable (outerSnapshot setup k) := by
  induction k with
  | zero =>
    simp [outerSnapshot]
  | succ k ih =>
    simp [outerSnapshot, outerGradLTilde]
    -- Measurability of svrgProcess with ω-dependent snapshot requires advanced treatment
    -- This would need a lemma about joint measurability in (wTilde, gradLTilde, ω)
    -- For now, we use the staging lemma
    exact svrgProcess_measurable_random_snapshot setup.innerSetup (outerSnapshot setup k)
      (setup.innerSetup.toSGDSetup.gradF ∘ outerSnapshot setup k) ih
      (hgF.comp ih) hgL setup.innerIters

/-- Outer-loop strongly-convex convergence theorem.

This theorem bounds the expected squared distance to optimum after `numEpochs` epochs,
where each epoch runs `innerIters` inner iterations.

Used in: `SVRG outer-loop convergence analysis` (Algorithms/SVRGOuterLoop.lean, main result) -/
theorem svrg_outer_convergence_strongly_convex
    (setup : SVRGOuterSetup E S Ω) (f : E → ℝ) {L : NNReal} {μ σeff η : ℝ}
    (wStar : E)
    (hgrad : IsGradientOf f setup.innerSetup.toSGDSetup.gradF)
    (hsmooth : IsLSmooth setup.innerSetup.toSGDSetup.gradF L)
    (hsc : StrongConvexOn Set.univ μ f)
    (hunb : IsUnbiased setup.innerSetup.toSGDSetup.gradL setup.innerSetup.toSGDSetup.gradF
      setup.innerSetup.sampleDist)
    (hmin : IsMinimizer f wStar)
    (h_sample_prob : IsProbabilityMeasure setup.innerSetup.sampleDist)
    (hμ_pos : 0 < μ) (hη_pos : 0 < η) (_hη_L : η ≤ 1 / (L : ℝ))
    (hημ : η * μ < 1) (hη : ∀ t, setup.innerSetup.toSGDSetup.η t = η)
    (h_inner_iters : setup.innerIters > 0)
    (hgL : Measurable (Function.uncurry setup.innerSetup.toSGDSetup.gradL))
    (hgF : Measurable setup.innerSetup.toSGDSetup.gradF)
    (h_intL_base : ∀ w, Integrable (setup.innerSetup.toSGDSetup.gradL w)
      setup.innerSetup.sampleDist)
    (hvar_eff : ∀ k ω, HasBoundedVariance
      (setup.innerSetup.svrgOracle (outerSnapshot setup k ω) (outerGradLTilde setup k ω))
      setup.innerSetup.sampleDist σeff)
    (h_int_sq : ∀ k t, Integrable (fun ω =>
        ‖setup.innerSetup.svrgOracle (outerSnapshot setup k ω) (outerGradLTilde setup k ω)
          (outerProcess setup k t ω) (setup.innerSetup.toSGDSetup.ξ t ω)‖ ^ 2)
      setup.innerSetup.toSGDSetup.P)
    (h_int_norm_sq : ∀ k t, Integrable (fun ω =>
        ‖outerProcess setup k t ω - wStar‖ ^ 2) setup.innerSetup.toSGDSetup.P)
    (h_int_inner : ∀ k t, Integrable (fun ω =>
        ⟪outerProcess setup k t ω - wStar,
          setup.innerSetup.svrgOracle (outerSnapshot setup k ω) (outerGradLTilde setup k ω)
            (outerProcess setup k t ω) (setup.innerSetup.toSGDSetup.ξ t ω)⟫_ℝ)
      setup.innerSetup.toSGDSetup.P)
    (h_int_gF_inner : ∀ k t, Integrable (fun ω =>
        ⟪outerProcess setup k t ω - wStar,
          setup.innerSetup.toSGDSetup.gradF (outerProcess setup k t ω)⟫_ℝ)
      setup.innerSetup.toSGDSetup.P) :
    ∫ ω, ‖outerProcess setup setup.numEpochs 0 ω - wStar‖ ^ 2 ∂setup.innerSetup.toSGDSetup.P ≤
      (1 - η * μ) ^ (setup.numEpochs * setup.innerIters) * ‖setup.innerSetup.toSGDSetup.w₀ - wStar‖ ^ 2
        + (η * σeff ^ 2 / μ) * (1 - (1 - η * μ) ^ setup.numEpochs) / (η * μ) := by
  -- Outer-loop convergence proof requires iterative application of inner-loop convergence
  -- This is a stub for the full proof
  sorry

end SVRGOuterSetup
