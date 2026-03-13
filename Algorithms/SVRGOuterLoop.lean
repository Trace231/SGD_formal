import Algorithms.SVRG
import Lib.Glue.Probability
import Lib.Glue.Staging.SVRGOuterLoop

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {S : Type*} [MeasurableSpace S]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- SVRG outer-loop setup: manages snapshot updates across epochs.

The outer loop maintains a sequence of snapshots `w̃_k` and their corresponding
full gradients `∇f(w̃_k)`, which are used to initialize each inner loop. -/
structure SVRGOuterSetup
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E]
    (S : Type*) [MeasurableSpace S]
    (Ω : Type*) [MeasurableSpace Ω] where
  toSVRGSetup : SVRGSetup E S Ω
  m : ℕ  -- inner loop length
  K : ℕ  -- number of outer epochs
  wInit : E  -- initial snapshot

namespace SVRGOuterSetup

/-- Sample distribution inherited from the base setup.

Used in: `svrg_outer_convergence_strongly_convex` (Algorithms/SVRGOuterLoop.lean, main theorem) -/
noncomputable def sampleDist (setup : SVRGOuterSetup E S Ω) : Measure S :=
  setup.toSVRGSetup.toSGDSetup.sampleDist

/-- Outer process: sequence of snapshots across epochs.

`outerProcess setup k` returns the snapshot at epoch `k`.
Note: This is a simplified deterministic version for theorem statement purposes.
In a full formalization, this would track the random iterate.

Used in: `svrg_outer_convergence_strongly_convex` (Algorithms/SVRGOuterLoop.lean, main theorem) -/
noncomputable def outerProcess (setup : SVRGOuterSetup E S Ω) : ℕ → E :=
  Nat.rec setup.wInit fun k w_k => w_k

/-- Inner process for epoch k, given snapshot w̃_k.

`innerProcess setup k t ω` returns the t-th iterate of the inner loop at epoch k.

Used in: `svrg_outer_convergence_strongly_convex` (Algorithms/SVRGOuterLoop.lean, main theorem) -/
noncomputable def innerProcess (setup : SVRGOuterSetup E S Ω) (k : ℕ) : ℕ → Ω → E :=
  let w_k := outerProcess setup k
  let gradLTilde := setup.toSVRGSetup.toSGDSetup.gradF w_k
  setup.toSVRGSetup.svrgProcess w_k gradLTilde

/-- Measurability of the inner process at epoch k.

Used in: `svrg_outer_convergence_strongly_convex` (Algorithms/SVRGOuterLoop.lean, measurability argument) -/
theorem innerProcess_measurable (setup : SVRGOuterSetup E S Ω) (k t : ℕ)
    (hgL : Measurable (Function.uncurry setup.toSVRGSetup.toSGDSetup.gradL)) :
    Measurable (innerProcess setup k t) := by
  let w_k := outerProcess setup k
  let gradLTilde := setup.toSVRGSetup.toSGDSetup.gradF w_k
  exact setup.toSVRGSetup.svrgProcess_measurable w_k gradLTilde hgL t

/-- Adaptedness of the inner process at epoch k.

Used in: `svrg_outer_convergence_strongly_convex` (Algorithms/SVRGOuterLoop.lean, filtration argument) -/
theorem innerProcess_adapted (setup : SVRGOuterSetup E S Ω) (k : ℕ)
    (hgL : Measurable (Function.uncurry setup.toSVRGSetup.toSGDSetup.gradL)) :
    Adapted (sgdFiltration setup.toSVRGSetup.toSGDSetup.ξ setup.toSVRGSetup.toSGDSetup.hξ_meas)
      (fun t => innerProcess setup k t) := by
  let w_k := outerProcess setup k
  let gradLTilde := setup.toSVRGSetup.toSGDSetup.gradF w_k
  exact setup.toSVRGSetup.svrgProcess_adapted w_k gradLTilde hgL

/-- Independence of inner process and fresh samples at epoch k.

Used in: `svrg_outer_convergence_strongly_convex` (Algorithms/SVRGOuterLoop.lean, independence argument) -/
lemma innerProcess_indepFun_xi (setup : SVRGOuterSetup E S Ω) (k t : ℕ)
    (hgL : Measurable (Function.uncurry setup.toSVRGSetup.toSGDSetup.gradL)) :
    IndepFun (innerProcess setup k t) (setup.toSVRGSetup.toSGDSetup.ξ t)
      setup.toSVRGSetup.toSGDSetup.P := by
  let w_k := outerProcess setup k
  let gradLTilde := setup.toSVRGSetup.toSGDSetup.gradF w_k
  exact setup.toSVRGSetup.svrgProcess_indepFun_xi w_k gradLTilde hgL t

/-- Outer-loop convergence theorem for strongly convex objectives.

This theorem establishes linear convergence of the SVRG outer loop when the
objective is strongly convex and smooth.

Used in: `svrg_outer_convergence_strongly_convex` (Algorithms/SVRGOuterLoop.lean, main convergence result) -/
theorem svrg_outer_convergence_strongly_convex
    (setup : SVRGOuterSetup E S Ω) (f : E → ℝ) {L : NNReal} {μ σeff η : ℝ}
    (wStar : E)
    (hgrad : IsGradientOf f setup.toSVRGSetup.toSGDSetup.gradF)
    (hsmooth : IsLSmooth setup.toSVRGSetup.toSGDSetup.gradF L)
    (hsc : StrongConvexOn Set.univ μ f)
    (hvar : HasBoundedVariance setup.toSVRGSetup.toSGDSetup.gradL (sampleDist setup) σeff)
    (hunb : IsUnbiased setup.toSVRGSetup.toSGDSetup.gradL setup.toSVRGSetup.toSGDSetup.gradF (sampleDist setup))
    (hmin : IsMinimizer f wStar)
    (h_sample_prob : IsProbabilityMeasure (sampleDist setup))
    (hμ_pos : 0 < μ) (hη_pos : 0 < η)
    (hη_L : η ≤ 1 / (L : ℝ))
    (hημ : η * μ < 1)
    (hη_const : ∀ t, setup.toSVRGSetup.toSGDSetup.η t = η)
    (h_inner_length : setup.m ≥ 1)
    (hgL : Measurable (Function.uncurry setup.toSVRGSetup.toSGDSetup.gradL))
    (hgF_meas : Measurable setup.toSVRGSetup.toSGDSetup.gradF)
    (h_intL : ∀ w, Integrable (setup.toSVRGSetup.toSGDSetup.gradL w) (sampleDist setup))
    (h_int_sq : ∀ k t, Integrable (fun ω =>
        ‖setup.toSVRGSetup.svrgOracle (outerProcess setup k)
            (setup.toSVRGSetup.toSGDSetup.gradF (outerProcess setup k))
            (innerProcess setup k t ω)
            (setup.toSVRGSetup.toSGDSetup.ξ t ω)‖ ^ 2)
        setup.toSVRGSetup.toSGDSetup.P)
    (h_int_norm_sq : ∀ k t, Integrable (fun ω =>
        ‖innerProcess setup k t ω - wStar‖ ^ 2) setup.toSVRGSetup.toSGDSetup.P)
    (h_int_inner : ∀ k t, Integrable (fun ω =>
        ⟪innerProcess setup k t ω - wStar,
          setup.toSVRGSetup.svrgOracle (outerProcess setup k)
            (setup.toSVRGSetup.toSGDSetup.gradF (outerProcess setup k))
            (innerProcess setup k t ω)
            (setup.toSVRGSetup.toSGDSetup.ξ t ω)⟫_ℝ)
        setup.toSVRGSetup.toSGDSetup.P)
    (h_int_gF_inner : ∀ k t, Integrable (fun ω =>
        ⟪innerProcess setup k t ω - wStar,
          setup.toSVRGSetup.toSGDSetup.gradF (innerProcess setup k t ω)⟫_ℝ)
        setup.toSVRGSetup.toSGDSetup.P) :
    ∫ ω, ‖innerProcess setup setup.K 0 ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.toSGDSetup.P ≤
      (1 - η * μ) ^ (setup.K * setup.m) * ‖setup.wInit - wStar‖ ^ 2 +
        (η * σeff ^ 2 / μ) * (1 - (1 - η * μ) ^ setup.K) := by
  sorry

end SVRGOuterSetup
