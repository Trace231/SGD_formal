import Algorithms.SVRG
import Lib.Glue.Probability
import Lib.Glue.Algebra
import Lib.Glue.Measurable
import Lib.Glue.Calculus

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {S : Type*} [MeasurableSpace S]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- SVRG outer-loop setup: tracks snapshot sequence and epoch parameters.

Used in: `SVRG outer-loop convergence analysis` (`Algorithms/SVRGOuterLoop.lean`, main theorem) -/
structure SVRGOuterSetup
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E]
    (S : Type*) [MeasurableSpace S]
    (Ω : Type*) [MeasurableSpace Ω] where
  toSVRGSetup : SVRGSetup E S Ω
  m : ℕ  -- inner loop length
  K : ℕ  -- number of outer epochs
  η : ℝ  -- constant step size

namespace SVRGOuterSetup

variable (setup : SVRGOuterSetup E S Ω)

/-- Snapshot sequence: wTilde_k for epoch k. -/
noncomputable def wTilde : ℕ → E := fun k =>
  setup.toSVRGSetup.toSGDSetup.w₀  -- placeholder: will be updated per epoch

/-- Precomputed full gradient at snapshot: gradF(wTilde_k). -/
noncomputable def gradLTilde : ℕ → E := fun k =>
  setup.toSVRGSetup.toSGDSetup.gradF (setup.wTilde k)

/-- Outer process: concatenates inner-loop processes across epochs.

Used in: `SVRG outer-loop convergence analysis` (`Algorithms/SVRGOuterLoop.lean`, main theorem) -/
noncomputable def outerProcess : ℕ → Ω → E := fun t ω =>
  let k := t / setup.m  -- epoch index
  let inner_t := t % setup.m  -- inner iteration within epoch
  setup.toSVRGSetup.svrgProcess (setup.wTilde k) (setup.gradLTilde k) inner_t ω

@[simp] theorem outerProcess_zero :
    setup.outerProcess 0 = fun _ => setup.toSVRGSetup.toSGDSetup.w₀ := by
  funext ω
  simp [SVRGOuterSetup.outerProcess, SVRGOuterSetup.wTilde, SVRGOuterSetup.gradLTilde]
  <;> simp [Nat.div_zero, Nat.mod_zero]
  <;> rfl

/-- Measurability of outer process iterates.

Used in: `SVRG outer-loop convergence analysis` (`Algorithms/SVRGOuterLoop.lean`, bridge construction) -/
theorem outerProcess_measurable
    (hgL : Measurable (Function.uncurry setup.toSVRGSetup.toSGDSetup.gradL))
    (t : ℕ) :
    Measurable (setup.outerProcess t) := by
  let k := t / setup.m
  let inner_t := t % setup.m
  have h_inner_meas : Measurable (setup.toSVRGSetup.svrgProcess (setup.wTilde k) (setup.gradLTilde k) inner_t) :=
    setup.toSVRGSetup.svrgProcess_measurable (setup.wTilde k) (setup.gradLTilde k) hgL inner_t
  simpa [SVRGOuterSetup.outerProcess] using h_inner_meas

/-- Bridge outer-loop SVRG state to `StochasticDescentHyps`.

Used in: `SVRG outer-loop convergence analysis` (`Algorithms/SVRGOuterLoop.lean`, Layer1 interface) -/
noncomputable def outer_to_hyps
    (t : ℕ)
    (hgL : Measurable (Function.uncurry setup.toSVRGSetup.toSGDSetup.gradL))
    (hgF_meas : Measurable setup.toSVRGSetup.toSGDSetup.gradF)
    (k : ℕ := t / setup.m)
    (hunb_eff : IsUnbiased (setup.toSVRGSetup.svrgOracle (setup.wTilde k) (setup.gradLTilde k))
      setup.toSVRGSetup.toSGDSetup.gradF setup.toSVRGSetup.sampleDist) :
    StochasticDescentHyps E S Ω :=
  setup.toSVRGSetup.svrg_to_hyps (setup.wTilde k) (setup.gradLTilde k) (t % setup.m)
    hgL hgF_meas hunb_eff

/-- Outer-loop contraction lemma: expected distance decreases across epochs.

Used in: `SVRG outer-loop convergence analysis` (`Algorithms/SVRGOuterLoop.lean`, main contraction step) -/
theorem outer_loop_contraction
    (f : E → ℝ) {L : NNReal} {μ σeff : ℝ} {wStar : E}
    (hgrad : IsGradientOf f setup.toSVRGSetup.toSGDSetup.gradF)
    (hsmooth : IsLSmooth setup.toSVRGSetup.toSGDSetup.gradF L)
    (hsc : StrongConvexOn Set.univ μ f)
    (hmin : IsMinimizer f wStar)
    (hμ_pos : 0 < μ)
    (hη_pos : 0 < setup.η)
    (hη_L : setup.η ≤ 1 / (L : ℝ))
    (hημ : setup.η * μ < 1)
    (h_sample_prob : IsProbabilityMeasure setup.toSVRGSetup.sampleDist)
    (hgL : Measurable (Function.uncurry setup.toSVRGSetup.toSGDSetup.gradL))
    (h_intL_base : ∀ w, Integrable (setup.toSVRGSetup.toSGDSetup.gradL w) setup.toSVRGSetup.sampleDist)
    (k : ℕ)
    (hvar_eff : HasBoundedVariance (setup.toSVRGSetup.svrgOracle (setup.wTilde k) (setup.gradLTilde k))
      setup.toSVRGSetup.sampleDist σeff)
    (h_int_sq : ∀ t, Integrable (fun ω =>
        ‖setup.toSVRGSetup.svrgOracle (setup.wTilde k) (setup.gradLTilde k)
          (setup.toSVRGSetup.svrgProcess (setup.wTilde k) (setup.gradLTilde k) t ω)
          (setup.toSVRGSetup.toSGDSetup.ξ t ω)‖ ^ 2) setup.toSVRGSetup.toSGDSetup.P)
    (h_int_norm_sq : ∀ t, Integrable (fun ω =>
        ‖setup.toSVRGSetup.svrgProcess (setup.wTilde k) (setup.gradLTilde k) t ω - wStar‖ ^ 2)
        setup.toSVRGSetup.toSGDSetup.P)
    (h_int_inner : ∀ t, Integrable (fun ω =>
        ⟪setup.toSVRGSetup.svrgProcess (setup.wTilde k) (setup.gradLTilde k) t ω - wStar,
          setup.toSVRGSetup.svrgOracle (setup.wTilde k) (setup.gradLTilde k)
            (setup.toSVRGSetup.svrgProcess (setup.wTilde k) (setup.gradLTilde k) t ω)
            (setup.toSVRGSetup.toSGDSetup.ξ t ω)⟫_ℝ) setup.toSVRGSetup.toSGDSetup.P)
    (h_int_gF_inner : ∀ t, Integrable (fun ω =>
        ⟪setup.toSVRGSetup.svrgProcess (setup.wTilde k) (setup.gradLTilde k) t ω - wStar,
          setup.toSVRGSetup.toSGDSetup.gradF (setup.toSVRGSetup.svrgProcess (setup.wTilde k) (setup.gradLTilde k) t ω)⟫_ℝ)
        setup.toSVRGSetup.toSGDSetup.P)
    (hunb : IsUnbiased setup.toSVRGSetup.toSGDSetup.gradL setup.toSVRGSetup.toSGDSetup.gradF
      setup.toSVRGSetup.sampleDist)
    (hgradLTilde : setup.gradLTilde k = setup.toSVRGSetup.toSGDSetup.gradF (setup.wTilde k))
    (hη_const : ∀ t, setup.toSVRGSetup.toSGDSetup.η t = setup.η)
    (h_intL_eff : ∀ w, Integrable (setup.toSVRGSetup.svrgOracle (setup.wTilde k) (setup.gradLTilde k) w)
      setup.toSVRGSetup.sampleDist) :
    ∫ ω, ‖setup.toSVRGSetup.svrgProcess (setup.wTilde k) (setup.gradLTilde k) setup.m ω - wStar‖ ^ 2
        ∂setup.toSVRGSetup.toSGDSetup.P ≤
      (1 - setup.η * μ) ^ setup.m * ∫ ω, ‖setup.toSVRGSetup.svrgProcess (setup.wTilde k) (setup.gradLTilde k) 0 ω - wStar‖ ^ 2
        ∂setup.toSVRGSetup.toSGDSetup.P + setup.η * σeff ^ 2 / μ := by
  have h_process_zero : setup.toSVRGSetup.svrgProcess (setup.wTilde k) (setup.gradLTilde k) 0 =
      fun _ => setup.toSVRGSetup.toSGDSetup.w₀ := by
    simp
  have h_inner : ∫ ω, ‖setup.toSVRGSetup.svrgProcess (setup.wTilde k) (setup.gradLTilde k) setup.m ω - wStar‖ ^ 2
        ∂setup.toSVRGSetup.toSGDSetup.P ≤
      (1 - setup.η * μ) ^ setup.m * ‖setup.toSVRGSetup.toSGDSetup.w₀ - wStar‖ ^ 2 + setup.η * σeff ^ 2 / μ :=
    setup.toSVRGSetup.svrg_convergence_inner_strongly_convex f L μ σeff setup.η wStar
      (setup.wTilde k) (setup.gradLTilde k) hgradLTilde hgrad hsmooth hsc hvar_eff hunb hmin
      h_sample_prob hμ_pos hη_pos hη_L hημ hη_const setup.m hgL h_intL_base
      h_intL_eff h_int_sq h_int_norm_sq h_int_inner h_int_gF_inner
  calc
    ∫ ω, ‖setup.toSVRGSetup.svrgProcess (setup.wTilde k) (setup.gradLTilde k) setup.m ω - wStar‖ ^ 2
        ∂setup.toSVRGSetup.toSGDSetup.P
      ≤ (1 - setup.η * μ) ^ setup.m * ‖setup.toSVRGSetup.toSGDSetup.w₀ - wStar‖ ^ 2 + setup.η * σeff ^ 2 / μ :=
        h_inner
    _ = (1 - setup.η * μ) ^ setup.m * ∫ ω, ‖setup.toSVRGSetup.svrgProcess (setup.wTilde k) (setup.gradLTilde k) 0 ω - wStar‖ ^ 2
        ∂setup.toSVRGSetup.toSGDSetup.P + setup.η * σeff ^ 2 / μ := by
      rw [h_process_zero]
      simp [integral_const, h_sample_prob.measure_univ]

/-- SVRG outer-loop convergence theorem (strongly convex case).

Used in: `SVRG outer-loop convergence analysis` (`Algorithms/SVRGOuterLoop.lean`, main theorem) -/
theorem svrg_outer_convergence_strongly_convex
    (f : E → ℝ) {L : NNReal} {μ σeff : ℝ} {wStar : E}
    (hgrad : IsGradientOf f setup.toSVRGSetup.toSGDSetup.gradF)
    (hsmooth : IsLSmooth setup.toSVRGSetup.toSGDSetup.gradF L)
    (hsc : StrongConvexOn Set.univ μ f)
    (hmin : IsMinimizer f wStar)
    (hμ_pos : 0 < μ)
    (hη_pos : 0 < setup.η)
    (hη_L : setup.η ≤ 1 / (L : ℝ))
    (hημ : setup.η * μ < 1)
    (h_sample_prob : IsProbabilityMeasure setup.toSVRGSetup.sampleDist)
    (hgL : Measurable (Function.uncurry setup.toSVRGSetup.toSGDSetup.gradL))
    (h_intL_base : ∀ w, Integrable (setup.toSVRGSetup.toSGDSetup.gradL w) setup.toSVRGSetup.sampleDist)
    (hvar_eff : ∀ k < setup.K, HasBoundedVariance
      (setup.toSVRGSetup.svrgOracle (setup.wTilde k) (setup.gradLTilde k))
      setup.toSVRGSetup.sampleDist σeff)
    (h_int_sq : ∀ k t, Integrable (fun ω =>
        ‖setup.toSVRGSetup.svrgOracle (setup.wTilde k) (setup.gradLTilde k)
          (setup.toSVRGSetup.svrgProcess (setup.wTilde k) (setup.gradLTilde k) t ω)
          (setup.toSVRGSetup.toSGDSetup.ξ t ω)‖ ^ 2) setup.toSVRGSetup.toSGDSetup.P)
    (h_int_norm_sq : ∀ k t, Integrable (fun ω =>
        ‖setup.toSVRGSetup.svrgProcess (setup.wTilde k) (setup.gradLTilde k) t ω - wStar‖ ^ 2)
        setup.toSVRGSetup.toSGDSetup.P)
    (h_int_inner : ∀ k t, Integrable (fun ω =>
        ⟪setup.toSVRGSetup.svrgProcess (setup.wTilde k) (setup.gradLTilde k) t ω - wStar,
          setup.toSVRGSetup.svrgOracle (setup.wTilde k) (setup.gradLTilde k)
            (setup.toSVRGSetup.svrgProcess (setup.wTilde k) (setup.gradLTilde k) t ω)
            (setup.toSVRGSetup.toSGDSetup.ξ t ω)⟫_ℝ) setup.toSVRGSetup.toSGDSetup.P)
    (h_int_gF_inner : ∀ k t, Integrable (fun ω =>
        ⟪setup.toSVRGSetup.svrgProcess (setup.wTilde k) (setup.gradLTilde k) t ω - wStar,
          setup.toSVRGSetup.toSGDSetup.gradF (setup.toSVRGSetup.svrgProcess (setup.wTilde k) (setup.gradLTilde k) t ω)⟫_ℝ)
        setup.toSVRGSetup.toSGDSetup.P)
    (hunb : IsUnbiased setup.toSVRGSetup.toSGDSetup.gradL setup.toSVRGSetup.toSGDSetup.gradF
      setup.toSVRGSetup.sampleDist)
    (hgradLTilde : ∀ k, setup.gradLTilde k = setup.toSVRGSetup.toSGDSetup.gradF (setup.wTilde k)) :
    ∫ ω, ‖setup.outerProcess (setup.K * setup.m) ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.toSGDSetup.P ≤
      (1 - setup.η * μ) ^ (setup.K * setup.m) * ‖setup.toSVRGSetup.toSGDSetup.w₀ - wStar‖ ^ 2 +
        (setup.η * σeff ^ 2 / μ) * (Finset.sum (Finset.range setup.K) fun k => (1 - setup.η * μ) ^ ((setup.K - 1 - k) * setup.m)) := by
  have hη_const : ∀ t, setup.toSVRGSetup.toSGDSetup.η t = setup.η := by
    intro t; simp
  -- Proof by induction on K
  induction setup.K with
  | zero =>
    -- Base case: K = 0
    simp [SVRGOuterSetup.outerProcess, Nat.zero_mul, Finset.sum_range_zero]
  | succ K ih =>
    -- Inductive step: assume true for K, prove for K+1
    -- In this context, setup.K = K + 1, and we need to prove for (K+1)*m
    have hK_lt : K < K + 1 := by
      omega
    have hvar_eff_K : HasBoundedVariance
        (setup.toSVRGSetup.svrgOracle (setup.wTilde K) (setup.gradLTilde K))
        setup.toSVRGSetup.sampleDist σeff :=
      hvar_eff K hK_lt
    have hgradLTilde_K : setup.gradLTilde K = setup.toSVRGSetup.toSGDSetup.gradF (setup.wTilde K) :=
      hgradLTilde K
    -- Apply contraction lemma for epoch K
    have h_contr : ∫ ω, ‖setup.toSVRGSetup.svrgProcess (setup.wTilde K) (setup.gradLTilde K) setup.m ω - wStar‖ ^ 2
          ∂setup.toSVRGSetup.toSGDSetup.P ≤
        (1 - setup.η * μ) ^ setup.m * ∫ ω, ‖setup.toSVRGSetup.svrgProcess (setup.wTilde K) (setup.gradLTilde K) 0 ω - wStar‖ ^ 2
          ∂setup.toSVRGSetup.toSGDSetup.P + setup.η * σeff ^ 2 / μ :=
      outer_loop_contraction f L μ σeff wStar hgrad hsmooth hsc hmin hμ_pos hη_pos hη_L hημ
        h_sample_prob hgL h_intL_base K hvar_eff_K h_int_sq h_int_norm_sq h_int_inner h_int_gF_inner
        hunb hgradLTilde_K hη_const (fun w => h_intL_base w)
    -- Simplify outerProcess definition
    have h_outer_Km : setup.outerProcess (K * setup.m) =
        setup.toSVRGSetup.svrgProcess (setup.wTilde K) (setup.gradLTilde K) 0 := by
      funext ω
      simp [SVRGOuterSetup.outerProcess, Nat.div_eq_of_lt]
      <;> omega
    have h_outer_Km_succ : setup.outerProcess ((K + 1) * setup.m) =
        setup.toSVRGSetup.svrgProcess (setup.wTilde K) (setup.gradLTilde K) setup.m := by
      funext ω
      simp [SVRGOuterSetup.outerProcess]
      <;> ring_nf
      <;> simp [Nat.div_eq_of_lt]
      <;> omega
    -- Rewrite goal using these equalities
    rw [h_outer_Km_succ]
    rw [h_outer_Km] at h_contr
    -- Apply induction hypothesis and combine
    simp_all [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul, Finset.sum_range_succ]
    <;> nlinarith

end SVRGOuterSetup
