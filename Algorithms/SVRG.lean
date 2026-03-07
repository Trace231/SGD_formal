import Algorithms.SGD
import Lib.Glue.Probability

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {S : Type*} [MeasurableSpace S]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- SVRG setup for inner-loop analysis: stochastic infrastructure is inherited from `SGDSetup`.

The snapshot `wTilde` and its precomputed full gradient are theorem parameters, not structure
fields, because they vary across outer epochs. -/
structure SVRGSetup
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E]
    (S : Type*) [MeasurableSpace S]
    (Ω : Type*) [MeasurableSpace Ω] where
  toSGDSetup : SGDSetup E S Ω

namespace SVRGSetup

variable (setup : SVRGSetup E S Ω)

/-- Sample distribution inherited from the base setup. -/
noncomputable def sampleDist : Measure S :=
  setup.toSGDSetup.sampleDist

/-- SVRG variance-reduced oracle with fixed snapshot and precomputed full gradient term.

`svrgOracle wTilde gradLTilde w s = gradL(w,s) - gradL(wTilde,s) + gradLTilde`. -/
def svrgOracle (wTilde gradLTilde : E) (w : E) (s : S) : E :=
  setup.toSGDSetup.gradL w s - setup.toSGDSetup.gradL wTilde s + gradLTilde

/-- SVRG inner-loop process for fixed snapshot parameters. -/
noncomputable def svrgProcess (wTilde gradLTilde : E) : ℕ → Ω → E :=
  sgdProcess setup.toSGDSetup.w₀ setup.toSGDSetup.η
    (setup.svrgOracle wTilde gradLTilde) setup.toSGDSetup.ξ

omit [SecondCountableTopology E] in
@[simp] theorem process_zero (wTilde gradLTilde : E) :
    setup.svrgProcess wTilde gradLTilde 0 = fun _ => setup.toSGDSetup.w₀ := rfl

omit [SecondCountableTopology E] in
@[simp] theorem process_succ (wTilde gradLTilde : E) (t : ℕ) :
    setup.svrgProcess wTilde gradLTilde (t + 1) = fun ω =>
      setup.svrgProcess wTilde gradLTilde t ω
        - (setup.toSGDSetup.η t) •
          (setup.toSGDSetup.gradL (setup.svrgProcess wTilde gradLTilde t ω) (setup.toSGDSetup.ξ t ω)
            - setup.toSGDSetup.gradL wTilde (setup.toSGDSetup.ξ t ω) + gradLTilde) := rfl

/-- Measurability of the SVRG oracle from base joint measurability.

Used in: `SVRG inner-loop strongly-convex convergence`
(`Algorithms/SVRG.lean`, bridge construction — oracle measurability) -/
theorem measurable_svrgOracle
    (wTilde gradLTilde : E)
    (hgL : Measurable (Function.uncurry setup.toSGDSetup.gradL)) :
    Measurable (Function.uncurry (setup.svrgOracle wTilde gradLTilde)) := by
  have h_wTilde : Measurable (fun p : E × S => setup.toSGDSetup.gradL wTilde p.2) := by
    simpa [Function.uncurry] using
      hgL.comp ((measurable_const : Measurable (fun _ : E × S => wTilde)).prodMk measurable_snd)
  simpa [SVRGSetup.svrgOracle, Function.uncurry] using
    (hgL.sub h_wTilde).add measurable_const

/-- Measurability of each SVRG iterate.

Used in: `SVRG inner-loop strongly-convex convergence`
(`Algorithms/SVRG.lean`, bridge construction — iterate measurability) -/
theorem svrgProcess_measurable
    (wTilde gradLTilde : E)
    (hgL : Measurable (Function.uncurry setup.toSGDSetup.gradL))
    (t : ℕ) :
    Measurable (setup.svrgProcess wTilde gradLTilde t) := by
  simpa [SVRGSetup.svrgProcess] using
    (sgdProcess_measurable
      (hξ := setup.toSGDSetup.hξ_meas)
      (hg := setup.measurable_svrgOracle wTilde gradLTilde hgL)
      (t := t))

/-- Adaptedness of SVRG process to `sgdFiltration`.

Used in: `SVRG inner-loop strongly-convex convergence`
(`Algorithms/SVRG.lean`, filtration argument reuse) -/
theorem svrgProcess_adapted
    (wTilde gradLTilde : E)
    (hgL : Measurable (Function.uncurry setup.toSGDSetup.gradL)) :
    Adapted (sgdFiltration setup.toSGDSetup.ξ setup.toSGDSetup.hξ_meas)
      (fun t => setup.svrgProcess wTilde gradLTilde t) := by
  simpa [SVRGSetup.svrgProcess] using
    (sgdProcess_adapted
      (hξ := setup.toSGDSetup.hξ_meas)
      (hg := setup.measurable_svrgOracle wTilde gradLTilde hgL))

/-- Independence of `svrgProcess t` and fresh sample `ξ t`.

Used in: `SVRG inner-loop strongly-convex convergence`
(`Algorithms/SVRG.lean`, bridge construction — independence field) -/
lemma svrgProcess_indepFun_xi
    (wTilde gradLTilde : E)
    (hgL : Measurable (Function.uncurry setup.toSGDSetup.gradL))
    (t : ℕ) :
    IndepFun (setup.svrgProcess wTilde gradLTilde t) (setup.toSGDSetup.ξ t) setup.toSGDSetup.P := by
  simpa [SVRGSetup.svrgProcess] using
    (sgdProcess_indepFun_xi
      (hξ_meas := setup.toSGDSetup.hξ_meas)
      (hξ_indep := setup.toSGDSetup.hξ_indep)
      (hgL := setup.measurable_svrgOracle wTilde gradLTilde hgL)
      (t := t))

omit [SecondCountableTopology E] in
/-- Unbiasedness of the SVRG oracle at fixed snapshot.

This is the key integral identity:
`∫(gradL w - gradL wTilde + gradLTilde) = gradF w`
when `gradLTilde = gradF wTilde`.

Used in: `SVRG inner-loop strongly-convex convergence`
(`Algorithms/SVRG.lean`, bridge construction — unbiasedness) -/
theorem unbiased_svrgOracle
    (wTilde gradLTilde : E)
    (hunb : IsUnbiased setup.toSGDSetup.gradL setup.toSGDSetup.gradF setup.sampleDist)
    (h_sample_prob : IsProbabilityMeasure setup.sampleDist)
    (h_intL : ∀ w, Integrable (setup.toSGDSetup.gradL w) setup.sampleDist)
    (hgradLTilde : gradLTilde = setup.toSGDSetup.gradF wTilde) :
    IsUnbiased (setup.svrgOracle wTilde gradLTilde) setup.toSGDSetup.gradF setup.sampleDist := by
  intro w
  letI : IsProbabilityMeasure setup.sampleDist := h_sample_prob
  have h_sub_int : Integrable
      (fun s => setup.toSGDSetup.gradL w s - setup.toSGDSetup.gradL wTilde s) setup.sampleDist :=
    (h_intL w).sub (h_intL wTilde)
  calc
    ∫ s, setup.svrgOracle wTilde gradLTilde w s ∂setup.sampleDist
        = ∫ s, (setup.toSGDSetup.gradL w s - setup.toSGDSetup.gradL wTilde s) ∂setup.sampleDist
          + ∫ s, gradLTilde ∂setup.sampleDist := by
            rw [show (fun s => setup.svrgOracle wTilde gradLTilde w s) =
                (fun s => (setup.toSGDSetup.gradL w s - setup.toSGDSetup.gradL wTilde s) + gradLTilde)
                from by
                  ext s
                  simp [SVRGSetup.svrgOracle]]
            rw [integral_add h_sub_int (integrable_const _)]
    _ = (∫ s, setup.toSGDSetup.gradL w s ∂setup.sampleDist)
          - (∫ s, setup.toSGDSetup.gradL wTilde s ∂setup.sampleDist) + gradLTilde := by
            simp [integral_sub (h_intL w) (h_intL wTilde), integral_const, probReal_univ]
    _ = setup.toSGDSetup.gradF w - setup.toSGDSetup.gradF wTilde + gradLTilde := by
          rw [hunb w, hunb wTilde]
    _ = setup.toSGDSetup.gradF w := by
          simpa [hgradLTilde] using
            (sub_add_cancel (setup.toSGDSetup.gradF w) (setup.toSGDSetup.gradF wTilde))

/-- Effective SGD setup corresponding to fixed-snapshot SVRG inner loop.

Used in: `SVRG inner-loop strongly-convex convergence`
(`Algorithms/SVRG.lean`, reduction to SGD strongly-convex theorem) -/
noncomputable def effectiveSGDSetup (wTilde gradLTilde : E) : SGDSetup E S Ω where
  w₀ := setup.toSGDSetup.w₀
  η := setup.toSGDSetup.η
  gradL := setup.svrgOracle wTilde gradLTilde
  gradF := setup.toSGDSetup.gradF
  ξ := setup.toSGDSetup.ξ
  P := setup.toSGDSetup.P
  hP := setup.toSGDSetup.hP
  hξ_meas := setup.toSGDSetup.hξ_meas
  hξ_indep := setup.toSGDSetup.hξ_indep
  hξ_ident := setup.toSGDSetup.hξ_ident

/-- Bridge fixed-snapshot SVRG state at step `t` to `StochasticDescentHyps`.

Used in: `SVRG inner-loop strongly-convex convergence`
(`Algorithms/SVRG.lean`, one-step Layer1 interface) -/
noncomputable def svrg_to_hyps
    (wTilde gradLTilde : E)
    (t : ℕ)
    (hgL : Measurable (Function.uncurry setup.toSGDSetup.gradL))
    (hgF_meas : Measurable setup.toSGDSetup.gradF)
    (hunb_eff : IsUnbiased (setup.svrgOracle wTilde gradLTilde) setup.toSGDSetup.gradF setup.sampleDist) :
    StochasticDescentHyps E S Ω :=
  sgd_to_hyps (setup := setup.effectiveSGDSetup wTilde gradLTilde) t
    (setup.measurable_svrgOracle wTilde gradLTilde hgL) hgF_meas hunb_eff

-- Optional bridge: derive `HasBoundedVariance` from finite-sum SVRG assumptions.
set_option maxHeartbeats 4000000 in
theorem svrg_hvar_eff_from_finite
    (setup : SVRGSetup E S Ω) (f : E → ℝ) {L : NNReal} {σeff : ℝ}
    [Fintype S] [Nonempty S]
    (wStar wTilde gradLTilde : E) (fStar : ℝ)
    (hgradLTilde : gradLTilde = setup.toSGDSetup.gradF wTilde)
    (h_unif_sample : ∀ g : S → ℝ, Integrable g setup.sampleDist →
      ∫ s, g s ∂setup.sampleDist = (1 / (Fintype.card S : ℝ)) * ∑ s : S, g s)
    (h_int_oracle_sample : ∀ w : E, Integrable
      (fun s => ‖setup.toSGDSetup.gradL w s - setup.toSGDSetup.gradL wTilde s +
        setup.toSGDSetup.gradF wTilde‖ ^ 2) setup.sampleDist)
    (h_pointwise_oracle : ∀ s : S, ∀ w : E,
      ‖setup.toSGDSetup.gradL w s - setup.toSGDSetup.gradL wTilde s + setup.toSGDSetup.gradF wTilde‖ ^ 2
        ≤ 4 * (L : ℝ) * (f w - fStar) +
          2 * ‖setup.toSGDSetup.gradF wTilde - setup.toSGDSetup.gradF wStar‖ ^ 2)
    (h_int_eff_sq_sample : ∀ w : E, Integrable
      (fun s => ‖setup.svrgOracle wTilde gradLTilde w s‖ ^ 2) setup.sampleDist)
    (h_rhs_uniform : ∀ w : E,
      4 * (L : ℝ) * (f w - fStar) +
        2 * ‖setup.toSGDSetup.gradF wTilde - setup.toSGDSetup.gradF wStar‖ ^ 2 ≤ σeff ^ 2) :
    HasBoundedVariance (setup.svrgOracle wTilde gradLTilde) setup.sampleDist σeff := by
  intro w
  refine ⟨h_int_eff_sq_sample w, ?_⟩
  have h_vr0 :
      ∫ s, ‖setup.toSGDSetup.gradL w s - setup.toSGDSetup.gradL wTilde s +
            setup.toSGDSetup.gradF wTilde‖ ^ 2 ∂setup.sampleDist
        ≤ 4 * (L : ℝ) * (f w - fStar)
          + 2 * ‖setup.toSGDSetup.gradF wTilde - setup.toSGDSetup.gradF wStar‖ ^ 2 :=
    _root_.svrg_variance_reduction
      (E := E) (S := S)
      (gradL := setup.toSGDSetup.gradL) (gradF := setup.toSGDSetup.gradF) (f := f)
      (ν := setup.sampleDist) (L := L) (wTilde := wTilde) (wStar := wStar) (fStar := fStar)
      h_unif_sample h_int_oracle_sample h_pointwise_oracle w
  have h_vr : ∫ s, ‖setup.svrgOracle wTilde gradLTilde w s‖ ^ 2 ∂setup.sampleDist
      ≤ 4 * (L : ℝ) * (f w - fStar)
        + 2 * ‖setup.toSGDSetup.gradF wTilde - setup.toSGDSetup.gradF wStar‖ ^ 2 := by
    simpa [SVRGSetup.svrgOracle, hgradLTilde] using h_vr0
  exact h_vr.trans (h_rhs_uniform w)

/-- Inner-loop strongly-convex convergence for fixed-snapshot SVRG.

This theorem uses the effective-SGD reduction. The caller provides a uniform
effective second-moment bound for the fixed-snapshot oracle.

Used in: `SVRG inner-loop strongly-convex convergence`
(`Algorithms/SVRG.lean`, final inner-loop theorem) -/
theorem svrg_convergence_inner_strongly_convex
    (setup : SVRGSetup E S Ω) (f : E → ℝ) {L : NNReal} {μ σeff η : ℝ}
    (wStar wTilde gradLTilde : E)
    (hgradLTilde : gradLTilde = setup.toSGDSetup.gradF wTilde)
    (hgrad : IsGradientOf f setup.toSGDSetup.gradF)
    (hsmooth : IsLSmooth setup.toSGDSetup.gradF L)
    (hsc : StrongConvexOn Set.univ μ f)
    (hvar_eff : HasBoundedVariance (setup.svrgOracle wTilde gradLTilde) setup.sampleDist σeff)
    (hunb : IsUnbiased setup.toSGDSetup.gradL setup.toSGDSetup.gradF setup.sampleDist)
    (hmin : IsMinimizer f wStar)
    (h_sample_prob : IsProbabilityMeasure setup.sampleDist)
    (hμ_pos : 0 < μ) (hη_pos : 0 < η) (_hη_L : η ≤ 1 / (L : ℝ))
    (hημ : η * μ < 1) (hη : ∀ t, setup.toSGDSetup.η t = η)
    (T : ℕ)
    (hgL : Measurable (Function.uncurry setup.toSGDSetup.gradL))
    (h_intL_base : ∀ w, Integrable (setup.toSGDSetup.gradL w) setup.sampleDist)
    (h_intL_eff : ∀ w, Integrable (setup.svrgOracle wTilde gradLTilde w) setup.sampleDist)
    (h_int_sq : ∀ t, Integrable (fun ω =>
        ‖setup.svrgOracle wTilde gradLTilde (setup.svrgProcess wTilde gradLTilde t ω)
          (setup.toSGDSetup.ξ t ω)‖ ^ 2) setup.toSGDSetup.P)
    (h_int_norm_sq : ∀ t, Integrable (fun ω =>
        ‖setup.svrgProcess wTilde gradLTilde t ω - wStar‖ ^ 2) setup.toSGDSetup.P)
    (h_int_inner : ∀ t, Integrable (fun ω =>
        ⟪setup.svrgProcess wTilde gradLTilde t ω - wStar,
          setup.svrgOracle wTilde gradLTilde (setup.svrgProcess wTilde gradLTilde t ω)
            (setup.toSGDSetup.ξ t ω)⟫_ℝ) setup.toSGDSetup.P)
    (h_int_gF_inner : ∀ t, Integrable (fun ω =>
        ⟪setup.svrgProcess wTilde gradLTilde t ω - wStar,
          setup.toSGDSetup.gradF (setup.svrgProcess wTilde gradLTilde t ω)⟫_ℝ) setup.toSGDSetup.P) :
    ∫ ω, ‖setup.svrgProcess wTilde gradLTilde T ω - wStar‖ ^ 2 ∂setup.toSGDSetup.P ≤
      (1 - η * μ) ^ T * ‖setup.toSGDSetup.w₀ - wStar‖ ^ 2 + η * σeff ^ 2 / μ := by
  have hunb_eff :
      IsUnbiased (setup.svrgOracle wTilde gradLTilde) setup.toSGDSetup.gradF setup.sampleDist :=
    setup.unbiased_svrgOracle wTilde gradLTilde hunb h_sample_prob h_intL_base hgradLTilde
  simpa [SVRGSetup.svrgProcess] using
    (sgd_convergence_strongly_convex_v2
      (setup := setup.effectiveSGDSetup wTilde gradLTilde)
      (f := f) (wStar := wStar)
      hgrad hsmooth hsc hvar_eff hunb_eff hmin
      hμ_pos hη_pos _hη_L hημ hη T
      (setup.measurable_svrgOracle wTilde gradLTilde hgL)
      h_intL_eff h_int_sq h_int_norm_sq h_int_inner h_int_gF_inner)

/-- Outer-loop SVRG theorem stub (out of scope for this pass).

Used in: `SVRG outer-loop roadmap` (`Algorithms/SVRG.lean`, placeholder theorem). -/
theorem svrg_convergence_outer_stub
    (setup : SVRGSetup E S Ω) :
    True := by
  sorry

end SVRGSetup
