import Algorithms.SGD

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {S : Type*} [MeasurableSpace S]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Weight-decay SGD setup: a base SGD setup plus decay strength `λ`. -/
structure WeightDecaySGDSetup
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E]
    (S : Type*) [MeasurableSpace S]
    (Ω : Type*) [MeasurableSpace Ω] where
  toSGDSetup : SGDSetup E S Ω
  decay : ℝ

namespace WeightDecaySGDSetup

variable (setup : WeightDecaySGDSetup E S Ω)

/-- Effective stochastic gradient for weight decay:
`g_eff(w, ξ) = gradL(w, ξ) + decay • w`. -/
def effGradL (w : E) (s : S) : E :=
  setup.toSGDSetup.gradL w s + setup.decay • w

/-- Effective full gradient for weight decay:
`∇F_eff(w) = gradF(w) + decay • w`. -/
def effGradF (w : E) : E :=
  setup.toSGDSetup.gradF w + setup.decay • w

/-- Weight-decay SGD as plain SGD with effective gradients. -/
noncomputable def effectiveSGDSetup : SGDSetup E S Ω where
  w₀ := setup.toSGDSetup.w₀
  η := setup.toSGDSetup.η
  gradL := setup.effGradL
  gradF := setup.effGradF
  ξ := setup.toSGDSetup.ξ
  P := setup.toSGDSetup.P
  hP := setup.toSGDSetup.hP
  hξ_meas := setup.toSGDSetup.hξ_meas
  hξ_indep := setup.toSGDSetup.hξ_indep
  hξ_ident := setup.toSGDSetup.hξ_ident

/-- Sample distribution inherited from the base setup. -/
noncomputable def sampleDist : Measure S :=
  setup.toSGDSetup.sampleDist

/-- Weight-decay process (the process of the effective SGD setup). -/
noncomputable def process : ℕ → Ω → E :=
  setup.effectiveSGDSetup.process

omit [SecondCountableTopology E] in
@[simp] theorem process_zero :
    setup.process 0 = fun _ => setup.toSGDSetup.w₀ := by
  rfl

omit [SecondCountableTopology E] in
/-- Explicit one-step recursion for weight decay:
`w_{t+1} = w_t - η_t • (gradL(w_t, ξ_t) + decay • w_t)`. -/
@[simp] theorem process_succ (t : ℕ) :
    setup.process (t + 1) = fun ω =>
      setup.process t ω - (setup.toSGDSetup.η t) •
        (setup.toSGDSetup.gradL (setup.process t ω) (setup.toSGDSetup.ξ t ω)
          + setup.decay • setup.process t ω) := by
  rfl

/-- Measurability transfer from base stochastic gradient to effective weight-decay gradient.

Used in: `Weight Decay SGD` (Algorithms/WeightDecaySGD.lean, Step bridge — measurable effective oracle) -/
theorem measurable_effGradL
    (hgL : Measurable (Function.uncurry setup.toSGDSetup.gradL)) :
    Measurable (Function.uncurry setup.effGradL) := by
  simpa [WeightDecaySGDSetup.effGradL, Function.uncurry] using
    hgL.add (measurable_fst.const_smul setup.decay)

theorem measurable_effGradF
    (hgF : Measurable setup.toSGDSetup.gradF) :
    Measurable setup.effGradF := by
  simpa [WeightDecaySGDSetup.effGradF] using
    hgF.add (measurable_id.const_smul setup.decay)

omit [SecondCountableTopology E] in
/-- Lift unbiasedness from `gradL/gradF` to effective `effGradL/effGradF`.

Used in: `Weight Decay SGD` (Algorithms/WeightDecaySGD.lean, Step bridge — unbiased effective oracle) -/
theorem unbiased_effGrad_of_unbiased
    (hunb : IsUnbiased setup.toSGDSetup.gradL setup.toSGDSetup.gradF setup.sampleDist)
    (h_sample_prob : IsProbabilityMeasure setup.sampleDist)
    (h_intL : ∀ w, Integrable (setup.toSGDSetup.gradL w) setup.sampleDist) :
    IsUnbiased setup.effGradL setup.effGradF setup.sampleDist := by
  intro w
  letI : IsProbabilityMeasure setup.sampleDist := h_sample_prob
  calc
    ∫ s, setup.effGradL w s ∂setup.sampleDist
        = ∫ s, setup.toSGDSetup.gradL w s ∂setup.sampleDist
          + ∫ s, (setup.decay • w) ∂setup.sampleDist := by
            simp [WeightDecaySGDSetup.effGradL, integral_add, h_intL w]
    _ = setup.toSGDSetup.gradF w + setup.decay • w := by
          simp [hunb w, integral_const, probReal_univ]
    _ = setup.effGradF w := by
          simp [WeightDecaySGDSetup.effGradF]

/-- Bridge `WeightDecaySGDSetup` to Layer-1 `StochasticDescentHyps`. -/
noncomputable def wd_sgd_to_hyps
    (t : ℕ)
    (hgL : Measurable (Function.uncurry setup.effGradL))
    (hgF_meas : Measurable setup.effGradF)
    (hunb : IsUnbiased setup.effGradL setup.effGradF setup.sampleDist) :
    StochasticDescentHyps E S Ω :=
  sgd_to_hyps setup.effectiveSGDSetup t hgL hgF_meas hunb

/-- One-step convex progress for weight decay via Layer-1 meta-theorem. -/
theorem weight_decay_one_step_convex
    (t : ℕ) (f : E → ℝ) {σ : ℝ} (wStar : E)
    (hgL : Measurable (Function.uncurry setup.effGradL))
    (hgF_meas : Measurable setup.effGradF)
    (hunb : IsUnbiased setup.effGradL setup.effGradF setup.sampleDist)
    (hgrad : IsGradientOf' f setup.effGradF)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hvar : HasBoundedVariance' setup.effGradL setup.sampleDist σ)
    (hη_pos : 0 < setup.effectiveSGDSetup.η t)
    (h_intL : ∀ w, Integrable (setup.effGradL w) setup.sampleDist)
    (h_int_inner : Integrable (fun ω =>
        ⟪setup.process t ω - wStar,
          setup.effGradL (setup.process t ω) (setup.effectiveSGDSetup.ξ t ω)⟫_ℝ)
      setup.effectiveSGDSetup.P)
    (h_int_sq : Integrable (fun ω =>
        ‖setup.effGradL (setup.process t ω) (setup.effectiveSGDSetup.ξ t ω)‖ ^ 2)
      setup.effectiveSGDSetup.P)
    (h_int_norm_sq : Integrable (fun ω => ‖setup.process t ω - wStar‖ ^ 2)
      setup.effectiveSGDSetup.P)
    (h_int_ft : Integrable (fun ω => f (setup.process t ω)) setup.effectiveSGDSetup.P)
    (h_int_gF_inner : Integrable (fun ω =>
        ⟪setup.process t ω - wStar, setup.effGradF (setup.process t ω)⟫_ℝ)
      setup.effectiveSGDSetup.P) :
    ∫ ω, ‖(setup.process t ω
        - setup.effectiveSGDSetup.η t •
          setup.effGradL (setup.process t ω) (setup.effectiveSGDSetup.ξ t ω)) - wStar‖ ^ 2
      ∂setup.effectiveSGDSetup.P ≤
      ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.effectiveSGDSetup.P
      - 2 * setup.effectiveSGDSetup.η t * (∫ ω, f (setup.process t ω) ∂setup.effectiveSGDSetup.P - f wStar)
      + (setup.effectiveSGDSetup.η t) ^ 2 * σ ^ 2 := by
  simpa [WeightDecaySGDSetup.wd_sgd_to_hyps, WeightDecaySGDSetup.process] using
    (stochastic_descent_convex'
      (hyps := setup.wd_sgd_to_hyps t hgL hgF_meas hunb)
      (f := f) (σ := σ) (wStar := wStar)
      hgrad hconvex hvar hη_pos h_intL h_int_inner h_int_sq h_int_norm_sq h_int_ft h_int_gF_inner)

/-- Convex convergence rate for weight-decay SGD by reduction to existing SGD theorem. -/
theorem weight_decay_convergence_convex_v2
    (f : E → ℝ) {L : NNReal} {σ η : ℝ} (wStar : E)
    (hgrad : IsGradientOf f setup.effGradF)
    (hsmooth : IsLSmooth setup.effGradF L)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hvar : HasBoundedVariance setup.effGradL setup.sampleDist σ)
    (hunb : IsUnbiased setup.effGradL setup.effGradF setup.sampleDist)
    (hmin : IsMinimizer f wStar)
    (hη_pos : 0 < η) (hη : ∀ t, setup.effectiveSGDSetup.η t = η)
    (T : ℕ) (hT : 0 < T)
    (hgL : Measurable (Function.uncurry setup.effGradL))
    (h_intL : ∀ w, Integrable (setup.effGradL w) setup.sampleDist)
    (h_int_f : ∀ t, Integrable (fun ω => f (setup.process t ω)) setup.effectiveSGDSetup.P)
    (h_int_sq : ∀ t, Integrable (fun ω =>
        ‖setup.effGradL (setup.process t ω) (setup.effectiveSGDSetup.ξ t ω)‖ ^ 2)
      setup.effectiveSGDSetup.P)
    (h_int_norm_sq : ∀ t, Integrable (fun ω =>
        ‖setup.process t ω - wStar‖ ^ 2) setup.effectiveSGDSetup.P)
    (h_int_inner : ∀ t, Integrable (fun ω =>
        ⟪setup.process t ω - wStar,
          setup.effGradL (setup.process t ω) (setup.effectiveSGDSetup.ξ t ω)⟫_ℝ)
      setup.effectiveSGDSetup.P)
    (h_int_gF_inner : ∀ t, Integrable (fun ω =>
        ⟪setup.process t ω - wStar, setup.effGradF (setup.process t ω)⟫_ℝ)
      setup.effectiveSGDSetup.P) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        (∫ ω, f (setup.process t ω) ∂setup.effectiveSGDSetup.P - f wStar) ≤
      ‖setup.effectiveSGDSetup.w₀ - wStar‖ ^ 2 / (2 * η * T) + η * σ ^ 2 / 2 := by
  simpa [WeightDecaySGDSetup.process] using
    (sgd_convergence_convex_v2
      (setup := setup.effectiveSGDSetup) (f := f) (wStar := wStar)
      hgrad hsmooth hconvex hvar hunb hmin hη_pos hη T hT
      hgL h_intL h_int_f h_int_sq h_int_norm_sq h_int_inner h_int_gF_inner)

/-- Non-convex convergence rate for weight-decay SGD by reduction to existing SGD theorem. -/
theorem weight_decay_convergence_nonconvex_v2
    (f : E → ℝ) {L : NNReal} {σ η f_star : ℝ}
    (hgrad : IsGradientOf f setup.effGradF)
    (hsmooth : IsLSmooth setup.effGradF L)
    (hvar : HasBoundedVariance setup.effGradL setup.sampleDist σ)
    (hunb : IsUnbiased setup.effGradL setup.effGradF setup.sampleDist)
    (hlower : ∀ w, f_star ≤ f w)
    (hη_pos : 0 < η) (hη : ∀ t, setup.effectiveSGDSetup.η t = η)
    (T : ℕ) (hT : 0 < T)
    (hgL : Measurable (Function.uncurry setup.effGradL))
    (h_intL : ∀ w, Integrable (setup.effGradL w) setup.sampleDist)
    (h_int_f : ∀ t, Integrable (fun ω => f (setup.process t ω)) setup.effectiveSGDSetup.P)
    (h_int_sq : ∀ t, Integrable (fun ω =>
        ‖setup.effGradL (setup.process t ω) (setup.effectiveSGDSetup.ξ t ω)‖ ^ 2)
      setup.effectiveSGDSetup.P)
    (h_int_inner : ∀ t, Integrable (fun ω =>
        ⟪setup.effGradF (setup.process t ω),
          setup.effGradL (setup.process t ω) (setup.effectiveSGDSetup.ξ t ω)⟫_ℝ)
      setup.effectiveSGDSetup.P) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        ∫ ω, ‖setup.effGradF (setup.process t ω)‖ ^ 2 ∂setup.effectiveSGDSetup.P ≤
      2 * (f setup.effectiveSGDSetup.w₀ - f_star) / (η * T) + η * (L : ℝ) * σ ^ 2 := by
  simpa [WeightDecaySGDSetup.process] using
    (sgd_convergence_nonconvex_v2
      (setup := setup.effectiveSGDSetup) (f := f)
      hgrad hsmooth hvar hunb hlower hη_pos hη T hT
      hgL h_intL h_int_f h_int_sq h_int_inner)

/-- Strongly convex convergence rate for weight-decay SGD by reduction to existing SGD theorem. -/
theorem weight_decay_convergence_strongly_convex_v2
    (f : E → ℝ) {L : NNReal} {μ σ η : ℝ} (wStar : E)
    (hgrad : IsGradientOf f setup.effGradF)
    (hsmooth : IsLSmooth setup.effGradF L)
    (hsc : StrongConvexOn Set.univ μ f)
    (hvar : HasBoundedVariance setup.effGradL setup.sampleDist σ)
    (hunb : IsUnbiased setup.effGradL setup.effGradF setup.sampleDist)
    (hmin : IsMinimizer f wStar)
    (hμ_pos : 0 < μ) (hη_pos : 0 < η) (_hη_L : η ≤ 1 / (L : ℝ))
    (hημ : η * μ < 1) (hη : ∀ t, setup.effectiveSGDSetup.η t = η)
    (T : ℕ)
    (hgL : Measurable (Function.uncurry setup.effGradL))
    (h_intL : ∀ w, Integrable (setup.effGradL w) setup.sampleDist)
    (h_int_sq : ∀ t, Integrable (fun ω =>
        ‖setup.effGradL (setup.process t ω) (setup.effectiveSGDSetup.ξ t ω)‖ ^ 2)
      setup.effectiveSGDSetup.P)
    (h_int_norm_sq : ∀ t, Integrable (fun ω =>
        ‖setup.process t ω - wStar‖ ^ 2) setup.effectiveSGDSetup.P)
    (h_int_inner : ∀ t, Integrable (fun ω =>
        ⟪setup.process t ω - wStar,
          setup.effGradL (setup.process t ω) (setup.effectiveSGDSetup.ξ t ω)⟫_ℝ)
      setup.effectiveSGDSetup.P)
    (h_int_gF_inner : ∀ t, Integrable (fun ω =>
        ⟪setup.process t ω - wStar, setup.effGradF (setup.process t ω)⟫_ℝ)
      setup.effectiveSGDSetup.P) :
    ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.effectiveSGDSetup.P ≤
      (1 - η * μ) ^ T * ‖setup.effectiveSGDSetup.w₀ - wStar‖ ^ 2 + η * σ ^ 2 / μ := by
  simpa [WeightDecaySGDSetup.process] using
    (sgd_convergence_strongly_convex_v2
      (setup := setup.effectiveSGDSetup) (f := f) (wStar := wStar)
      hgrad hsmooth hsc hvar hunb hmin hμ_pos hη_pos _hη_L hημ hη T
      hgL h_intL h_int_sq h_int_norm_sq h_int_inner h_int_gF_inner)

end WeightDecaySGDSetup
