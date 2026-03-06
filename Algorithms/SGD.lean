import Main
import Lib.Layer1.StochasticDescent

/-!
# SGD Convergence Proofs — Algorithm Layer

Layer: 2 (concrete algorithm proofs built on Layer 1 meta-theorems)

This file converts SGD's concrete setup into the abstract `StochasticDescentHyps`
and then calls the Layer 1 meta-theorems to prove convergence.

## Bridge strategy

The key bridge lemma `sgd_to_hyps` converts `SGDSetup` at step `t` into
`StochasticDescentHyps` by discharging the two non-trivial obligations:

* **Independence** (`h_indep`): `sgdProcess_indepFun_xi` proves `process t ⊥ ξ t`
  because the SGD iterate at step `t` depends only on `ξ₀, …, ξ_{t-1}`, while
  `ξ t` is independent of the past by `iIndepFun`.

* **Distribution** (`h_dist`): `IdentDistrib (ξ t) (ξ 0) P P` gives
  `Measure.map (ξ t) P = Measure.map (ξ 0) P = sampleDist`.

All other fields are direct projections from `SGDSetup`.

## Step equation

After the bridge, the meta-theorem conclusion uses
`hyps.wt ω - hyps.η • hyps.gradL (hyps.wt ω) (hyps.ξt ω)`,
which equals `setup.process (t+1) ω` by `SGDSetup.process_succ`.
This rewrite is the only non-trivial glue needed in each convergence theorem.

## Current status

* `sgd_to_hyps` — complete
* `sgd_convergence_nonconvex`, `sgd_convergence_convex`,
  `sgd_convergence_strongly_convex` — to be implemented (next step)
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {S : Type*} [MeasurableSpace S]
variable {Ω : Type*} [MeasurableSpace Ω]

-- ============================================================================
-- Bridge: SGDSetup at step t → StochasticDescentHyps
-- ============================================================================

/-- Convert a `SGDSetup` at step `t` into a `StochasticDescentHyps`.

Layer: 2 | This is pure glue — no mathematical content beyond what the
SGD measurability and IID lemmas already provide.

Key fields discharged:
* `h_indep`   := `sgdProcess_indepFun_xi` (process t ⊥ ξ t, from iIndepFun + filtration)
* `h_dist`    := `(hξ_ident t).map_eq` (ξ t has the same distribution as ξ 0 = sampleDist)
* `h_wt_meas` := `sgdProcess_measurable` (each iterate is a measurable random variable)

All remaining fields are direct projections from `SGDSetup`. -/
noncomputable def sgd_to_hyps
    (setup : SGDSetup E S Ω) (t : ℕ)
    (hgL : Measurable (Function.uncurry setup.gradL))
    (hgF_meas : Measurable setup.gradF)
    (hunb : IsUnbiased setup.gradL setup.gradF setup.sampleDist) :
    StochasticDescentHyps E S Ω where
  P         := setup.P
  hP        := setup.hP
  ν         := setup.sampleDist
  wt        := setup.process t
  ξt        := setup.ξ t
  gradL     := setup.gradL
  gradF     := setup.gradF
  η         := setup.η t
  -- Independence: process t depends only on ξ 0, …, ξ (t-1), hence ⊥ ξ t
  h_indep   := sgdProcess_indepFun_xi setup.hξ_meas setup.hξ_indep hgL t
  -- Distribution: IdentDistrib (ξ t) (ξ 0) P P implies map(ξ t)P = sampleDist
  h_dist    := (setup.hξ_ident t).map_eq
  h_wt_meas := sgdProcess_measurable setup.hξ_meas hgL t
  h_ξt_meas := setup.hξ_meas t
  hgL       := hgL
  hgF_meas  := hgF_meas
  -- IsUnbiased and IsUnbiased' are definitionally equal (same body); Lean accepts directly
  hunb      := hunb

/-- The step equation: the meta-theorem's output form equals `setup.process (t+1)`.

This is the only rewrite needed to connect Layer1 conclusions to SGD statements. -/
lemma sgd_step_eq (setup : SGDSetup E S Ω) (t : ℕ)
    (hgL : Measurable (Function.uncurry setup.gradL))
    (hgF_meas : Measurable setup.gradF)
    (hunb : IsUnbiased setup.gradL setup.gradF setup.sampleDist) :
    let hyps := sgd_to_hyps setup t hgL hgF_meas hunb
    ∀ ω, hyps.wt ω - hyps.η • hyps.gradL (hyps.wt ω) (hyps.ξt ω) =
      setup.process (t + 1) ω := by
  intro hyps ω
  simp only [hyps, sgd_to_hyps, SGDSetup.process_succ]

-- ============================================================================
-- Convergence theorems (to be implemented in the next step)
-- ============================================================================

/-- **Non-convex SGD convergence** (placeholder — calls stochastic_descent_nonconvex'). -/
theorem sgd_convergence_nonconvex_v2
    (setup : SGDSetup E S Ω) (f : E → ℝ) {L : NNReal} {σ η f_star : ℝ}
    (hgrad : IsGradientOf f setup.gradF)
    (hsmooth : IsLSmooth setup.gradF L)
    (hvar : HasBoundedVariance setup.gradL setup.sampleDist σ)
    (hunb : IsUnbiased setup.gradL setup.gradF setup.sampleDist)
    (hlower : ∀ w, f_star ≤ f w)
    (hη_pos : 0 < η) (hη : ∀ t, setup.η t = η)
    (T : ℕ) (hT : 0 < T)
    (hgL : Measurable (Function.uncurry setup.gradL))
    (h_intL : ∀ w, Integrable (setup.gradL w) setup.sampleDist)
    (h_int_f : ∀ t, Integrable (fun ω => f (setup.process t ω)) setup.P)
    (h_int_sq : ∀ t, Integrable (fun ω =>
        ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) setup.P)
    (h_int_gF_sq : ∀ t, Integrable (fun ω =>
        ‖setup.gradF (setup.process t ω)‖ ^ 2) setup.P)
    (h_int_inner : ∀ t, Integrable (fun ω =>
        ⟪setup.gradF (setup.process t ω), setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ)
      setup.P) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        ∫ ω, ‖setup.gradF (setup.process t ω)‖ ^ 2 ∂setup.P ≤
      2 * (f setup.w₀ - f_star) / (η * T) + η * (L : ℝ) * σ ^ 2 := by
  sorry

/-- **Convex SGD convergence** (placeholder — calls stochastic_descent_convex'). -/
theorem sgd_convergence_convex_v2
    (setup : SGDSetup E S Ω) (f : E → ℝ) {L : NNReal} {σ η : ℝ} (wStar : E)
    (hgrad : IsGradientOf f setup.gradF)
    (hsmooth : IsLSmooth setup.gradF L)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hvar : HasBoundedVariance setup.gradL setup.sampleDist σ)
    (hunb : IsUnbiased setup.gradL setup.gradF setup.sampleDist)
    (hmin : IsMinimizer f wStar)
    (hη_pos : 0 < η) (hη : ∀ t, setup.η t = η)
    (T : ℕ) (hT : 0 < T)
    (hgL : Measurable (Function.uncurry setup.gradL))
    (h_intL : ∀ w, Integrable (setup.gradL w) setup.sampleDist)
    (h_int_f : ∀ t, Integrable (fun ω => f (setup.process t ω)) setup.P)
    (h_int_sq : ∀ t, Integrable (fun ω =>
        ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) setup.P)
    (h_int_norm_sq : ∀ t, Integrable (fun ω =>
        ‖setup.process t ω - wStar‖ ^ 2) setup.P)
    (h_int_inner : ∀ t, Integrable (fun ω =>
        ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ)
      setup.P)
    (h_int_gF_inner : ∀ t, Integrable (fun ω =>
        ⟪setup.process t ω - wStar, setup.gradF (setup.process t ω)⟫_ℝ) setup.P) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
      ‖setup.w₀ - wStar‖ ^ 2 / (2 * η * T) + η * σ ^ 2 / 2 := by
  sorry

/-- **Strongly convex SGD convergence** (placeholder — calls stochastic_descent_strongly_convex'). -/
theorem sgd_convergence_strongly_convex_v2
    (setup : SGDSetup E S Ω) (f : E → ℝ) {L : NNReal} {μ σ η : ℝ} (wStar : E)
    (hgrad : IsGradientOf f setup.gradF)
    (hsmooth : IsLSmooth setup.gradF L)
    (hsc : StrongConvexOn Set.univ μ f)
    (hvar : HasBoundedVariance setup.gradL setup.sampleDist σ)
    (hunb : IsUnbiased setup.gradL setup.gradF setup.sampleDist)
    (hmin : IsMinimizer f wStar)
    (hμ_pos : 0 < μ) (hη_pos : 0 < η) (hη_L : η ≤ 1 / (L : ℝ))
    (hημ : η * μ < 1) (hη : ∀ t, setup.η t = η)
    (T : ℕ)
    (hgL : Measurable (Function.uncurry setup.gradL))
    (h_intL : ∀ w, Integrable (setup.gradL w) setup.sampleDist)
    (h_int_sq : ∀ t, Integrable (fun ω =>
        ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) setup.P)
    (h_int_norm_sq : ∀ t, Integrable (fun ω =>
        ‖setup.process t ω - wStar‖ ^ 2) setup.P)
    (h_int_inner : ∀ t, Integrable (fun ω =>
        ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ)
      setup.P)
    (h_int_gF_inner : ∀ t, Integrable (fun ω =>
        ⟪setup.process t ω - wStar, setup.gradF (setup.process t ω)⟫_ℝ) setup.P) :
    ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P ≤
      (1 - η * μ) ^ T * ‖setup.w₀ - wStar‖ ^ 2 + η * σ ^ 2 / μ := by
  sorry
