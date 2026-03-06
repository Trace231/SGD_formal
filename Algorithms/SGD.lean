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

/-- **Non-convex SGD convergence** via Layer1 meta-theorem `stochastic_descent_nonconvex'`.

Proof outline:
1. `hstep`: for each t, convert `SGDSetup` to `StochasticDescentHyps` via `sgd_to_hyps`,
   call the meta-theorem, rewrite `process(t+1) = process t − η t • gradL` (process_succ),
   then substitute `η t = η`.
2. `hsum`: telescope the per-step bounds → η·Σ‖∇f‖² ≤ (f(w₀) − E[f(w_T)]) + T·η²Lσ²/2.
3. `hlb`: E[f(w_T)] ≥ f* (f is bounded below).
4. Algebraic rearrangement and division by η·T. -/
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
    (h_int_inner : ∀ t, Integrable (fun ω =>
        ⟪setup.gradF (setup.process t ω), setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ)
      setup.P) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        ∫ ω, ‖setup.gradF (setup.process t ω)‖ ^ 2 ∂setup.P ≤
      2 * (f setup.w₀ - f_star) / (η * T) + η * (L : ℝ) * σ ^ 2 := by
  haveI := setup.hP
  -- ----------------------------------------------------------------
  -- Step 1: per-step descent bound via bridge + meta-theorem
  -- ----------------------------------------------------------------
  have hstep : ∀ t < T,
      ∫ ω, f (setup.process (t + 1) ω) ∂setup.P ≤
        ∫ ω, f (setup.process t ω) ∂setup.P
        - η * ∫ ω, ‖setup.gradF (setup.process t ω)‖ ^ 2 ∂setup.P
        + η ^ 2 * (L : ℝ) * σ ^ 2 / 2 := fun t _ => by
    -- process(t+1) = process t − η_t • gradL  (by process_succ)
    -- apply meta-theorem via bridge, then substitute η_t = η
    calc ∫ ω, f (setup.process (t + 1) ω) ∂setup.P
        = ∫ ω, f (setup.process t ω -
              setup.η t • setup.gradL (setup.process t ω) (setup.ξ t ω)) ∂setup.P := by
            -- process_succ is proved by rfl (definitional), so the integrals are equal
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun _ => rfl
      _ ≤ ∫ ω, f (setup.process t ω) ∂setup.P
            - setup.η t * ∫ ω, ‖setup.gradF (setup.process t ω)‖ ^ 2 ∂setup.P
            + (setup.η t) ^ 2 * (L : ℝ) * σ ^ 2 / 2 :=
            -- Fields of sgd_to_hyps reduce definitionally to SGDSetup projections,
            -- so the meta-theorem's conclusion matches this form exactly.
            stochastic_descent_nonconvex'
              (sgd_to_hyps setup t hgL (hsmooth.continuous.measurable) hunb)
              f hgrad hsmooth hvar h_intL
              (h_int_f t) (h_int_f (t + 1)) (h_int_inner t) (h_int_sq t)
      _ = ∫ ω, f (setup.process t ω) ∂setup.P
            - η * ∫ ω, ‖setup.gradF (setup.process t ω)‖ ^ 2 ∂setup.P
            + η ^ 2 * (L : ℝ) * σ ^ 2 / 2 := by rw [hη t]
  -- ----------------------------------------------------------------
  -- Step 2: sum and telescope
  -- ----------------------------------------------------------------
  have hsum : η * ∑ t ∈ Finset.range T,
        ∫ ω, ‖setup.gradF (setup.process t ω)‖ ^ 2 ∂setup.P ≤
      f setup.w₀ - ∫ ω, f (setup.process T ω) ∂setup.P +
        (T : ℝ) * (η ^ 2 * (L : ℝ) * σ ^ 2 / 2) := by
    set a := fun t => ∫ ω, f (setup.process t ω) ∂setup.P
    set b := fun t => ∫ ω, ‖setup.gradF (setup.process t ω)‖ ^ 2 ∂setup.P
    have h_rearr : ∀ t, t < T → η * b t ≤ (a t - a (t + 1)) + η ^ 2 * (L : ℝ) * σ ^ 2 / 2 :=
      fun t ht => by simp only [a, b]; linarith [hstep t ht]
    have h_sum_le := Finset.sum_le_sum (fun t ht => h_rearr t (Finset.mem_range.mp ht))
    rw [← Finset.mul_sum] at h_sum_le
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h_sum_le
    have h_tele : ∑ t ∈ Finset.range T, (a t - a (t + 1)) = a 0 - a T := by
      simp_rw [show ∀ t, a t - a (t + 1) = -(a (t + 1) - a t) from fun t => by ring]
      rw [Finset.sum_neg_distrib, Finset.sum_range_sub]; ring
    rw [h_tele] at h_sum_le
    have h_init : a 0 = f setup.w₀ := by
      simp [a, SGDSetup.process_zero, integral_const, probReal_univ]
    rw [h_init] at h_sum_le; linarith
  -- ----------------------------------------------------------------
  -- Step 3: E[f(w_T)] ≥ f*
  -- ----------------------------------------------------------------
  have hlb : f_star ≤ ∫ ω, f (setup.process T ω) ∂setup.P := by
    calc f_star = ∫ _, f_star ∂setup.P := by
              rw [integral_const, smul_eq_mul, probReal_univ, one_mul]
      _ ≤ ∫ ω, f (setup.process T ω) ∂setup.P := by
              apply integral_mono (integrable_const _) (h_int_f T)
              intro ω; exact hlower _
  -- ----------------------------------------------------------------
  -- Step 4: algebraic rearrangement and division by η·T
  -- ----------------------------------------------------------------
  have hT_pos : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hηT_pos : (0 : ℝ) < η * T := mul_pos hη_pos hT_pos
  have h_comb : η * ∑ t ∈ Finset.range T,
        ∫ ω, ‖setup.gradF (setup.process t ω)‖ ^ 2 ∂setup.P ≤
      (f setup.w₀ - f_star) + ↑T * (η ^ 2 * ↑↑L * σ ^ 2 / 2) := by linarith
  have h_weak : η * ∑ t ∈ Finset.range T,
        ∫ ω, ‖setup.gradF (setup.process t ω)‖ ^ 2 ∂setup.P ≤
      2 * (f setup.w₀ - f_star) + ↑T * (η ^ 2 * ↑↑L * σ ^ 2) := by
    have h_fstar : (0 : ℝ) ≤ f setup.w₀ - f_star := by linarith [hlower setup.w₀]
    have h_noise : (0 : ℝ) ≤ ↑T * (η ^ 2 * ↑↑L * σ ^ 2 / 2) := by positivity
    linarith
  have h_div : ∑ t ∈ Finset.range T,
        ∫ ω, ‖setup.gradF (setup.process t ω)‖ ^ 2 ∂setup.P ≤
      (2 * (f setup.w₀ - f_star) + ↑T * (η ^ 2 * ↑↑L * σ ^ 2)) / η := by
    rw [le_div_iff₀ hη_pos]; linarith
  calc (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
          ∫ ω, ‖setup.gradF (setup.process t ω)‖ ^ 2 ∂setup.P
      ≤ (1 / ↑T) * ((2 * (f setup.w₀ - f_star) + ↑T * (η ^ 2 * ↑↑L * σ ^ 2)) / η) :=
          mul_le_mul_of_nonneg_left h_div (by positivity : (0 : ℝ) ≤ 1 / ↑T)
    _ = 2 * (f setup.w₀ - f_star) / (η * ↑T) + η * ↑↑L * σ ^ 2 := by field_simp

/-- **Convex SGD convergence** via `stochastic_descent_convex'`.

Proof outline:
1. `hstep`: at each t, build `hyps` via `sgd_to_hyps`, call `stochastic_descent_convex'`
   to get `E[‖w_{t+1}−w*‖²] ≤ E[‖w_t−w*‖²] − 2η(E[f(w_t)]−f*) + η²σ²`,
   then rewrite `process(t+1) = process t − η_t • gradL` (rfl) and `η_t = η`.
2. `hsum`: telescope the per-step bounds over t = 0..T−1.
3. Drop `‖w_T−w*‖² ≥ 0` and divide by 2ηT. -/
theorem sgd_convergence_convex_v2
    (setup : SGDSetup E S Ω) (f : E → ℝ) {L : NNReal} {σ η : ℝ} (wStar : E)
    (hgrad : IsGradientOf f setup.gradF)
    (hsmooth : IsLSmooth setup.gradF L)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hvar : HasBoundedVariance setup.gradL setup.sampleDist σ)
    (hunb : IsUnbiased setup.gradL setup.gradF setup.sampleDist)
    (_hmin : IsMinimizer f wStar)
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
  haveI := setup.hP
  -- ----------------------------------------------------------------
  -- Step 1: per-step norm-squared descent via bridge + meta-theorem
  -- ----------------------------------------------------------------
  have hstep : ∀ t < T,
      ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P ≤
        ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P
        - 2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)
        + η ^ 2 * σ ^ 2 := fun t _ => by
    calc ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P
        = ∫ ω, ‖(setup.process t ω -
              setup.η t • setup.gradL (setup.process t ω) (setup.ξ t ω)) - wStar‖ ^ 2
            ∂setup.P := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun _ => rfl
      _ ≤ ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P
            - 2 * setup.η t * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)
            + (setup.η t) ^ 2 * σ ^ 2 :=
            stochastic_descent_convex'
              (sgd_to_hyps setup t hgL (hsmooth.continuous.measurable) hunb)
              f wStar hgrad hconvex hvar
              (by show 0 < setup.η t; linarith [hη t])
              h_intL
              (h_int_inner t) (h_int_sq t) (h_int_norm_sq t) (h_int_f t) (h_int_gF_inner t)
      _ = ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P
            - 2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)
            + η ^ 2 * σ ^ 2 := by rw [hη t]
  -- ----------------------------------------------------------------
  -- Step 2: sum and telescope → 2η · Σ(gap) ≤ ‖w₀−w*‖² − ‖w_T−w*‖² + T·η²σ²
  -- ----------------------------------------------------------------
  have hsum : 2 * η * ∑ t ∈ Finset.range T,
        (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
      ‖setup.w₀ - wStar‖ ^ 2 -
        ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P +
        (T : ℝ) * (η ^ 2 * σ ^ 2) := by
    set a := fun t => ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P
    set gap := fun t => ∫ ω, f (setup.process t ω) ∂setup.P - f wStar
    have h_rearr : ∀ t, t < T → 2 * η * gap t ≤ (a t - a (t + 1)) + η ^ 2 * σ ^ 2 :=
      fun t ht => by simp only [a, gap]; linarith [hstep t ht]
    have h_sum_le := Finset.sum_le_sum (fun t ht => h_rearr t (Finset.mem_range.mp ht))
    rw [← Finset.mul_sum] at h_sum_le
    simp only [Finset.sum_add_distrib, Finset.sum_const,
               Finset.card_range, nsmul_eq_mul] at h_sum_le
    have h_tele : ∑ t ∈ Finset.range T, (a t - a (t + 1)) = a 0 - a T := by
      simp_rw [show ∀ t, a t - a (t + 1) = -(a (t + 1) - a t) from fun t => by ring]
      rw [Finset.sum_neg_distrib, Finset.sum_range_sub]; ring
    rw [h_tele] at h_sum_le
    have h_init : a 0 = ‖setup.w₀ - wStar‖ ^ 2 := by
      simp [a, SGDSetup.process, sgdProcess, integral_const, probReal_univ]
    rw [h_init] at h_sum_le; linarith
  -- ----------------------------------------------------------------
  -- Step 3: drop ‖w_T − w*‖² ≥ 0 and divide by 2ηT
  -- ----------------------------------------------------------------
  have h_norm_nonneg : 0 ≤ ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P :=
    integral_nonneg fun ω => sq_nonneg _
  have h_drop : 2 * η * ∑ t ∈ Finset.range T,
        (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
      ‖setup.w₀ - wStar‖ ^ 2 + (T : ℝ) * (η ^ 2 * σ ^ 2) := by linarith
  have hT_pos : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hη2_pos : (0 : ℝ) < 2 * η := by linarith
  rw [one_div, inv_mul_le_iff₀ hT_pos]
  have h_rhs : ↑T * (‖setup.w₀ - wStar‖ ^ 2 / (2 * η * ↑T) + η * σ ^ 2 / 2) =
      (‖setup.w₀ - wStar‖ ^ 2 + ↑T * (η ^ 2 * σ ^ 2)) / (2 * η) := by field_simp
  rw [h_rhs, le_div_iff₀ hη2_pos]; linarith

/-- **Strongly convex SGD convergence** via `stochastic_descent_strongly_convex'`.

Proof outline:
- Induction on T.
- Base (T=0): `process 0 = w₀` (definitional), integral of a constant = constant.
- Step (T+1): call `stochastic_descent_strongly_convex'` via `sgd_to_hyps` to get
  `E[‖w_{T+1}−w*‖²] ≤ (1−ημ)·E[‖w_T−w*‖²] + η²σ²`, then chain with `ih` via `gcongr`.
  The noise accumulates as a geometric series: the identity
  `(1−ημ)·(ησ²/μ) + η²σ² = ησ²/μ` closes the induction. -/
theorem sgd_convergence_strongly_convex_v2
    (setup : SGDSetup E S Ω) (f : E → ℝ) {L : NNReal} {μ σ η : ℝ} (wStar : E)
    (hgrad : IsGradientOf f setup.gradF)
    (hsmooth : IsLSmooth setup.gradF L)
    (hsc : StrongConvexOn Set.univ μ f)
    (hvar : HasBoundedVariance setup.gradL setup.sampleDist σ)
    (hunb : IsUnbiased setup.gradL setup.gradF setup.sampleDist)
    (hmin : IsMinimizer f wStar)
    (hμ_pos : 0 < μ) (hη_pos : 0 < η) (_hη_L : η ≤ 1 / (L : ℝ))
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
  haveI := setup.hP
  have h_nonneg : 0 ≤ 1 - η * μ := by linarith
  induction T with
  | zero =>
    -- process 0 = w₀ (definitional); integral of constant = constant on prob. space
    simp only [SGDSetup.process, sgdProcess, pow_zero, one_mul]
    rw [integral_const, smul_eq_mul, probReal_univ, one_mul]
    linarith [div_nonneg (mul_nonneg (le_of_lt hη_pos) (sq_nonneg σ)) (le_of_lt hμ_pos)]
  | succ T ih =>
    -- Per-step contraction at step T via bridge + meta-theorem
    have hstep : ∫ ω, ‖setup.process (T + 1) ω - wStar‖ ^ 2 ∂setup.P ≤
        (1 - η * μ) * ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P
        + η ^ 2 * σ ^ 2 := by
      calc ∫ ω, ‖setup.process (T + 1) ω - wStar‖ ^ 2 ∂setup.P
          = ∫ ω, ‖(setup.process T ω -
                setup.η T • setup.gradL (setup.process T ω) (setup.ξ T ω)) - wStar‖ ^ 2
              ∂setup.P := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun _ => rfl
        _ ≤ (1 - setup.η T * μ) * ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P
              + (setup.η T) ^ 2 * σ ^ 2 :=
              -- μ σ are implicit, inferred from hsc/hvar; wStar is first explicit arg after f
              stochastic_descent_strongly_convex'
                (sgd_to_hyps setup T hgL (hsmooth.continuous.measurable) hunb)
                f wStar hgrad hsc hvar hmin hμ_pos
                (by show 0 < setup.η T; linarith [hη T])
                h_intL
                (h_int_inner T) (h_int_sq T) (h_int_norm_sq T) (h_int_gF_inner T)
        _ = (1 - η * μ) * ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P
              + η ^ 2 * σ ^ 2 := by rw [hη T]
    -- Noise term: (1−ημ)·(ησ²/μ) + η²σ² = ησ²/μ (geometric series identity)
    have hkey : (1 - η * μ) * ((1 - η * μ) ^ T * ‖setup.w₀ - wStar‖ ^ 2 + η * σ ^ 2 / μ) +
        η ^ 2 * σ ^ 2 = (1 - η * μ) ^ (T + 1) * ‖setup.w₀ - wStar‖ ^ 2 + η * σ ^ 2 / μ := by
      have hne : μ ≠ 0 := ne_of_gt hμ_pos
      field_simp; ring
    -- Chain: per-step bound → induction hypothesis → closed form
    calc ∫ ω, ‖setup.process (T + 1) ω - wStar‖ ^ 2 ∂setup.P
        ≤ (1 - η * μ) * ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P
            + η ^ 2 * σ ^ 2 := hstep
      _ ≤ (1 - η * μ) * ((1 - η * μ) ^ T * ‖setup.w₀ - wStar‖ ^ 2 + η * σ ^ 2 / μ)
            + η ^ 2 * σ ^ 2 := by gcongr
      _ = (1 - η * μ) ^ (T + 1) * ‖setup.w₀ - wStar‖ ^ 2 + η * σ ^ 2 / μ := hkey
