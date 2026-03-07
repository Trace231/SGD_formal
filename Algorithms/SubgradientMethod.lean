-- File: Algorithms/SubgradientMethod.lean
import Main
import Lib.Layer1.StochasticDescent

/-!
# Subgradient Method Convergence Proofs — Algorithm Layer

Layer: 2 (concrete algorithm proofs built on Layer 1 meta-theorems)

This file converts Subgradient Method's concrete setup into the abstract `StochasticDescentHyps`
and then calls the Layer 1 meta-theorems to prove convergence.

## Bridge strategy

The key bridge lemma `subgradient_to_hyps` converts `SubgradientSetup` at step `t` into
`StochasticDescentHyps` by discharging the two non-trivial obligations:

* **Independence** (`h_indep`): `sgdProcess_indepFun_xi` proves `process t ⊥ ξ t`
  because the iterate at step `t` depends only on `ξ₀, …, ξ_{t-1}`, while
  `ξ t` is independent of the past by `iIndepFun`.

* **Distribution** (`h_dist`): `IdentDistrib (ξ t) (ξ 0) P P` gives
  `Measure.map (ξ t) P = Measure.map (ξ 0) P = sampleDist`.

All other fields are direct projections from `SubgradientSetup`.

## Step equation

After the bridge, the meta-theorem conclusion uses
`hyps.wt ω - hyps.η • hyps.subgradL (hyps.wt ω) (hyps.ξt ω)`,
which equals `setup.process (t+1) ω` by `SubgradientSetup.process_succ`.
This rewrite is the only non-trivial glue needed in each convergence theorem.

## Current status

* `subgradient_to_hyps` — complete
* `subgradient_convergence_convex_v2` — complete (relies on Layer 1 `stochastic_subgradient_convex'`)
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {S : Type*} [MeasurableSpace S]
variable {Ω : Type*} [MeasurableSpace Ω]

-- ============================================================================
-- Subgradient Setup Structure
-- ============================================================================

/-- Complete Subgradient Method setup: initial point, learning rate schedule,
subgradient oracle, true subgradient, and IID random samples.
Used in: `subgradient_convergence_convex_v2` (setup parameter) -/
structure SubgradientSetup
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E]
    (S : Type*) [MeasurableSpace S]
    (Ω : Type*) [MeasurableSpace Ω] where
  w₀ : E
  η : ℕ → ℝ
  subgradL : E → S → E
  subgradF : E → E
  ξ : ℕ → Ω → S
  P : Measure Ω
  hP : IsProbabilityMeasure P
  hξ_meas : ∀ t, Measurable (ξ t)
  hξ_indep : iIndepFun (β := fun _ => S) ξ P
  hξ_ident : ∀ t, IdentDistrib (ξ t) (ξ 0) P P

namespace SubgradientSetup

variable (setup : SubgradientSetup E S Ω)

/-- The common distribution of each `ξ t` (pushforward of `P` through `ξ 0`).
Used in: `subgradient_to_hyps`, `subgradient_convergence_convex_v2` (variance hypothesis) -/
noncomputable def sampleDist : Measure S :=
  Measure.map (setup.ξ 0) setup.P

/-- The Subgradient Method random process derived from the setup.
Used in: all convergence theorems (iterate sequence) -/
noncomputable def process : ℕ → Ω → E :=
  sgdProcess setup.w₀ setup.η setup.subgradL setup.ξ

/-- `process` at step 0 equals the initial point everywhere.
Used in: `subgradient_convergence_convex_v2` (Algorithms/SubgradientMethod.lean, h_init — initial norm bound) -/
omit [SecondCountableTopology E] in
@[simp]
theorem process_zero : setup.process 0 = fun _ => setup.w₀ := rfl

/-- `process` at step `t+1` unfolds the SGD recursion by definition.
Used in: `subgradient_convergence_convex_v2` (Algorithms/SubgradientMethod.lean, hstep — step rewrite via simp) -/
omit [SecondCountableTopology E] in
@[simp]
theorem process_succ (t : ℕ) :
    setup.process (t + 1) = fun ω =>
      setup.process t ω - (setup.η t) • setup.subgradL (setup.process t ω) (setup.ξ t ω) :=
  rfl

end SubgradientSetup

-- ============================================================================
-- Bridge: SubgradientSetup at step t → StochasticDescentHyps
-- ============================================================================

/-- Convert a `SubgradientSetup` at step `t` into a `StochasticDescentHyps`.

Layer: 2 | Pure glue — no mathematical content beyond measurability/IID lemmas.

Key fields discharged:
* `h_indep`   := `sgdProcess_indepFun_xi` (process t ⊥ ξ t, from iIndepFun + filtration)
* `h_dist`    := `(hξ_ident t).map_eq` (ξ t has same distribution as ξ 0 = sampleDist)
* `h_wt_meas` := `sgdProcess_measurable` (each iterate is measurable random variable)

All remaining fields are direct projections from `SubgradientSetup`.
Used in: `subgradient_convergence_convex_v2` (per-step bridge) -/
noncomputable def subgradient_to_hyps
    (setup : SubgradientSetup E S Ω) (t : ℕ) (f : E → ℝ) (wStar : E)
    (hsubgrad_ineq : ∀ w s, f wStar ≥ f w + ⟪setup.subgradF w, wStar - w⟫_ℝ)
    (hgL : Measurable (Function.uncurry setup.subgradL))
    (hgF_meas : Measurable setup.subgradF)
    (hunb : IsUnbiased' setup.subgradL setup.subgradF setup.sampleDist) :
    StochasticDescentHyps E S Ω where
  P         := setup.P
  hP        := setup.hP
  ν         := setup.sampleDist
  wt        := setup.process t
  ξt        := setup.ξ t
  gradL     := setup.subgradL
  gradF     := setup.subgradF
  η         := setup.η t
  -- Independence: process t depends only on ξ 0, …, ξ (t-1), hence ⊥ ξ t
  h_indep   := sgdProcess_indepFun_xi setup.hξ_meas setup.hξ_indep hgL t
  -- Distribution: IdentDistrib (ξ t) (ξ 0) P P implies map(ξ t)P = sampleDist
  h_dist    := (setup.hξ_ident t).map_eq
  h_wt_meas := sgdProcess_measurable setup.hξ_meas hgL t
  h_ξt_meas := setup.hξ_meas t
  hgL       := hgL
  hgF_meas  := hgF_meas
  hunb      := hunb

-- ============================================================================
-- Convergence theorem for convex functions
-- ============================================================================

/-- **Convex Subgradient Method convergence** via `stochastic_subgradient_convex'`.

Proof outline:
1. `hstep`: at each t, build `hyps` via `subgradient_to_hyps`, call `stochastic_subgradient_convex'`
   to get `E[‖w_{t+1}−w*‖²] ≤ E[‖w_t−w*‖²] − 2η(E[f(w_t)]−f*) + η²G²`,
   then rewrite `process(t+1) = process t − η_t • subgradL` (rfl) and `η_t = η`.
2. `hsum`: telescope per-step bounds over t = 0..T−1.
3. Drop `‖w_T−w*‖² ≥ 0` and divide by 2ηT.
Used in: Non-smooth convex optimization convergence guarantees (e.g., SVM, L1-regularized problems) -/
theorem subgradient_convergence_convex_v2
    (setup : SubgradientSetup E S Ω) (f : E → ℝ) {G η : ℝ} (wStar : E)
    (hsubgrad_ineq : ∀ w s, f wStar ≥ f w + ⟪setup.subgradF w, wStar - w⟫_ℝ)
    (hvar : HasBoundedVariance' setup.subgradL setup.sampleDist G)
    (hunb : IsUnbiased' setup.subgradL setup.subgradF setup.sampleDist)
    (_hmin : IsMinimizer f wStar)
    (hη_pos : 0 < η) (hη : ∀ t, setup.η t = η)
    (T : ℕ) (hT : 0 < T)
    (hgL : Measurable (Function.uncurry setup.subgradL))
    (hgF_meas : Measurable setup.subgradF)
    (h_intL : ∀ w, Integrable (setup.subgradL w) setup.sampleDist)
    (h_int_f : ∀ t, Integrable (fun ω => f (setup.process t ω)) setup.P)
    (h_int_sq : ∀ t, Integrable (fun ω =>
        ‖setup.subgradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) setup.P)
    (h_int_norm_sq : ∀ t, Integrable (fun ω =>
        ‖setup.process t ω - wStar‖ ^ 2) setup.P)
    (h_int_inner : ∀ t, Integrable (fun ω =>
        ⟪setup.process t ω - wStar, setup.subgradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ)
      setup.P)
    (h_int_gF_inner : ∀ t, Integrable (fun ω =>
        ⟪setup.process t ω - wStar, setup.subgradF (setup.process t ω)⟫_ℝ) setup.P) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
      ‖setup.w₀ - wStar‖ ^ 2 / (2 * η * T) + η * G ^ 2 / 2 := by
  haveI := setup.hP
  calc
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)
      ≤ (1 / ↑T) * ((‖setup.w₀ - wStar‖ ^ 2 + ↑T * (η ^ 2 * G ^ 2)) / (2 * η)) := by
        -- PHASE 1: Per-step bound (defensive construction)
        have hstep : ∀ t < T,
            ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P ≤
              ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P
              - 2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)
              + η ^ 2 * G ^ 2 := fun t ht => by
          calc
            ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P
                = ∫ ω, ‖(setup.process t ω - setup.η t • setup.subgradL (setup.process t ω) (setup.ξ t ω)) - wStar‖ ^ 2 ∂setup.P := by
                  apply integral_congr_ae
                  exact Filter.Eventually.of_forall fun _ => by simp [SubgradientSetup.process_succ]
            _ ≤ ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P
                  - 2 * setup.η t * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)
                  + (setup.η t) ^ 2 * G ^ 2 := by
                  let hyps := subgradient_to_hyps setup t f wStar hsubgrad_ineq hgL hgF_meas hunb
                  exact stochastic_subgradient_convex' hyps f wStar hvar
                    (by linarith [hη t]) (h_int_sq t) (h_int_norm_sq t) (h_int_inner t) (h_int_f t)
            _ = ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P
                  - 2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)
                  + η ^ 2 * G ^ 2 := by rw [hη t]
        -- PHASE 2: Telescoping (explicit intermediate steps)
        set a : ℕ → ℝ := fun t => ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P
        set gap : ℕ → ℝ := fun t => ∫ ω, f (setup.process t ω) ∂setup.P - f wStar
        have h_rearr : ∀ t, t < T → 2 * η * gap t ≤ (a t - a (t + 1)) + η ^ 2 * G ^ 2 :=
          fun t ht => by simp only [a, gap]; linarith [hstep t ht]
        have h_sum_le := Finset.sum_le_sum fun t ht => h_rearr t (Finset.mem_range.mp ht)
        rw [← Finset.mul_sum] at h_sum_le
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h_sum_le
        have h_tele : ∑ t ∈ Finset.range T, (a t - a (t + 1)) = a 0 - a T := by
          simp_rw [show ∀ t, a t - a (t + 1) = -(a (t + 1) - a t) from fun t => by ring]
          rw [Finset.sum_neg_distrib, Finset.sum_range_sub]; ring
        rw [h_tele] at h_sum_le
        have h_init : a 0 = ‖setup.w₀ - wStar‖ ^ 2 := by
          simp [a, SubgradientSetup.process_zero, integral_const, probReal_univ]
        rw [h_init] at h_sum_le
        have h_norm_nonneg : 0 ≤ ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P :=
          integral_nonneg fun _ => sq_nonneg _
        linarith
    _ = ‖setup.w₀ - wStar‖ ^ 2 / (2 * η * ↑T) + η * G ^ 2 / 2 := by
        field_simp; ring