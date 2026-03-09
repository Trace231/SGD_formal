import Main
import Lib.Layer0.IndepExpect
import Lib.Glue.Algebra
import Mathlib.Analysis.Convex.Subdifferential

/-!
# Stochastic Subgradient Method for Convex Non-Smooth Optimization (Archetype B)

Layer: 2 (concrete algorithm proofs built directly on Layer 0/Glue infrastructure)

This file formalizes the stochastic subgradient method for convex non-smooth optimization.
Although the update rule syntactically matches SGD (`$w_{t+1} = w_t - \eta \cdot g_t$`),
the oracle semantics differ fundamentally: `gradL` provides subgradients satisfying
`$\text{gradL}(w, s) \in \partial f(w)$` (not unbiased estimates of a smooth gradient).
Therefore, the proof cannot reuse Layer 1 meta-theorems (which require `gradF` and unbiasedness)
and instead derives the one-step bound directly using the pointwise subgradient inequality.

## Main results

* `SubgradientSetup` — algorithm data and IID assumptions (no `gradF` field)
* `process` — iterate recursion (alias of `sgdProcess` from `Main.lean`)
* `subgradient_convergence_convex` — $O(1/\sqrt{T})$ convergence rate

## Archetype

B — novel proof structure despite identical update syntax.
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {S : Type*} [MeasurableSpace S]
variable {Ω : Type*} [MeasurableSpace Ω]

-- ============================================================================
-- Subgradient Setup (no `gradF` field)
-- ============================================================================

/-- Complete subgradient method setup: initial point, step size schedule,
stochastic subgradient oracle, and IID random samples.

Note: Contains **no `gradF` field** (unlike `SGDSetup`), reflecting the absence of
a true gradient for non-smooth functions. Subgradient membership is enforced via
hypothesis `hsubgrad` in the convergence theorem.
Used in: `subgradient_convergence_convex` (this file, main theorem) -/
structure SubgradientSetup where
  w₀ : E
  η : ℕ → ℝ
  gradL : E → S → E
  ξ : ℕ → Ω → S
  P : Measure Ω
  hP : IsProbabilityMeasure P
  hξ_meas : ∀ t, Measurable (ξ t)
  hξ_indep : iIndepFun (β := fun _ => S) ξ P
  hξ_ident : ∀ t, IdentDistrib (ξ t) (ξ 0) P P

namespace SubgradientSetup

variable (setup : SubgradientSetup E S Ω)

/-- The common distribution of each `ξ t` (pushforward of `P` through `ξ 0`).
Used in: `subgradient_convergence_convex` (variance bound) -/
noncomputable def sampleDist : Measure S :=
  Measure.map (setup.ξ 0) setup.P

/-- The stochastic subgradient process.

Definitionally equal to `sgdProcess` from `Main.lean`; we reuse the same recursion.
Used in: all convergence and infrastructure lemmas -/
noncomputable def process : ℕ → Ω → E :=
  sgdProcess setup.w₀ setup.η setup.gradL setup.ξ

@[simp]
theorem process_zero : setup.process 0 = fun _ => setup.w₀ := rfl

@[simp]
theorem process_succ (t : ℕ) :
    setup.process (t + 1) = fun ω =>
      setup.process t ω - (setup.η t) • setup.gradL (setup.process t ω) (setup.ξ t ω) := rfl

end SubgradientSetup

-- ============================================================================
-- Infrastructure Lemmas (thin wrappers over Main.lean's SGD infrastructure)
-- ============================================================================

/-- Measurability of the subgradient process.

This is a thin wrapper over `sgdProcess_measurable` from `Main.lean`.
Used in: `subgradient_convergence_convex` (measurability of `process t`) -/
theorem subgradientProcess_measurable {setup : SubgradientSetup E S Ω}
    (hgL : Measurable (Function.uncurry setup.gradL)) (t : ℕ) :
    Measurable (setup.process t) := by
  unfold SubgradientSetup.process
  exact sgdProcess_measurable setup.hξ_meas hgL t

/-- Adaptedness of the subgradient process to the natural filtration.

This is a thin wrapper over `sgdProcess_adapted` from `Main.lean`.
Used in: independence proofs (via `subgradientProcess_indepFun_xi`) -/
theorem subgradientProcess_adapted {setup : SubgradientSetup E S Ω}
    (hgL : Measurable (Function.uncurry setup.gradL)) :
    Adapted (sgdFiltration setup.ξ setup.hξ_meas) (fun t => setup.process t) := by
  unfold SubgradientSetup.process
  exact sgdProcess_adapted setup.hξ_meas hgL

/-- Independence of `process t` from `ξ t`.

This is a thin wrapper over `sgdProcess_indepFun_xi` from `Main.lean`.
Used in: `subgradient_convergence_convex` (variance bound step) -/
theorem subgradientProcess_indepFun_xi {setup : SubgradientSetup E S Ω}
    (hgL : Measurable (Function.uncurry setup.gradL)) (t : ℕ) :
    IndepFun (setup.process t) (setup.ξ t) setup.P := by
  unfold SubgradientSetup.process
  exact sgdProcess_indepFun_xi setup.hξ_meas setup.hξ_indep hgL t

-- ============================================================================
-- Convergence Theorem
-- ============================================================================

/-- **Stochastic subgradient method convergence for convex non-smooth functions**.

Archetype B proof: uses subgradient inequality directly, bypassing Layer 1 meta-theorems.

Conclusion:
`$$\frac{1}{T} \sum_{t<T} \big(\mathbb{E}[f(w_t)] - f(w^*)\big)
   \le \frac{\|w_0 - w^*\|^2}{2\eta T} + \frac{\eta G^2}{2}$$`

Proof outline:
1. Pointwise norm expansion (`norm_sq_sgd_step`)
2. Subgradient inequality (`mem_subdifferential_iff`)
3. Integrate and apply variance bound (`expectation_norm_sq_gradL_bound`)
4. Telescope over t < T

Used in: Top-level algorithm validation -/
theorem subgradient_convergence_convex
    (setup : SubgradientSetup E S Ω) (f : E → ℝ) (G η : ℝ) (wStar : E)
    (hsubgrad : ∀ w s, setup.gradL w s ∈ subdifferential ℝ f w)
    (hbounded : ∀ w s, ‖setup.gradL w s‖ ≤ G)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hη_pos : 0 < η) (hη : ∀ t, setup.η t = η)
    (T : ℕ) (hT : 0 < T)
    (hgL : Measurable (Function.uncurry setup.gradL))
    (h_int_norm_sq : ∀ t, Integrable (fun ω => ‖setup.process t ω - wStar‖ ^ 2) setup.P)
    (h_int_f : ∀ t, Integrable (fun ω => f (setup.process t ω)) setup.P)
    (h_int_sq : ∀ t, Integrable (fun ω =>
        ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) setup.P) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
      ‖setup.w₀ - wStar‖ ^ 2 / (2 * η * T) + η * G ^ 2 / 2 := by
  haveI := setup.hP
  -- Derive bounded variance from pointwise norm bound
  have hvar : HasBoundedVariance' setup.gradL setup.sampleDist G := by
    intro w
    -- Integrability component (Convention §1)
    have h_int : Integrable (fun s => ‖setup.gradL w s‖ ^ 2) setup.sampleDist := by
      apply Integrable.mono (integrable_const (G ^ 2))
      · intro s; exact pow_le_pow_left₀ (norm_nonneg _) (hbounded w s) 2
      · exact integrable_const _
    -- Bound component
    have h_bound : ∫ s, ‖setup.gradL w s‖ ^ 2 ∂setup.sampleDist ≤ G ^ 2 := by
      calc
        ∫ s, ‖setup.gradL w s‖ ^ 2 ∂setup.sampleDist
          ≤ ∫ s, G ^ 2 ∂setup.sampleDist := integral_mono h_int (integrable_const _)
            (fun s => pow_le_pow_left₀ (norm_nonneg _) (hbounded w s) 2)
        _ = G ^ 2 := by simp [integral_const, probReal_univ]
    exact ⟨h_int, h_bound⟩
  -- Per-step bound
  have hstep : ∀ t < T,
      ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P ≤
        ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P
        - 2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)
        + η ^ 2 * G ^ 2 := by
    intro t ht
    -- Pointwise norm expansion
    have h_expand : ∀ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 =
        ‖setup.process t ω - wStar‖ ^ 2
        - 2 * η * ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ
        + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := by
      intro ω
      rw [setup.process_succ, hη t]
      exact norm_sq_sgd_step (setup.process t ω) (setup.gradL (setup.process t ω) (setup.ξ t ω)) wStar η
    -- Subgradient inequality
    have h_subgrad_ineq : ∀ ω, f (setup.process t ω) - f wStar ≤
        ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ := by
      intro ω
      have h_mem : setup.gradL (setup.process t ω) (setup.ξ t ω) ∈ subdifferential ℝ f (setup.process t ω) :=
        hsubgrad (setup.process t ω) (setup.ξ t ω)
      have h_ineq : ∀ y, f y ≥ f (setup.process t ω) + ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), y - setup.process t ω⟫_ℝ :=
        mem_subdifferential_iff.mp h_mem
      specialize h_ineq wStar
      simpa [inner_sub_right, inner_neg_right, real_inner_comm] using h_ineq
    -- Pointwise combined bound
    have h_pointwise : ∀ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ≤
        ‖setup.process t ω - wStar‖ ^ 2
        - 2 * η * (f (setup.process t ω) - f wStar)
        + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := by
      intro ω
      calc
        ‖setup.process (t + 1) ω - wStar‖ ^ 2
          = ‖setup.process t ω - wStar‖ ^ 2
              - 2 * η * ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ
              + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := h_expand ω
        _ ≤ ‖setup.process t ω - wStar‖ ^ 2
              - 2 * η * (f (setup.process t ω) - f wStar)
              + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := by
            gcongr
            · rw [real_inner_comm]
              exact h_subgrad_ineq ω
            · rfl
    -- Integrate pointwise bound
    have h_int_bound : ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P ≤
        ∫ ω, (‖setup.process t ω - wStar‖ ^ 2
          - 2 * η * (f (setup.process t ω) - f wStar)
          + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) ∂setup.P := by
      apply integral_mono (h_int_norm_sq (t + 1)) _ h_pointwise
      exact (h_int_norm_sq t).sub (((h_int_f t).sub (integrable_const _)).const_mul (2 * η))
        |>.add ((h_int_sq t).const_mul (η ^ 2))
    -- Apply linearity and variance bound
    calc
      ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P
        ≤ ∫ ω, (‖setup.process t ω - wStar‖ ^ 2
            - 2 * η * (f (setup.process t ω) - f wStar)
            + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) ∂setup.P := h_int_bound
      _ = ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P
          - 2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)
          + η ^ 2 * ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P := by
        simp_rw [integral_add, integral_sub, integral_const_mul]
        · ring
        · exact h_int_norm_sq t
        · exact ((h_int_f t).sub (integrable_const _)).const_mul (2 * η)
        · exact (h_int_sq t).const_mul (η ^ 2)
        · exact (h_int_f t).sub (integrable_const _)
        · exact h_int_sq t
      _ ≤ ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P
          - 2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)
          + η ^ 2 * G ^ 2 := by
        gcongr
        exact expectation_norm_sq_gradL_bound
          (fun w => (hvar w).2)
          (subgradientProcess_indepFun_xi setup hgL t)
          ((setup.hξ_ident t).map_eq)
          (subgradientProcess_measurable setup hgL t)
          (setup.hξ_meas t)
          hgL
          (h_int_sq t)
  -- Telescope over t < T
  have hsum : 2 * η * ∑ t ∈ Finset.range T,
        (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
      ‖setup.w₀ - wStar‖ ^ 2 + (T : ℝ) * (η ^ 2 * G ^ 2) := by
    set a := fun t => ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P
    set gap := fun t => ∫ ω, f (setup.process t ω) ∂setup.P - f wStar
    have h_rearr : ∀ t, t < T → 2 * η * gap t ≤ (a t - a (t + 1)) + η ^ 2 * G ^ 2 := by
      intro t ht
      have h := hstep t ht
      linarith
    have h_sum_le := Finset.sum_le_sum (fun t ht => h_rearr t (Finset.mem_range.mp ht))
    rw [← Finset.mul_sum] at h_sum_le
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h_sum_le
    have h_tele : ∑ t ∈ Finset.range T, (a t - a (t + 1)) = a 0 - a T := by
      simp_rw [show ∀ t, a t - a (t + 1) = -(a (t + 1) - a t) from fun t => by ring]
      rw [Finset.sum_neg_distrib, Finset.sum_range_sub]
      ring
    rw [h_tele] at h_sum_le
    have h_init : a 0 = ‖setup.w₀ - wStar‖ ^ 2 := by
      simp [a, SubgradientSetup.process_zero, integral_const, probReal_univ]
    rw [h_init] at h_sum_le
    linarith
  -- Final algebraic rearrangement
  have hT_pos : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hη2_pos : (0 : ℝ) < 2 * η := by linarith
  rw [one_div, inv_mul_le_iff₀ hT_pos]
  have h_rhs : ↑T * (‖setup.w₀ - wStar‖ ^ 2 / (2 * η * ↑T) + η * G ^ 2 / 2) =
      (‖setup.w₀ - wStar‖ ^ 2 + ↑T * (η ^ 2 * G ^ 2)) / (2 * η) := by
    field_simp
    ring
  rw [h_rhs, le_div_iff₀ hη2_pos]
  linarith
