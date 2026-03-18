import Main
import Lib.Glue.Algebra
import Lib.Glue.Probability
import Lib.Layer0.IndepExpect

/-!
# Stochastic Subgradient Method — Convex Non-Smooth Optimization (Primitive Form)

Layer: 2 (concrete algorithm proof with novel structure)

CRITICAL CORRECTION: Removed all abstract subdifferential symbols per Principle A.
Replaced with primitive inequality form: ∀ w s y, f y ≥ f w + ⟪gradL w s, y - w⟫_ℝ
This avoids invented symbols and matches Mathlib's primitive requirements.

Archetype B — novel proof structure bypassing Layer 1 meta-theorems due to:
- Absence of gradF/unbiasedness hypotheses
- Direct use of primitive subgradient inequality in pointwise bound
- Variance bound derived internally from uniform oracle bound (Pattern I)

Proof chain (convex case, constant η):
1. Pointwise norm expansion via `norm_sq_sgd_step`
2. Primitive subgradient inequality: f(wₜ) - f(w*) ≤ ⟪gₜ, wₜ - w*⟫ (direct quantifier form)
3. Substitute inequality into expansion
4. Integrate + linearity
5. Bounded oracle → variance bound via Pattern I
6. Telescope sum + algebraic rearrangement

Design compliance:
- Convention §1: Variance bound derived internally with explicit integrability
- Convention §2: hgL stored in structure (weakest measurability level)
- Convention §4: All lemmas include Used in: tags
- Convention §5: NOT APPLICABLE (uniform oracle bound)

Used in: main convergence result for non-smooth convex stochastic optimization
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {S : Type*} [MeasurableSpace S]
variable {Ω : Type*} [MeasurableSpace Ω]

-- ============================================================================
-- SubgradientSetup: NO gradF field (non-smooth objective)
-- ============================================================================
/-- Complete setup for stochastic subgradient method.
Critical distinction: contains NO `gradF` field (non-smooth objective has no gradient).
Includes oracle measurability `hgL` as structure field (Convention §2). -/
structure SubgradientSetup
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E]
    (S : Type*) [MeasurableSpace S]
    (Ω : Type*) [MeasurableSpace Ω] where
  w₀ : E
  η : ℕ → ℝ
  gradL : E → S → E
  ξ : ℕ → Ω → S
  P : Measure Ω
  hP : IsProbabilityMeasure P
  hξ_meas : ∀ t, Measurable (ξ t)
  hξ_indep : iIndepFun (β := fun _ => S) ξ P
  hξ_ident : ∀ t, IdentDistrib (ξ t) (ξ 0) P P
  hgL : Measurable (Function.uncurry gradL)

/-- Self-contained recursive process definition for subgradient method (Archetype B). -/
noncomputable def SubgradientSetup.process (setup : SubgradientSetup E S Ω) : ℕ → Ω → E
  | 0 => fun _ => setup.w₀
  | t + 1 => fun ω => 
      let w_t := process setup t ω
      w_t - setup.η t • setup.gradL w_t (setup.ξ t ω)

namespace SubgradientSetup

variable (setup : SubgradientSetup E S Ω)

@[simp]
theorem process_zero : process setup 0 = fun _ => setup.w₀ := by
  sorry
@[simp]
theorem process_succ (t : ℕ) : process setup (t + 1) = fun ω => process setup t ω - setup.η t • setup.gradL (process setup t ω) (setup.ξ t ω) := by
  sorry

end SubgradientSetup

-- ============================================================================
-- Convergence theorem (PRIMITIVE FORM — NO abstract subdifferential symbols)
-- ============================================================================
/-- Convex convergence for stochastic subgradient method (primitive inequality form).
Archetype B: novel proof structure bypassing Layer 1 meta-theorems.
Uses primitive subgradient condition: ∀ w s y, f y ≥ f w + ⟪gradL w s, y - w⟫_ℝ
Derives variance bound internally from uniform oracle bound (Pattern I).
Used in: main result for non-smooth convex stochastic optimization (this file) -/
theorem subgradient_convergence_convex
    (setup : SubgradientSetup E S Ω) (f : E → ℝ) {G η : ℝ} (wStar : E)
    -- PRIMITIVE SUBGRADIENT CONDITION (replaces abstract subdifferential membership):
    (hsubgrad : ∀ w s y, f y ≥ f w + ⟪setup.gradL w s, y - w⟫_ℝ)
    (hbounded : ∀ w s, ‖setup.gradL w s‖ ≤ G)
    (hη_pos : 0 < η) (hη : ∀ t, setup.η t = η)
    (T : ℕ) (hT : 0 < T)
    (h_int_f : ∀ t, Integrable (fun ω => f (setup.process t ω)) setup.P)
    (h_int_norm_sq : ∀ t, Integrable (fun ω => ‖setup.process t ω - wStar‖ ^ 2) setup.P)
    (h_int_sq : ∀ t, Integrable (fun ω =>
        ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) setup.P) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
      ‖setup.w₀ - wStar‖ ^ 2 / (2 * η * T) + η * G ^ 2 / 2 := by
  have hη_const : ∀ t, setup.η t = η := hη

    -- Step 1: Pointwise norm expansion
    have h_step_ineq : ∀ t ω, 
        ‖setup.process (t + 1) ω - wStar‖ ^ 2 ≤ 
        ‖setup.process t ω - wStar‖ ^ 2 - 
        2 * η * ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ +
        η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := by
      intro t ω
      have h1 : setup.process (t + 1) ω = setup.process t ω - η • setup.gradL (setup.process t ω) (setup.ξ t ω) := by
        rw [SubgradientSetup.process_succ setup t]
        simp [hη t]
      rw [h1]
      have h2 : ‖setup.process t ω - η • setup.gradL (setup.process t ω) (setup.ξ t ω) - wStar‖ ^ 2 = 
          ‖(setup.process t ω - wStar) - η • setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := by
        rw [sub_sub]
      rw [h2]
      have h3 : ‖(setup.process t ω - wStar) - η • setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 = 
          ‖setup.process t ω - wStar‖ ^ 2 - 2 * η * ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := by
        rw [norm_sub_sq_real]
        simp [inner_smul_right, inner_comm, smul_smul]
        ring
      rw [h3]

    -- Step 2: Subgradient inequality for function values
    have h_subgrad_bound : ∀ t ω, 
        f (setup.process t ω) - f wStar ≤ ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ := by
      intro t ω
      have h1 : f wStar ≥ f (setup.process t ω) + ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), wStar - setup.process t ω⟫_ℝ := 
        hsubgrad (setup.process t ω) (setup.ξ t ω) wStar
      have h2 : ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), wStar - setup.process t ω⟫_ℝ = 
          -⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ := by
        rw [inner_sub_left, inner_self_sub]
        ring
      rw [h2] at h1
      linarith

    -- Step 3: Gradient norm bound
    have h_grad_bound : ∀ t ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ≤ G ^ 2 := by
      intro t ω
      have h1 : ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ≤ G := hbounded (setup.process t ω) (setup.ξ t ω)
      have h2 : 0 ≤ G := by
        have h3 := hbounded (setup.process t ω) (setup.ξ t ω)
        exact le_of_lt (lt_of_le_of_ne h3 (by intro h; rw [h] at h1; norm_num at h1))
      nlinarith

    -- Step 4: Integrate step inequality
    have h_int_step : ∀ t, 
        ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P ≤ 
        ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P - 
        2 * η * ∫ ω, ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ ∂setup.P +
        η ^ 2 * ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P := by
      intro t
      have h1 : ∀ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ≤ 
          ‖setup.process t ω - wStar‖ ^ 2 - 
          2 * η * ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ +
          η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := h_step_ineq t
      have h2 : ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P ≤ 
          ∫ ω, (‖setup.process t ω - wStar‖ ^ 2 - 
          2 * η * ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ +
          η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) ∂setup.P := by
        apply integral_mono_on
        · exact Set.univ
        · exact h1
        · exact MeasurableSet.univ
        · exact setup.hP.pos
      have h3 : ∫ ω, (‖setup.process t ω - wStar‖ ^ 2 - 
          2 * η * ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ +
          η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) ∂setup.P = 
          ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P - 
          2 * η * ∫ ω, ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ ∂setup.P +
          η ^ 2 * ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P := by
        rw [integral_add, integral_sub]
        · rw [integral_add]
          · ring
          · exact h_int_sq t
        · exact h_int_norm_sq t
        · exact h_int_sq t
      rw [h3] at h2
      exact h2

    -- Step 5: Integrate subgradient bound
    have h_int_subgrad : ∀ t, 
        ∫ ω, f (setup.process t ω) ∂setup.P - f wStar ≤ 
        ∫ ω, ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ ∂setup.P := by
      intro t
      have h1 : ∀ ω, f (setup.process t ω) - f wStar ≤ ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ := h_subgrad_bound t
      have h2 : ∫ ω, f (setup.process t ω) ∂setup.P - f wStar = 
          ∫ ω, (f (setup.process t ω) - f wStar) ∂setup.P := by
        rw [integral_sub_const]
        simp [setup.hP.volume_univ]
      rw [h2]
      have h3 : ∫ ω, (f (setup.process t ω) - f wStar) ∂setup.P ≤ 
          ∫ ω, ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ ∂setup.P := by
        apply integral_mono_on
        · exact Set.univ
        · exact h1
        · exact MeasurableSet.univ
        · exact setup.hP.pos
      exact h3

    -- Step 6: Integrate gradient bound
    have h_int_grad : ∀ t, ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P ≤ G ^ 2 := by
      intro t
      have h1 : ∀ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ≤ G ^ 2 := h_grad_bound t
      have h2 : ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P ≤ 
          ∫ ω, G ^ 2 ∂setup.P := by
        apply integral_mono_on
        · exact Set.univ
        · exact h1
        · exact MeasurableSet.univ
        · exact setup.hP.pos
      have h3 : ∫ ω, G ^ 2 ∂setup.P = G ^ 2 := by
        rw [integral_const]
        simp [setup.hP.volume_univ]
      rw [h3] at h2
      exact h2

    -- Step 7: Telescope sum
    have h_telescope : ∑ t ∈ Finset.range T, 
        (∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P - 
         ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) = 
        ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P - 
        ∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P := by
      have h1 : ∑ t ∈ Finset.range T, 
          (∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P - 
           ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) = 
          ∑ t ∈ Finset.range T, 
          (∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) - 
          ∑ t ∈ Finset.range T, 
          (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) := by
        rw [Finset.sum_sub_distrib]
      rw [h1]
      have h2 : ∑ t ∈ Finset.range T, 
          (∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) = 
          ∑ t ∈ Finset.Ico 1 (T + 1), 
          (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) := by
        apply Finset.sum_bij' (fun t _ => t + 1) (fun t _ => t - 1)
        · intro t ht
          simp only [Finset.mem_Ico, Nat.succ_le_succ_iff, Nat.lt_succ_iff] at ht ⊢
          omega
        · intro t ht
          simp only [Finset.mem_Ico, Nat.succ_le_succ_iff, Nat.lt_succ_iff] at ht ⊢
          omega
        · intro t ht
          simp only [Finset.mem_range, Nat.lt_succ_iff] at ht ⊢
          omega
        · intro t ht
          simp only [Finset.mem_Ico, Nat.succ_le_succ_iff, Nat.lt_succ_iff] at ht ⊢
          omega
        · intro t ht
          simp
      rw [h2]
      have h3 : ∑ t ∈ Finset.Ico 1 (T + 1), 
          (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) - 
          ∑ t ∈ Finset.range T, 
          (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) = 
          ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P - 
          ∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P := by
        have h4 : ∑ t ∈ Finset.Ico 1 (T + 1), 
            (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) = 
            ∑ t ∈ Finset.range (T + 1), 
            (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) - 
            ∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P := by
          rw [Finset.sum_Ico_eq_sum_range]
          simp
        rw [h4]
        have h5 : ∑ t ∈ Finset.range (T + 1), 
            (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) = 
            ∑ t ∈ Finset.range T, 
            (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) + 
            ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P := by
          rw [Finset.sum_range_succ]
        rw [h5]
        ring
      rw [h3]

    -- Step 8: Initial condition
    have h_init : ∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P = ‖setup.w₀ - wStar‖ ^ 2 := by
      have h1 : setup.process 0 = fun _ => setup.w₀ := SubgradientSetup.process_zero setup
      rw [h1]
      simp [integral_const]
      simp [setup.hP.volume_univ]

    -- Step 9: Main inequality
    have h_main : ∑ t ∈ Finset.range T, 
        (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤ 
        (‖setup.w₀ - wStar‖ ^ 2 - ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P) / (2 * η) + 
        T * η * G ^ 2 / 2 := by
      have h1 : ∀ t, 
          ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P ≤ 
          ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P - 
          2 * η * ∫ ω, ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ ∂setup.P +
          η ^ 2 * ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P := 
        h_int_step
      have h2 : ∀ t, 
          ∫ ω, f (setup.process t ω) ∂setup.P - f wStar ≤ 
          ∫ ω, ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ ∂setup.P := 
        h_int_subgrad
      have h3 : ∀ t, ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P ≤ G ^ 2 := 
        h_int_grad
      have h4 : ∑ t ∈ Finset.range T, 
          (∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P - 
           ∫ ω, ‖setup.process t ω - wStar‖
