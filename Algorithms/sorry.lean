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
  rfl
@[simp]
theorem process_succ (t : ℕ) : process setup (t + 1) = fun ω => process setup t ω - setup.η t • setup.gradL (process setup t ω) (setup.ξ t ω) := by
  rfl

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
  -- Key step: For each t, expand the norm using the update rule
  have step_expansion : ∀ t, ∫ ω, (‖setup.process (t + 1) ω - wStar‖ ^ 2 - ‖setup.process t ω - wStar‖ ^ 2) ∂setup.P ≤
                        -2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) + η ^ 2 * G ^ 2 := by
    intro t
    -- Use the process definition and norm expansion
    have aux : ∀ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 = 
                    ‖setup.process t ω - wStar‖ ^ 2 - 2 * η * ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := by
      intro ω
      have h := congr_fun (SubgradientSetup.process_succ setup t) ω
      rw [h]
      simp [hη]
      apply norm_sq_sgd_step
    -- Integrate both sides
    have int_eq : ∫ ω, (‖setup.process (t + 1) ω - wStar‖ ^ 2 - ‖setup.process t ω - wStar‖ ^ 2) ∂setup.P =
                   ∫ ω, (- 2 * η * ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) ∂setup.P := by
      congr
      ext ω
      rw [aux ω]
      ring
    rw [int_eq]
    -- Use linearity of integration
    · -- First integrability goal: for (- 2 * η * ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2)
      apply Integrable.add
      · apply Integrable.const_mul
        apply integrable_neg
        apply integrable_inner_of_sq_integrable (h_int_norm_sq t) (h_int_sq t)
      · exact h_int_sq t
    · -- Second integrability goal: for (‖setup.process (t + 1) ω - wStar‖ ^ 2 - ‖setup.process t ω - wStar‖ ^ 2)
      apply Integrable.sub (h_int_norm_sq (t+1)) (h_int_norm_sq t)
    rw [integral_add]
    rw [integral_smul, integral_smul]
    · -- Prove integrability for (-2 * η) * ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ
      apply Integrable.const_mul
      apply integrable_neg
      apply integrable_inner_of_sq_integrable (h_int_norm_sq t) (h_int_sq t)
    · -- Prove integrability for η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2
      exact h_int_sq t
    -- Apply the subgradient inequality
    have subgrad_use : ∫ ω, (-2 * η) * ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ ∂setup.P ≤
                        ∫ ω, (-2 * η) * (f (setup.process t ω) - f wStar) ∂setup.P := by
      -- Since -2η < 0, multiplying the subgradient inequality by -2η flips the sign
      suffices : ∀ ω, (-2 * η) * ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ ≤
                     (-2 * η) * (f (setup.process t ω) - f wStar) by
        apply integral_mono (Integrable.const_mul _) (Integrable.const_mul _)
        · apply integrable_neg
          apply Integrable.const_mul
          apply integrable_inner_of_sq_integrable (h_int_norm_sq t) (h_int_sq t)
        · apply Integrable.const_mul
          apply h_int_f t
        intro ω
        have subg := hsubgrad (setup.process t ω) (setup.ξ t ω) wStar
        have : f wStar ≥ f (setup.process t ω) + ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), wStar - setup.process t ω⟫_ℝ := subg
        linarith [inner_sub_left, this]
    -- Bound the squared gradient term
    have grad_bound : ∫ ω, η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P ≤ η ^ 2 * G ^ 2 := by
      have : ∀ ω, η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ≤ η ^ 2 * G ^ 2 := by
        intro ω
        apply mul_le_mul_of_nonneg_left (sq_le_sq.mpr (hbounded (setup.process t ω) (setup.ξ t ω))) (sq_nonneg η)
      apply integral_mono_on _ (h_int_sq t) (integrable_const _) (Set.univ_mem_sets) this
    -- Combine the bounds
    linarith [subgrad_use, grad_bound]
  -- Sum the inequalities over t from 0 to T-1
  have sum_ineq : ∑ t ∈ Finset.range T, ∫ ω, (‖setup.process (t + 1) ω - wStar‖ ^ 2 - ‖setup.process t ω - wStar‖ ^ 2) ∂setup.P ≤
                  ∑ t ∈ Finset.range T, (-2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) + η ^ 2 * G ^ 2) := by
    apply Finset.sum_le_sum
    intro t ht
    exact step_expansion t
  -- The left-hand side telescopes
  have telescope : ∑ t ∈ Finset.range T, ∫ ω, (‖setup.process (t + 1) ω - wStar‖ ^ 2 - ‖setup.process t ω - wStar‖ ^ 2) ∂setup.P =
                   ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P - ∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P := by
    have : ∀ t, ∫ ω, (‖setup.process (t + 1) ω - wStar‖ ^ 2 - ‖setup.process t ω - wStar‖ ^ 2) ∂setup.P =
             ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P - ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P := by
      intro t
      rw [integral_sub (h_int_norm_sq (t+1)) (h_int_norm_sq t)]
    simp_rw [this]
    rw [Finset.sum_range_subtract_cancel (fun t => ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P)]
    rfl
  rw [telescope] at sum_ineq
  -- Use that ∫ ||process T - wStar||^2 ≥ 0
  have nonneg_T : 0 ≤ ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P := by
    apply integral_nonneg
    intro ω
    apply sq_nonneg
  -- So: LHS ≥ -∫ ||process 0 - wStar||^2
  have lhs_bound : ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P - ∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P ≥
                   -∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P := by
    calc
      ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P - ∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P ≥
        0 - ∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P := by
        gcongr
        apply nonneg_T
      _ = -∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P := by
        rw [zero_sub]
  -- Combining with the sum inequality
  have combined : -∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P ≤
                   ∑ t ∈ Finset.range T, (-2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) + η ^ 2 * G ^ 2) := by
    calc
      -∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P ≤
        ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P - ∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P := by
        exact lhs_bound
      _ ≤ ∑ t ∈ Finset.range T, (-2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) + η ^ 2 * G ^ 2) := by
        exact sum_ineq
  -- Simplify the initial condition
  have init_simp : ∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P = ‖setup.w₀ - wStar‖ ^ 2 := by
    rw [SubgradientSetup.process_zero]
    apply integral_const
  rw [init_simp] at combined
  -- Rearrange to get the sum bound
  have rearranged : -‖setup.w₀ - wStar‖ ^ 2 ≤ -2 * η * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) + T * η ^ 2 * G ^ 2 := by
    calc
      -‖setup.w₀ - wStar‖ ^ 2 = -∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P := by
        rw [init_simp]
      _ ≤ ∑ t ∈ Finset.range T, (-2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) + η ^ 2 * G ^ 2) := by
        exact combined
    _ = -2 * η * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) + ∑ t ∈ Finset.range T, (η ^ 2 * G ^ 2) := by
      rw [Finset.sum_add_distrib]
      congr
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ = -2 * η * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) + T * η ^ 2 * G ^ 2 := by
      rw [Finset.sum_const]
      rfl
  -- Add 2η * sum to both sides
  have aux_ineq : 2 * η * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
                  ‖setup.w₀ - wStar‖ ^ 2 + T * η ^ 2 * G ^ 2 := by
    calc
      2 * η * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) =
        (-‖setup.w₀ - wStar‖ ^ 2) + (2 * η * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)) + ‖setup.w₀ - wStar‖ ^ 2 ≤
          (-2 * η * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) + T * η ^ 2 * G ^ 2) + ‖setup.w₀ - wStar‖ ^ 2 := by
        gcongr
        exact rearranged
      _ = ‖setup.w₀ - wStar‖ ^ 2 + T * η ^ 2 * G ^ 2 := by
        ring
  -- Divide by 2η > 0
  have div_eta : ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
                 ‖setup.w₀ - wStar‖ ^ 2 / (2 * η) + T * η * G ^ 2 / 2 := by
    calc
      ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
        (‖setup.w₀ - wStar‖ ^ 2 + T * η ^ 2 * G ^ 2) / (2 * η) := by
        apply div_le_div_of_pos_right aux_ineq (by linarith [hη_pos])
      _ = ‖setup.w₀ - wStar‖ ^ 2 / (2 * η) + (T * η ^ 2 * G ^ 2) / (2 * η) := by
        rw [add_div]
      _ = ‖setup.w₀ - wStar‖ ^ 2 / (2 * η) + T * η * G ^ 2 / 2 := by
        congr
        apply div_eq_div_iff (by positivity) (by positivity)
        ring
  -- Finally, divide by T > 0
  calc
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
      (‖setup.w₀ - wStar‖ ^ 2 / (2 * η) + T * η * G ^ 2 / 2) / T := by
      apply div_le_div_of_pos_right div_eta (by positivity)
    _ = ‖setup.w₀ - wStar‖ ^ 2 / (2 * η * T) + η * G ^ 2 / 2 := by
      rw [add_div, div_div_assoc]
      congr
      · rw [div_comm, one_mul]
      · rw [mul_div_assoc, div_self (by positivity), mul_one]
