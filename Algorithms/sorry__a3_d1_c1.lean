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
theorem process_succ (t : ℕ) :
    process setup (t + 1) =
      fun ω => process setup t ω - setup.η t • setup.gradL (process setup t ω) (setup.ξ t ω) := by
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
  -- The proof proceeds by establishing several intermediate results first
  -- For each t, expand the squared distance from the next iterate to the optimal point
  have step_expansion : ∀ (t : ℕ) (ω : Ω),
    ‖setup.process (t+1) ω - wStar‖^2 = 
      ‖setup.process t ω - wStar‖^2 - 2 * setup.η t * ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ + (setup.η t)^2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖^2 := by
    intro t ω
    rw [SubgradientSetup.process_succ]
    simp
    apply norm_sq_sgd_step
  
  -- Use the subgradient inequality to bound the inner product term
  have subgrad_bound : ∀ (t : ℕ) (ω : Ω),
    ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ ≥ f (setup.process t ω) - f wStar := by
    intro t ω
    specialize hsubgrad (setup.process t ω) (setup.ξ t ω) wStar
    -- From hsubgrad: f wStar ≥ f (setup.process t ω) + ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), wStar - setup.process t ω⟫_ℝ
    have h_temp : f wStar ≥ f (setup.process t ω) + ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), wStar - setup.process t ω⟫_ℝ := hsubgrad
    -- Show wStar - setup.process t ω = -(setup.process t ω - wStar)
    have neg_eq : wStar - setup.process t ω = -(setup.process t ω - wStar) := by abel
    rw [neg_eq] at h_temp
    -- So f wStar ≥ f (setup.process t ω) + ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), -(setup.process t ω - wStar)⟫_ℝ
    -- Use the property that ⟪x, -y⟫ = -⟪x, y⟫
    rw [inner_neg_right] at h_temp
    -- So f wStar ≥ f (setup.process t ω) - ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ
    -- Rearranging: ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ ≥ f (setup.process t ω) - f wStar
    have temp_result : ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ ≥ f (setup.process t ω) - f wStar := by
      linarith [h_temp]
    -- By symmetry of inner product: ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ = ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ
    rw [inner_comm]
    exact temp_result
  
  -- Since η is constant, we can factor it out
  have h_const : ∀ t, setup.η t = η := hη
  
  -- Combine to get a recursive bound
  have recursive_bound : ∀ (t : ℕ) (ω : Ω),
    2 * setup.η t * (f (setup.process t ω) - f wStar) ≤
      ‖setup.process t ω - wStar‖^2 - ‖setup.process (t+1) ω - wStar‖^2 + (setup.η t)^2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖^2 := by
    intro t ω
    -- From step_expansion: ‖setup.process (t+1) ω - wStar‖^2 = 
    --   ‖setup.process t ω - wStar‖^2 - 2 * setup.η t * ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ + (setup.η t)^2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖^2
    -- Therefore: -‖setup.process (t+1) ω - wStar‖^2 = 
    --   -‖setup.process t ω - wStar‖^2 + 2 * setup.η t * ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ - (setup.η t)^2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖^2
    have step_expansion_neg : -‖setup.process (t+1) ω - wStar‖^2 =
      -‖setup.process t ω - wStar‖^2 + 2 * setup.η t * ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ - (setup.η t)^2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖^2 := by
      calc
        -‖setup.process (t+1) ω - wStar‖^2
        = -(‖setup.process t ω - wStar‖^2 - 2 * setup.η t * ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ + (setup.η t)^2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖^2) := by
          congr
          exact (step_expansion t ω)
        _ = -‖setup.process t ω - wStar‖^2 + 2 * setup.η t * ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ - (setup.η t)^2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖^2 := by
          ring
    calc
      2 * setup.η t * (f (setup.process t ω) - f wStar)
      ≤ 2 * setup.η t * ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ := by
        rw [h_const t]
        apply mul_le_mul_of_nonneg_left (subgrad_bound t ω)
        apply mul_nonneg (by positivity) (le_of_lt hη_pos)
      _ = ‖setup.process t ω - wStar‖^2 - ‖setup.process t ω - wStar‖^2 + 2 * setup.η t * ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ - (setup.η t)^2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖^2 + (setup.η t)^2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖^2 := by
        ring
      _ = ‖setup.process t ω - wStar‖^2 + (-‖setup.process t ω - wStar‖^2 + 2 * setup.η t * ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ - (setup.η t)^2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖^2) + (setup.η t)^2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖^2 := by
        ring
      _ = ‖setup.process t ω - wStar‖^2 + (-‖setup.process (t+1) ω - wStar‖^2) + (setup.η t)^2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖^2 := by
        rw [←step_expansion_neg]
  
  -- Prove the telescoping sum property separately
  have telescoping_part : ∀ T : ℕ, T > 0 → ∑ t ∈ Finset.range T, ∫ ω, (‖setup.process t ω - wStar‖^2 - ‖setup.process (t+1) ω - wStar‖^2) ∂setup.P =
      ∫ ω, ‖setup.process 0 ω - wStar‖^2 ∂setup.P - ∫ ω, ‖setup.process T ω - wStar‖^2 ∂setup.P := by
    intro T hT
    -- We prove this by induction on T
    cases T
    · exfalso
      apply Nat.not_lt_zero 0
      exact hT
    · rename_i n
      -- Now T = n + 1, we prove the claim for T = n + 1 by induction on n
      induction n with
      | zero =>
        -- Base case: T = 1
        simp [Finset.range_one]
        -- Need to show: ∫ (‖setup.process 0 ω - wStar‖^2 - ‖setup.process 1 ω - wStar‖^2) dω = ∫ ‖setup.process 0 ω - wStar‖^2 dω - ∫ ‖setup.process 1 ω - wStar‖^2 dω
        erw [integral_sub (h_int_norm_sq 0) (h_int_norm_sq 1)]
        ring
      | succ k hk =>
        -- Inductive step: T = k + 2
        -- Our goal is for T = n + 1 where n = k + 1, so T = k + 2
        -- We need: ∑ t ∈ range(k+2), ... = ∫ w_0 - ∫ w_{k+2}
        rw [Finset.range_succ]
        rw [Finset.sum_insert (Finset.not_mem_range_self _)]
        -- Apply inductive hypothesis for T = k + 1
        specialize hk (by omega)
        rw [hk]
        -- Now use integral_sub for the additional term
        rw [integral_sub (h_int_norm_sq (k+1)) (h_int_norm_sq (k+1 + 1))]
        ring
  
  -- Sum over t from 0 to T-1
  have sum_inequality : 2 * η * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
    ‖setup.w₀ - wStar‖^2 - ∫ ω, ‖setup.process T ω - wStar‖^2 ∂setup.P + η^2 * ∑ t ∈ Finset.range T, ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖^2 ∂setup.P := by
    calc
      2 * η * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)
      _ = ∑ t ∈ Finset.range T, 2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) := (Finset.sum_mul _ _).symm
      _ = ∑ t ∈ Finset.range T, ∫ ω, (2 * η * f (setup.process t ω) - 2 * η * f wStar) ∂setup.P := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [integral_sub (integrable_const_smul (2 * η) (h_int_f t)) (integrable_const_smul (2 * η) (integrable_const (f wStar) setup.P))]
        rw [integral_const_smul, integral_const_smul, integral_const]
        ring
      _ ≤ ∑ t ∈ Finset.range T, ∫ ω, (‖setup.process t ω - wStar‖^2 - ‖setup.process (t+1) ω - wStar‖^2 + η^2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖^2) ∂setup.P := by
        apply Finset.sum_le_sum
        intro t ht
        -- Use integral_mono with the pointwise bound from recursive_bound
        apply integral_mono
        · -- Prove integrability of left side
          exact (integrable_const_smul (2 * η) (integrable_sub (h_int_f t) (integrable_const (f wStar) setup.P))).1
        · -- Prove integrability of right side
          exact (integrable_sub (h_int_norm_sq t) (h_int_norm_sq (t + 1))).add (integrable_const_smul (η^2) (h_int_sq t))
        · -- Prove pointwise inequality
          intro ω
          calc
            (2 * η * f (setup.process t ω) - 2 * η * f wStar)
            _ = 2 * η * (f (setup.process t ω) - f wStar) := by
              ring
            _ ≤ ‖setup.process t ω - wStar‖^2 - ‖setup.process (t+1) ω - wStar‖^2 + η^2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖^2 := by
              have temp := recursive_bound t ω
              rw [h_const t] at temp
              exact temp
      _ = (∑ t ∈ Finset.range T, ∫ ω, ‖setup.process t ω - wStar‖^2 ∂setup.P) - (∑ t ∈ Finset.range T, ∫ ω, ‖setup.process (t+1) ω - wStar‖^2 ∂setup.P) + (η^2 * ∑ t ∈ Finset.range T, ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖^2 ∂setup.P) := by
        ring
      _ = (∫ ω, ‖setup.process 0 ω - wStar‖^2 ∂setup.P - ∫ ω, ‖setup.process T ω - wStar‖^2 ∂setup.P) + (η^2 * ∑ t ∈ Finset.range T, ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖^2 ∂setup.P) := by
        rw [←telescoping_part T hT]
      _ = ∫ ω, ‖setup.w₀ - wStar‖^2 ∂setup.P - ∫ ω, ‖setup.process T ω - wStar‖^2 ∂setup.P + η^2 * ∑ t ∈ Finset.range T, ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖^2 ∂setup.P := by
        rw [SubgradientSetup.process_zero]
        ring
      _ = ‖setup.w₀ - wStar‖^2 - ∫ ω, ‖setup.process T ω - wStar‖^2 ∂setup.P + η^2 * ∑ t ∈ Finset.range T, ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖^2 ∂setup.P := by
        rw [integral_const]
        simp [setup.hP]
  
  -- Bound the gradient norm terms using the bounded assumption
  have grad_norm_bound : ∀ t, ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖^2 ∂setup.P ≤ G^2 := by
    intro t
    calc
      ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖^2 ∂setup.P
      ≤ ∫ ω, G^2 ∂setup.P := by
        apply integral_mono
        · exact h_int_sq t
        · exact (MeasureTheory.integrable_const.mpr (G^2 : ℝ) setup.P)
        · intro ω
          calc
            ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖^2
            ≤ G ^ 2 := by
              have hbound : ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ≤ G := hbounded (setup.process t ω) (setup.ξ t ω)
              -- Since norms are non-negative and hbound shows ||gradL|| ≤ G, we can square both sides
              apply pow_le_pow_left₀ (norm_nonneg _) hbound 2
      _ = G^2 := by
        simp [MeasureTheory.integral_const, probReal_univ]
  
  -- Apply the gradient norm bound
  have final_sum_bound : η^2 * ∑ t ∈ Finset.range T, ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖^2 ∂setup.P ≤ η^2 * T * G^2 := by
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left (Finset.sum_le_card_mul_of_le _ _ (fun t _ => grad_norm_bound t))
    -- Need to prove η^2 ≥ 0
    apply pow_two_nonneg_of_nonneg
    apply le_of_lt hη_pos
  
  -- Auxiliary fact: negative integral of squared norm is non-positive
  have aux : -(∫ ω, ‖setup.process T ω - wStar‖^2 ∂setup.P) ≤ 0 := by
    apply neg_nonpos.mpr
    apply integral_nonneg_ae (by positivity) (fun ω => by positivity)

  -- Combine everything
  have combined_ineq : 2 * η * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
    ‖setup.w₀ - wStar‖^2 + η^2 * T * G^2 := by
    calc
      2 * η * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)
      ≤ ‖setup.w₀ - wStar‖^2 - ∫ ω, ‖setup.process T ω - wStar‖^2 ∂setup.P + η^2 * ∑ t ∈ Finset.range T, ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖^2 ∂setup.P := by
        exact sum_inequality
      _ ≤ ‖setup.w₀ - wStar‖^2 - ∫ ω, ‖setup.process T ω - wStar‖^2 ∂setup.P + η^2 * T * G^2 := by
        apply add_le_add_of_le_of_le (le_refl _)
        exact final_sum_bound
      _ ≤ ‖setup.w₀ - wStar‖^2 + η^2 * T * G^2 := by
        apply add_le_add_of_le_of_le (le_refl _)
        exact aux

  have main_ineq : ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤ (‖setup.w₀ - wStar‖^2 + η^2 * T * G^2) / (2 * η) := by
    apply div_le_of_mul_le₀
    · apply mul_pos (by positivity) hη_pos
    · exact combined_ineq
  
  calc
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)
    _ ≤ (1 / (T : ℝ)) * ((‖setup.w₀ - wStar‖^2 + η^2 * T * G^2) / (2 * η)) := by
      apply mul_le_mul_of_nonneg_left main_ineq
      apply mul_nonneg
      · positivity
      · apply inv_nonneg.mpr
        positivity
    _ = (‖setup.w₀ - wStar‖^2 + η^2 * T * G^2) / (2 * η * T) := by
      field_simp
      ring
    _ = ‖setup.w₀ - wStar‖ ^ 2 / (2 * η * T) + η * G ^ 2 / 2 := by
      rw [div_add_div_same]
      rw [add_comm]
      ring


