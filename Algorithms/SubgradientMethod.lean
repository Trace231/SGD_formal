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
  haveI : IsProbabilityMeasure setup.P := setup.hP
  have hη_const : ∀ t, setup.η t = η := hη
  have h_pointwise : ∀ t ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ≤ ‖setup.process t ω - wStar‖ ^ 2 - 2 * η * ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := by
    intro t ω
    have hη_t : setup.η t = η := hη_const t
    rw [SubgradientSetup.process_succ, hη_t]
    have := norm_sq_sgd_step (setup.process t ω) (setup.gradL (setup.process t ω) (setup.ξ t ω)) wStar η
    rw [this]
    <;> ring_nf
  -- Step 1: Derive subgradient inequality from hsubgrad
  have h_subgrad_ineq : ∀ t ω, f (setup.process t ω) - f wStar ≤ ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ := by
    intro t ω
    have h1 := hsubgrad (setup.process t ω) (setup.ξ t ω) wStar
    have h3 : f wStar ≥ f (setup.process t ω) + ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), wStar - setup.process t ω⟫_ℝ := h1
    have h4 : ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), wStar - setup.process t ω⟫_ℝ = -⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ := by
      rw [← neg_sub, inner_neg_right]
      <;> ring
    rw [h4] at h3
    linarith
  -- Step 2: Substitute subgradient inequality into h_pointwise
  have h_pointwise_with_f : ∀ t ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ≤ ‖setup.process t ω - wStar‖ ^ 2 - 2 * η * (f (setup.process t ω) - f wStar) + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := by
    intro t ω
    have h1 := h_pointwise t ω
    have h2 := h_subgrad_ineq t ω
    have h3 : -2 * η * ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ ≤ -2 * η * (f (setup.process t ω) - f wStar) := by
      have h4 : ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ = ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ := by
        rw [real_inner_comm]
      rw [h4]
      have h5 : 0 < η := hη_pos
      have h6 : ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ ≥ f (setup.process t ω) - f wStar := by linarith
      nlinarith
    linarith
  -- Step 3-7: Main proof using calc chain
  calc
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)
      = (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, ((1 / (2 * η)) * (2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar))) := by
        field_simp [hη_pos.ne', hT.ne']
        <;> ring
      _ ≤ (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, ((1 / (2 * η)) * ((∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) - (∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) + η ^ 2 * G ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro t _
        -- For each t, prove: (1/(2η))*(2η*(∫f - f*)) ≤ (1/(2η))*(∫‖w_t‖² - ∫‖w_{t+1}‖² + η²G²)
        have h_int_ineq : (1 / (2 * η)) * (2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)) ≤ (1 / (2 * η)) * ((∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) - (∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) + η ^ 2 * G ^ 2) := by
          have h_inner : 2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤ (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) - (∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) + η ^ 2 * G ^ 2 := by
            have h1 : ∀ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ≤ ‖setup.process t ω - wStar‖ ^ 2 - 2 * η * (f (setup.process t ω) - f wStar) + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := h_pointwise_with_f t
            have h_int_rhs : Integrable (fun ω => ‖setup.process t ω - wStar‖ ^ 2 - 2 * η * (f (setup.process t ω) - f wStar) + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) setup.P := by
              apply Integrable.add
              · apply Integrable.sub
                · exact h_int_norm_sq t
                · apply Integrable.const_mul ((h_int_f t).sub (integrable_const (f wStar))) (2 * η)
              · apply Integrable.const_mul (h_int_sq t) (η ^ 2)
            have h2 : (∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) ≤ ∫ ω, (‖setup.process t ω - wStar‖ ^ 2 - 2 * η * (f (setup.process t ω) - f wStar) + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) ∂setup.P := by
              apply integral_mono (h_int_norm_sq (t + 1)) h_int_rhs
              intro ω
              exact h1 ω
            have h3 : ∫ ω, (‖setup.process t ω - wStar‖ ^ 2 - 2 * η * (f (setup.process t ω) - f wStar) + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) ∂setup.P = (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) - 2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) + η ^ 2 * (∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P) := by
              have h_int_AB : Integrable (fun ω => ‖setup.process t ω - wStar‖ ^ 2 - 2 * η * (f (setup.process t ω) - f wStar)) setup.P := by
                apply Integrable.sub
                · exact h_int_norm_sq t
                · apply Integrable.const_mul ((h_int_f t).sub (integrable_const (f wStar))) (2 * η)
              have h_int_C : Integrable (fun ω => η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) setup.P := by
                apply Integrable.const_mul (h_int_sq t) (η ^ 2)
              rw [integral_add h_int_AB h_int_C]
              have h_int_A : Integrable (fun ω => ‖setup.process t ω - wStar‖ ^ 2) setup.P := h_int_norm_sq t
              have h_int_f_t : Integrable (fun ω => f (setup.process t ω)) setup.P := h_int_f t
              have h_int_f_star : Integrable (fun ω => f wStar) setup.P := integrable_const (f wStar)
              have h_int_f_diff : Integrable (fun ω => f (setup.process t ω) - f wStar) setup.P := h_int_f_t.sub h_int_f_star
              have h_int_scaled : Integrable (fun ω => 2 * η * (f (setup.process t ω) - f wStar)) setup.P := by
                apply Integrable.const_mul h_int_f_diff (2 * η)
              rw [integral_sub h_int_A h_int_scaled]
              have h_smul : (∫ ω, (2 * η) * (f (setup.process t ω) - f wStar) ∂setup.P) = (2 * η) * ∫ ω, (f (setup.process t ω) - f wStar) ∂setup.P := by
                rw [integral_const_mul]
              have h_integ : (∫ ω, f (setup.process t ω) - f wStar ∂setup.P) = (∫ ω, f (setup.process t ω) ∂setup.P) - f wStar := by
                rw [integral_sub h_int_f_t h_int_f_star]
                simp [integral_const]
              rw [h_smul, h_integ]
              have h_smul2 : (∫ ω, η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P) = η ^ 2 * ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P := by
                rw [integral_const_mul]
              rw [h_smul2]
            rw [h3] at h2
            have h4 : (∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P) ≤ G ^ 2 := by
              have h5 : ∀ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ≤ G ^ 2 := by
                intro ω
                have h6 := hbounded (setup.process t ω) (setup.ξ t ω)
                have h7 : 0 ≤ ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ := norm_nonneg _
                have h8 : 0 ≤ G := by
                  have h9 := hbounded (setup.w₀ : E) (setup.ξ 0 ω)
                  linarith [norm_nonneg (setup.gradL (setup.w₀ : E) (setup.ξ 0 ω))]
                nlinarith
              have h6 : (∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P) ≤ ∫ ω, (G ^ 2 : ℝ) ∂setup.P := by
                apply integral_mono (h_int_sq t) (integrable_const (G ^ 2)) (fun ω => h5 ω)
              have h7 : ∫ ω, (G ^ 2 : ℝ) ∂setup.P = G ^ 2 := by
                simp [integral_const]
              rw [h7] at h6
              exact h6
            have h5 : 0 ≤ η ^ 2 := by positivity
            have h6 : 2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤ (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) - (∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) + η ^ 2 * G ^ 2 := by
              have h7 : (∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) ≤ (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) - 2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) + η ^ 2 * (∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P) := h2
              have h8 : η ^ 2 * (∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P) ≤ η ^ 2 * G ^ 2 := by
                exact mul_le_mul_of_nonneg_left h4 h5
              linarith [h7, h8]
            exact h6
          exact mul_le_mul_of_nonneg_left h_inner (by positivity)
        exact h_int_ineq
      _ = (1 / (T : ℝ)) * ((1 / (2 * η)) * (∑ t ∈ Finset.range T, ((∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) - (∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P)) + ∑ t ∈ Finset.range T, (η ^ 2 * G ^ 2))) := by
        have h_sum_factor : ∑ t ∈ Finset.range T, (1 / (2 * η)) * ((∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) - (∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) + η ^ 2 * G ^ 2) = (1 / (2 * η)) * (∑ t ∈ Finset.range T, ((∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) - (∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P)) + ∑ t ∈ Finset.range T, (η ^ 2 * G ^ 2)) := by
          rw [← Finset.mul_sum]
          rw [Finset.sum_add_distrib]
          <;> ring
        rw [h_sum_factor]
        <;> ring
      _ = (1 / (T : ℝ)) * ((1 / (2 * η)) * ((∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P) - (∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P) + T * η ^ 2 * G ^ 2)) := by
        have h_telescope : ∑ t ∈ Finset.range T, ((∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) - (∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P)) = (∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P) - (∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P) := by
          have h1 : ∀ n, ∑ t ∈ Finset.range n, ((∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) - (∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P)) = (∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P) - (∫ ω, ‖setup.process n ω - wStar‖ ^ 2 ∂setup.P) := by
            intro n
            induction n with
            | zero => simp
            | succ n ih =>
              rw [Finset.sum_range_succ, ih]
              ring
          exact h1 T
        have h_sum_const : ∑ t ∈ Finset.range T, (η ^ 2 * G ^ 2) = (T : ℝ) * η ^ 2 * G ^ 2 := by
          rw [Finset.sum_const]
          rw [nsmul_eq_mul]
          <;> simp [mul_assoc]
          <;> ring_nf
        rw [h_telescope]
        rw [h_sum_const]
        <;> ring_nf
      _ = (1 / (T : ℝ)) * ((1 / (2 * η)) * (‖setup.w₀ - wStar‖ ^ 2 - (∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P) + T * η ^ 2 * G ^ 2)) := by
        have h0 : (∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P) = ‖setup.w₀ - wStar‖ ^ 2 := by
          have h1 : setup.process 0 = fun _ => setup.w₀ := by
            ext ω
            simp [SubgradientSetup.process_zero]
          rw [h1]
          simp [integral_const, setup.hP.measure_univ]
        rw [h0]
      _ ≤ (1 / (T : ℝ)) * ((1 / (2 * η)) * (‖setup.w₀ - wStar‖ ^ 2 + T * η ^ 2 * G ^ 2)) := by
        gcongr
        have h_nonneg : 0 ≤ (∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P) := by
          apply integral_nonneg
          intro ω _
          exact pow_two_nonneg _
        linarith
      _ = ‖setup.w₀ - wStar‖ ^ 2 / (2 * η * T) + η * G ^ 2 / 2 := by
        field_simp [hη_pos.ne', hT.ne']
        <;> ring
        <;> field_simp [hη_pos.ne', hT.ne']
        <;> ring

