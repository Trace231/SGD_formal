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
theorem process_zero : process setup 0 = fun _ => setup.w₀ := rfl
@[simp]
theorem process_succ (t : ℕ) : process setup (t + 1) = fun ω => process setup t ω - setup.η t • setup.gradL (process setup t ω) (setup.ξ t ω) := rfl

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
  have h_expand : ∀ t ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 =
      ‖setup.process t ω - wStar‖ ^ 2 - 2 * η * ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := by
    intro t ω
    simp [setup.process_succ t, hη t]
    exact norm_sq_sgd_step (setup.process t ω) (setup.gradL (setup.process t ω) (setup.ξ t ω)) wStar η
  have h_subgrad_ineq : ∀ t ω, f (setup.process t ω) - f wStar ≤ ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ := by
    intro t ω
    have h1 := hsubgrad (setup.process t ω) (setup.ξ t ω) wStar
    have h2 : ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), wStar - setup.process t ω⟫_ℝ = -⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ := by
      rw [← inner_neg_right, neg_sub]
    linarith
  have h_combined : ∀ t ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ≤ ‖setup.process t ω - wStar‖ ^ 2 - 2 * η * (f (setup.process t ω) - f wStar) + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := by
    intro t ω
    have h1 := h_expand t ω
    have h2 := h_subgrad_ineq t ω
    have h3 : -2 * η * ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ ≤ -2 * η * (f (setup.process t ω) - f wStar) := by
      have h4 : ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ = ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ := by
        rw [real_inner_comm (setup.process t ω - wStar) (setup.gradL (setup.process t ω) (setup.ξ t ω))]
      rw [h4]
      nlinarith [hη_pos]
    nlinarith
  have h_int_ineq : ∀ t, ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P ≤
      ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P - 2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) + η ^ 2 * ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P := by
    intro t
    haveI : IsProbabilityMeasure setup.P := setup.hP
    have h1 : Integrable (fun ω => ‖setup.process (t + 1) ω - wStar‖ ^ 2) setup.P := h_int_norm_sq (t + 1)
    have h2 : Integrable (fun ω => ‖setup.process t ω - wStar‖ ^ 2) setup.P := h_int_norm_sq t
    have h3 : Integrable (fun ω => f (setup.process t ω)) setup.P := h_int_f t
    have h4 : Integrable (fun ω => ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) setup.P := h_int_sq t
    have h5 : Integrable (fun ω : Ω => (2 : ℝ) * η * (f (setup.process t ω) - f wStar)) setup.P := by
      apply Integrable.const_mul
      exact h3.sub (integrable_const _)
    have h6 : Integrable (fun ω : Ω => η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) setup.P := by
      apply Integrable.const_mul
      exact h4
    have h_regroup : ∀ ω, (‖setup.process t ω - wStar‖ ^ 2 - 2 * η * (f (setup.process t ω) - f wStar) + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) =
        (‖setup.process t ω - wStar‖ ^ 2 + (-(2 * η * (f (setup.process t ω) - f wStar)) + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2)) := by
      intro ω; ring
    calc
      ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P ≤ ∫ ω, (‖setup.process t ω - wStar‖ ^ 2 - 2 * η * (f (setup.process t ω) - f wStar) + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) ∂setup.P :=
        integral_mono h1 (by apply Integrable.add; apply Integrable.sub; exact h2; exact h5; exact h6) (fun ω => h_combined t ω)
      _ = ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P + (∫ ω, -(2 * η * (f (setup.process t ω) - f wStar)) ∂setup.P + ∫ ω, η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P) := by
        have h7 : Integrable (fun ω => -(2 * η * (f (setup.process t ω) - f wStar))) setup.P := by
          apply Integrable.neg
          apply Integrable.const_mul
          exact h3.sub (integrable_const _)
        have h8 : Integrable (fun ω => -(2 * η * (f (setup.process t ω) - f wStar)) + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) setup.P := by
          apply Integrable.add
          · exact h7
          · exact h6
        rw [integral_congr_ae (Filter.Eventually.of_forall h_regroup)]
        rw [integral_add h2 h8]
        rw [integral_add h7 h6]
      _ = ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P + (-(2 * η) * ∫ ω, (f (setup.process t ω) - f wStar) ∂setup.P + η ^ 2 * ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P) := by
        have h_diff_int : Integrable (fun ω => f (setup.process t ω) - f wStar) setup.P := h3.sub (integrable_const _)
        have h9 : ∫ ω, -(2 * η * (f (setup.process t ω) - f wStar)) ∂setup.P = -(2 * η) * ∫ ω, (f (setup.process t ω) - f wStar) ∂setup.P := by
          have h_int : Integrable (fun ω => (2 : ℝ) * η * (f (setup.process t ω) - f wStar)) setup.P := by
            apply Integrable.const_mul
            exact h_diff_int
          calc
            ∫ ω, -(2 * η * (f (setup.process t ω) - f wStar)) ∂setup.P = ∫ ω, -((2 : ℝ) * η * (f (setup.process t ω) - f wStar)) ∂setup.P := by simp
            _ = -∫ ω, (2 : ℝ) * η * (f (setup.process t ω) - f wStar) ∂setup.P := by
              simp_rw [integral_neg]
            _ = -((2 : ℝ) * η * ∫ ω, (f (setup.process t ω) - f wStar) ∂setup.P) := by
              simp_rw [integral_const_mul]
            _ = -(2 * η) * ∫ ω, (f (setup.process t ω) - f wStar) ∂setup.P := by ring
        rw [h9]
        have h10 : ∫ ω, η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P = η ^ 2 * ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P := by
          simp_rw [integral_const_mul]
        rw [h10]
      _ = ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P - 2 * η * ∫ ω, (f (setup.process t ω) - f wStar) ∂setup.P + η ^ 2 * ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P := by
        ring_nf
      _ = ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P - 2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) + η ^ 2 * ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P := by
        simp [integral_sub, h3, integrable_const]
  have h_variance_bound : ∀ t, ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P ≤ G ^ 2 := by
    intro t
    haveI : IsProbabilityMeasure setup.P := setup.hP
    have h1 : ∀ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ≤ G := by
      intro ω
      exact hbounded (setup.process t ω) (setup.ξ t ω)
    have h2 : ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P ≤ ∫ ω, G ^ 2 ∂setup.P := by
      apply integral_mono (h_int_sq t) (integrable_const _) (fun ω => pow_le_pow_left₀ (norm_nonneg _) (h1 ω) 2)
    calc
      ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P ≤ ∫ ω, G ^ 2 ∂setup.P := h2
      _ = G ^ 2 := by simp [integral_const]
  have h_sum_ineq : ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
      (‖setup.w₀ - wStar‖ ^ 2 - ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P) / (2 * η) + T * η * G ^ 2 / 2 := by
    have h1 : ∀ t ∈ Finset.range T, 2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
        ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P - ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P + η ^ 2 * G ^ 2 := by
      intro t ht
      have h2 := h_int_ineq t
      have h3 := h_variance_bound t
      nlinarith [hη_pos]
    calc
      ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) =
          ∑ t ∈ Finset.range T, (2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)) / (2 * η) := by
        apply Finset.sum_congr rfl
        intro t ht
        field_simp [hη_pos.ne']
      _ ≤ ∑ t ∈ Finset.range T, ((∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P - ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P + η ^ 2 * G ^ 2) / (2 * η)) := by
        apply Finset.sum_le_sum
        intro t ht
        exact div_le_div_of_nonneg_right (h1 t ht) (by nlinarith [hη_pos]) (by nlinarith [hη_pos])
      _ = (1 / (2 * η)) * ∑ t ∈ Finset.range T, (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P - ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P + η ^ 2 * G ^ 2) := by
        rw [div_eq_mul_inv, Finset.sum_mul]
      _ = (1 / (2 * η)) * (∑ t ∈ Finset.range T, (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P - ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) + ∑ t ∈ Finset.range T, (η ^ 2 * G ^ 2)) := by
        rw [Finset.sum_add_distrib]
      _ = (∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P - ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P) / (2 * η) +
          T * (η ^ 2 * G ^ 2 / (2 * η)) := by
        rw [Finset.sum_range_sub' (fun t => ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P)]
        simp [Finset.sum_const, Finset.card_range]
      _ = (‖setup.w₀ - wStar‖ ^ 2 - ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P) / (2 * η) + T * η * G ^ 2 / 2 := by
        have h2 : ∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P = ‖setup.w₀ - wStar‖ ^ 2 := by
          rw [setup.process_zero]
          simp [integral_const]
        rw [h2]
        field_simp [hη_pos.ne']
        ring
  calc
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
        (1 / (T : ℝ)) * ((‖setup.w₀ - wStar‖ ^ 2 - ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P) / (2 * η) + T * η * G ^ 2 / 2) := by
      gcongr
      exact h_sum_ineq
    _ = (‖setup.w₀ - wStar‖ ^ 2 - ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P) / (2 * η * T) + η * G ^ 2 / 2 := by
      field_simp [hT.ne', hη_pos.ne']
      ring
    _ ≤ ‖setup.w₀ - wStar‖ ^ 2 / (2 * η * T) + η * G ^ 2 / 2 := by
      have h1 : 0 ≤ ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P := by
        apply integral_nonneg
        exact fun ω => sq_nonneg _
      have h2 : (‖setup.w₀ - wStar‖ ^ 2 - ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P) / (2 * η * T) ≤ ‖setup.w₀ - wStar‖ ^ 2 / (2 * η * T) := by
        apply div_le_div_of_nonneg_right
        · nlinarith
        · nlinarith [hη_pos, hT]
        · nlinarith [hη_pos, hT]
      nlinarith
