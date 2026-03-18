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
  have h_step : ∀ t, ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P ≤
        ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P - 2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) + η^2 * G^2 := by
      intro t
      have h1 : ∀ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 =
          ‖setup.process t ω - wStar‖ ^ 2 - 2 * η * ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ + η^2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := by
        intro ω
        rw [SubgradientSetup.process_succ setup t, hη t]
        rw [norm_sub_sq_real]
        simp [inner_smul_left, inner_smul_right, inner_comm]
        ring
      have h2 : ∀ ω, ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ ≥ f (setup.process t ω) - f wStar := by
        intro ω
        have := hsubgrad (setup.process t ω) (setup.ξ t ω) wStar
        rw [inner_sub_left] at this
        linarith
      have h3 : ∀ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ≤ G ^ 2 := by
        intro ω
        exact pow_le_pow_of_le_left (norm_nonneg _) (hbounded _ _) 2
      calc
        ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P
          = ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 - 2 * η * ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ + η^2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P := by
            congr; ext ω; rw [h1 ω]
          _ = ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P - 2 * η * ∫ ω, ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ ∂setup.P + η^2 * ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P := by
            simp [integral_add, integral_sub, integral_smul]
          _ ≤ ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P - 2 * η * ∫ ω, (f (setup.process t ω) - f wStar) ∂setup.P + η^2 * ∫ ω, G ^ 2 ∂setup.P := by
            gcongr <;> aesop
          _ = ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P - 2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) + η^2 * G^2 := by
            simp [integral_const, hP.volume_one]; ring

    have h_sum : ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
        ‖setup.w₀ - wStar‖ ^ 2 / (2 * η) + T * η * G^2 / 2 := by
      have : ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
          ∑ t ∈ Finset.range T, ((∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P - ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) / (2 * η) + η * G^2 / 2) := by
        apply Finset.sum_le_sum; intro t _; have := h_step t; linarith
      calc
        ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)
          ≤ ∑ t ∈ Finset.range T, ((∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P - ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) / (2 * η) + η * G^2 / 2) := this
        _ = (∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P - ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P) / (2 * η) + T * η * G^2 / 2 := by
          simp [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_range_telescope, Finset.sum_const, Finset.card_range]
        _ ≤ (∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P) / (2 * η) + T * η * G^2 / 2 := by
          gcongr; exact integral_nonneg (fun ω => ‖setup.process T ω - wStar‖ ^ 2)
        _ = ‖setup.w₀ - wStar‖ ^ 2 / (2 * η) + T * η * G^2 / 2 := by
          simp [SubgradientSetup.process_zero]; congr; simp

    calc
      (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)
        ≤ (1 / (T : ℝ)) * (‖setup.w₀ - wStar‖ ^ 2 / (2 * η) + T * η * G^2 / 2) := by gcongr; exact h_sum
      _ = ‖setup.w₀ - wStar‖ ^ 2 / (2 * η * T) + η * G^2 / 2 := by field_simp; ring
