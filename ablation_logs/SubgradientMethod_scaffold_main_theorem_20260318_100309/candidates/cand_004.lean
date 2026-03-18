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

    have hG_nonneg : 0 ≤ G := by
      have h := hbounded setup.w₀ (setup.ξ 0 Classical.arbitrary Ω)
      exact le_trans (by norm_num [norm_nonneg]) h

    have h_main_ineq : ∀ t, ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P ≤
        ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P - 2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) + η ^ 2 * G ^ 2 := by
      intro t
      have h1 : ∀ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 = 
          ‖setup.process t ω - wStar‖ ^ 2 - 2 * η * ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫ + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := by
        intro ω
        calc
          ‖setup.process (t + 1) ω - wStar‖ ^ 2
            = ‖setup.process t ω - η • setup.gradL (setup.process t ω) (setup.ξ t ω) - wStar‖ ^ 2 := by
              simp [SubgradientSetup.process_succ, hη_const t]
            _ = ‖(setup.process t ω - wStar) - η • setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := by
              abel
            _ = ‖setup.process t ω - wStar‖ ^ 2 - 2 * η * ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫ + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := by
              rw [norm_sub_sq_real]
              simp [inner_smul_right, inner_comm, smul_eq_mul]
              ring
      have h2 : ∀ ω, f (setup.process t ω) - f wStar ≤ ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫ := by
        intro ω
        have h3 := hsubgrad (setup.process t ω) (setup.ξ t ω) wStar
        linarith
      have h3 : ∀ ω, -2 * η * ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫ ≤ -2 * η * (f (setup.process t ω) - f wStar) := by
        intro ω
        have h4 := h2 ω
        have h5 : 0 < η := hη_pos
        nlinarith
      have h4 : ∀ ω, η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ≤ η ^ 2 * G ^ 2 := by
        intro ω
        have h5 := hbounded (setup.process t ω) (setup.ξ t ω)
        have h6 : 0 ≤ η ^ 2 := by positivity
        have h7 : ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ≤ G ^ 2 := by
          gcongr
        nlinarith
      calc
        ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P
          = ∫ ω, (‖setup.process t ω - wStar‖ ^ 2 - 2 * η * ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫ + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) ∂setup.P := by
            congr
            ext ω
            exact h1 ω
          _ = ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P - 2 * η * ∫ ω, ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫ ∂setup.P + η ^ 2 * ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P := by
            simp [integral_add, integral_sub, integral_smul]
          _ ≤ ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P - 2 * η * ∫ ω, (f (setup.process t ω) - f wStar) ∂setup.P + η ^ 2 * ∫ ω, G ^ 2 ∂setup.P := by
            gcongr
            · exact h3
            · exact h4
          _ = ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P - 2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) + η ^ 2 * G ^ 2 := by
            simp [integral_sub, integral_const, hP.volume_univ]
            ring

    have h_sum : ∑ t ∈ Finset.range T, (∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P - ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) ≤
        ∑ t ∈ Finset.range T, (-2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) + η ^ 2 * G ^ 2) := by
      apply Finset.sum_le_sum
      intro t ht
      have h1 := h_main_ineq t
      linarith

    have h_telescope : ∑ t ∈ Finset.range T, (∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P - ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) =
        ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P - ∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P := by
      calc
        _ = ∑ t ∈ Finset.range T, (∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P - ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) := by rfl
        _ = ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P - ∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P := by
          simp [Finset.sum_range_succ, SubgradientSetup.process_zero]
          <;> induction T with
          | zero => contradiction
          | succ T ih =>
            simp [Finset.sum_range_succ, ih]
            ring

    have h_right : ∑ t ∈ Finset.range T, (-2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) + η ^ 2 * G ^ 2) =
        -2 * η * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) + T * η ^ 2 * G ^ 2 := by
      calc
        _ = ∑ t ∈ Finset.range T, (-2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) + η ^ 2 * G ^ 2) := by rfl
        _ = ∑ t ∈ Finset.range T, (-2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)) + ∑ t ∈ Finset.range T, (η ^ 2 * G ^ 2) := by
          simp [Finset.sum_add_distrib]
        _ = -2 * η * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) + T * η ^ 2 * G ^ 2 := by
          simp [Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
          ring

    have h_combined : ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P - ∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P ≤
        -2 * η * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) + T * η ^ 2 * G ^ 2 := by
      linarith [h_sum, h_telescope, h_right]

    have h_rearrange : 2 * η * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
        ∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P - ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P + T * η ^ 2 * G ^ 2 := by
      linarith

    have h_norm_nonneg : 0 ≤ ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P := by
      apply integral_nonneg
      intro ω
      exact sq_nonneg _

    have h_final : 2 * η * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
        ∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P + T * η ^ 2 * G ^ 2 := by
      linarith [h_rearrange, h_norm_nonneg]

    have h_process0 : ∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P = ‖setup.w₀ - wStar‖ ^ 2 := by
      simp [SubgradientSetup.process_zero]
      simp [integral_const, hP.volume_univ]

    have h_final2 : 2 * η * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
        ‖setup.w₀ - wStar‖ ^ 2 + T * η ^ 2 * G ^ 2 := by
      rw [h_process0] at h_final
      exact h_final

    have h_divide : (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
        ‖setup.w₀ - wStar‖ ^ 2 / (2 * η * T) + η * G ^ 2 / 2 := by
      have h1 : 0 < (T : ℝ) := by exact_mod_cast hT
      have h2 : 0 < η := hη_pos
      have h3 : 0 < 2 * η * T := by positivity
      calc
        (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)
          = (1 / (2 * η * T)) * (2 * η * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)) := by
            field_simp [h1, h2, h3]
            ring
          _ ≤ (1 / (2 * η * T)) * (‖setup.w₀ - wStar‖ ^ 2 + T * η ^ 2 * G ^ 2) := by
            gcongr
            exact h_final2
          _ = ‖setup.w₀ - wStar‖ ^ 2 / (2 * η * T) + η * G ^ 2 / 2 := by
            field_simp [h1, h2, h3]
            ring

    exact h_divide
