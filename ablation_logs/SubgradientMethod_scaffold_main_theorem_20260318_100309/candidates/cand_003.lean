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
    -- Key inequality for each iteration t
    have h_iter_bound : ∀ t < T,
        (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
          (1 / (2 * η)) * (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P -
            ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) + η * G ^ 2 / 2 := by
      intro t ht
      have hη_t : setup.η t = η := hη_const t
      -- Norm expansion: ‖w_{t+1} - w*‖² = ‖w_t - η·g_t - w*‖²
      have h_norm_expand : ∀ ω,
          ‖setup.process (t + 1) ω - wStar‖ ^ 2 =
            ‖setup.process t ω - wStar‖ ^ 2 - 2 * η * ⟪setup.gradL (setup.process t ω) (setup.ξ t ω),
              setup.process t ω - wStar⟫_ℝ + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := by
        intro ω
        calc
          ‖setup.process (t + 1) ω - wStar‖ ^ 2 =
              ‖(setup.process t ω - η • setup.gradL (setup.process t ω) (setup.ξ t ω)) - wStar‖ ^ 2 := by
            rw [SubgradientSetup.process_succ setup t]
            simp
          _ = ‖(setup.process t ω - wStar) - η • setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := by
            rw [sub_sub, sub_eq_add_neg, add_comm]
            simp [sub_eq_add_neg]
          _ = ‖setup.process t ω - wStar‖ ^ 2 - 2 * η * ⟪setup.gradL (setup.process t ω) (setup.ξ t ω),
                setup.process t ω - wStar⟫_ℝ + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := by
            rw [norm_sub_sq_real]
            simp [inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq]
            ring
      -- Subgradient inequality: f(w_t) - f(w*) ≤ ⟨g_t, w_t - w*⟩
      have h_subgrad_ineq : ∀ ω, f (setup.process t ω) - f wStar ≤
          ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ := by
        intro ω
        have := hsubgrad (setup.process t ω) (setup.ξ t ω) wStar
        linarith
      -- Integrate norm expansion
      have h_int_norm : ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P =
          ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P -
            2 * η * ∫ ω, ⟪setup.gradL (setup.process t ω) (setup.ξ t ω),
              setup.process t ω - wStar⟫_ℝ ∂setup.P +
            η ^ 2 * ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P := by
        calc
          ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P =
              ∫ ω, (‖setup.process t ω - wStar‖ ^ 2 - 2 * η * ⟪setup.gradL (setup.process t ω) (setup.ξ t ω),
                setup.process t ω - wStar⟫_ℝ + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) ∂setup.P := by
            congr
            ext ω
            exact h_norm_expand ω
          _ = ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P -
                2 * η * ∫ ω, ⟪setup.gradL (setup.process t ω) (setup.ξ t ω),
                  setup.process t ω - wStar⟫_ℝ ∂setup.P +
                η ^ 2 * ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P := by
            simp [integral_add, integral_sub, integral_smul, h_int_norm_sq t, h_int_norm_sq (t + 1), h_int_sq t]
            ring
      -- Rearrange to isolate inner product term
      have h_inner_bound : 2 * η * ∫ ω, ⟪setup.gradL (setup.process t ω) (setup.ξ t ω),
          setup.process t ω - wStar⟫_ℝ ∂setup.P ≥
            ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P -
              ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P +
              η ^ 2 * ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P := by
        linarith [h_int_norm]
      -- Apply subgradient inequality and integrate
      have h_f_bound : ∫ ω, f (setup.process t ω) ∂setup.P - f wStar ≤
          ∫ ω, ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ ∂setup.P := by
        calc
          ∫ ω, f (setup.process t ω) ∂setup.P - f wStar =
              ∫ ω, (f (setup.process t ω) - f wStar) ∂setup.P := by
            simp [integral_const, hP.volume_eq_one]
          _ ≤ ∫ ω, ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ ∂setup.P := by
            apply integral_mono_on_univ hP
            intro ω _
            exact h_subgrad_ineq ω
            exact h_int_f t
      -- Combine with bounded gradient
      have h_grad_bound : ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P ≤ G ^ 2 := by
        calc
          ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P ≤
              ∫ ω, G ^ 2 ∂setup.P := by
            apply integral_mono_on_univ hP
            intro ω _
            have := hbounded (setup.process t ω) (setup.ξ t ω)
            have : ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ≤ G ^ 2 := by
              have h₁ : ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ≤ G := this
              have h₂ : 0 ≤ ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ := norm_nonneg _
              have h₃ : 0 ≤ G := by linarith [hbounded (setup.process t ω) (setup.ξ t ω)]
              nlinarith
            exact this
          _ = G ^ 2 := by
            simp [integral_const, hP.volume_eq_one]
      -- Final bound for iteration t
      calc
        (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
            ∫ ω, ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ ∂setup.P := h_f_bound
        _ = (1 / (2 * η)) * (2 * η * ∫ ω, ⟪setup.gradL (setup.process t ω) (setup.ξ t ω),
              setup.process t ω - wStar⟫_ℝ ∂setup.P) := by
          field_simp [hη_pos.ne']
          ring
        _ ≥ (1 / (2 * η)) * (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P -
              ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P +
              η ^ 2 * ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P) := by
          gcongr
          exact h_inner_bound
        _ ≥ (1 / (2 * η)) * (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P -
              ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) +
              (1 / (2 * η)) * (η ^ 2 * G ^ 2) := by
          have h₁ : η ^ 2 * ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P ≥
              η ^ 2 * 0 := by
            apply mul_nonneg
            · nlinarith
            · apply integral_nonneg
              intro ω _
              exact sq_nonneg _
          have h₂ : (1 / (2 * η)) * (η ^ 2 * ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P) ≥
              (1 / (2 * η)) * (η ^ 2 * 0) := by
            gcongr
          have h₃ : (1 / (2 * η)) * (η ^ 2 * G ^ 2) = η * G ^ 2 / 2 := by
            field_simp [hη_pos.ne']
            ring
          linarith [h_grad_bound]
        _ = (1 / (2 * η)) * (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P -
              ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) + η * G ^ 2 / 2 := by
          field_simp [hη_pos.ne']
          ring
    -- Sum over t and telescope
    have h_sum_bound : ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
        ∑ t ∈ Finset.range T, ((1 / (2 * η)) * (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P -
          ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) + η * G ^ 2 / 2) := by
      apply Finset.sum_le_sum
      intro t ht
      exact h_iter_bound t (Finset.mem_range.mp ht)
    -- Telescope the sum
    have h_telescope : ∑ t ∈ Finset.range T, ((1 / (2 * η)) * (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P -
        ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P)) =
          (1 / (2 * η)) * (∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P -
            ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P) := by
      calc
        ∑ t ∈ Finset.range T, ((1 / (2 * η)) * (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P -
            ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P)) =
            (1 / (2 * η)) * ∑ t ∈ Finset.range T, (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P -
              ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) := by
          simp [Finset.sum_smul]
        _ = (1 / (2 * η)) * (∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P -
              ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P) := by
          have h_tel : ∑ t ∈ Finset.range T, (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P -
              ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) =
                ∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P -
                  ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P := by
            calc
              ∑ t ∈ Finset.range T, (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P -
                  ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) =
                    ∑ t ∈ Finset.range T, (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) -
                      ∑ t ∈ Finset.range T, (∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) := by
                simp [Finset.sum_sub_distrib]
              _ = ∑ t ∈ Finset.range T, (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) -
                    ∑ t ∈ Finset.Ico 1 (T + 1), (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) := by
                have h_shift : ∑ t ∈ Finset.range T, (∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) =
                    ∑ t ∈ Finset.Ico 1 (T + 1), (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) := by
                  rw [Finset.sum_Ico_eq_sum_range]
                  congr
                  ext t
                  ring
                rw [h_shift]
              _ = ∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P -
                    ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P := by
                simp [Finset.sum_range_succ']
                <;>
                (try decide) <;>
                (try simp_all [Finset.sum_range_succ]) <;>
                (try ring)
          rw [h_tel]
    -- Constant term sum
    have h_const_sum : ∑ t ∈ Finset.range T, (η * G ^ 2 / 2) = (T : ℝ) * (η * G ^ 2 / 2) := by
      simp [Finset.sum_const, nsmul_eq_mul]
      <;> field_simp
      <;> ring
    -- Combine
    have h_main : ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
        (1 /
