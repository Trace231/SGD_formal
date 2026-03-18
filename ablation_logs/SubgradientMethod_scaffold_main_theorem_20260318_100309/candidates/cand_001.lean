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
  have hη_pos' : 0 < η := hη_pos
    have hT_pos : (0 : ℝ) < T := by exact_mod_cast hT

    -- Norm expansion for SGD step
    have h_norm_expand : ∀ t ω,
        ‖setup.process (t + 1) ω - wStar‖ ^ 2 =
        ‖setup.process t ω - wStar‖ ^ 2 - 2 * η * ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := by
      intro t ω
      rw [SubgradientSetup.process_succ setup t]
      simp only [sub_eq_add_neg, norm_sq_eq_inner, inner_add_right, inner_sub_right, inner_smul_right, inner_neg_right]
      simp [hη t]
      ring_nf
      <;> simp [inner_comm]
      <;> ring_nf

    -- Subgradient inequality at each iterate
    have h_subgrad_ineq : ∀ t ω,
        f (setup.process t ω) - f wStar ≤ ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ := by
      intro t ω
      have := hsubgrad (setup.process t ω) (setup.ξ t ω) wStar
      linarith

    -- Per-iteration inequality
    have h_per_iter : ∀ t ω,
        2 * η * (f (setup.process t ω) - f wStar) ≤
        ‖setup.process t ω - wStar‖ ^ 2 - ‖setup.process (t + 1) ω - wStar‖ ^ 2 + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := by
      intro t ω
      have h1 := h_norm_expand t ω
      have h2 := h_subgrad_ineq t ω
      have : 2 * η * (f (setup.process t ω) - f wStar) ≤ 2 * η * ⟪setup.gradL (setup.process t ω) (setup.ξ t ω), setup.process t ω - wStar⟫_ℝ := by
        nlinarith [hη_pos']
      nlinarith [h1, this]

    -- Integrated per-iteration inequality
    have h_int_per_iter : ∀ t,
        2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
        (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) - (∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) +
        η ^ 2 * (∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P) := by
      intro t
      have h_integrable_diff : Integrable (fun ω => ‖setup.process t ω - wStar‖ ^ 2 - ‖setup.process (t + 1) ω - wStar‖ ^ 2) setup.P := by
        apply Integrable.sub
        · exact h_int_norm_sq t
        · exact h_int_norm_sq (t + 1)
      have h_integrable_grad : Integrable (fun ω => ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) setup.P := h_int_sq t
      have h_integrable_f : Integrable (fun ω => f (setup.process t ω)) setup.P := h_int_f t
      have h_ineq : ∀ ω, 2 * η * (f (setup.process t ω) - f wStar) ≤
          ‖setup.process t ω - wStar‖ ^ 2 - ‖setup.process (t + 1) ω - wStar‖ ^ 2 +
          η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := by
        intro ω
        exact h_per_iter t ω
      calc
        2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) =
            ∫ ω, 2 * η * (f (setup.process t ω) - f wStar) ∂setup.P := by
          simp [integral_sub, h_integrable_f, integrable_const (f wStar)]
          <;> ring_nf
        _ ≤ ∫ ω, (‖setup.process t ω - wStar‖ ^ 2 - ‖setup.process (t + 1) ω - wStar‖ ^ 2 +
            η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) ∂setup.P := by
          apply integral_mono_on_univ
          · apply Integrable.add
            · exact h_integrable_diff
            · exact h_integrable_grad.const_mul (η ^ 2)
          · exact integrable_const (0 : ℝ)
          · intro ω _, exact h_ineq ω
        _ = (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) - (∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) +
            η ^ 2 * (∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P) := by
          simp [integral_add, integral_sub, h_integrable_diff, h_integrable_grad]
          <;> ring_nf

    -- Bounded gradient integral
    have h_bounded_integral : ∀ t, ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P ≤ G ^ 2 := by
      intro t
      have h_bound : ∀ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ≤ G ^ 2 := by
        intro ω
        have := hbounded (setup.process t ω) (setup.ξ t ω)
        nlinarith
      calc
        ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P ≤ ∫ ω, G ^ 2 ∂setup.P := by
          apply integral_mono_on_univ
          · exact h_int_sq t
          · exact integrable_const (G ^ 2)
          · intro ω _, exact h_bound ω
        _ = G ^ 2 := by
          simp [setup.hP]

    -- Sum over t ∈ Finset.range T
    have h_sum : ∑ t ∈ Finset.range T, (2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)) ≤
        ‖setup.w₀ - wStar‖ ^ 2 + η ^ 2 * ∑ t ∈ Finset.range T, G ^ 2 := by
      calc
        ∑ t ∈ Finset.range T, (2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)) ≤
            ∑ t ∈ Finset.range T, ((∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) -
                (∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) +
                η ^ 2 * (∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P)) := by
          apply Finset.sum_le_sum
          intro t ht
          exact h_int_per_iter t
        _ = ∑ t ∈ Finset.range T, ((∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) -
                (∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P)) +
            ∑ t ∈ Finset.range T, (η ^ 2 * (∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P)) := by
          rw [Finset.sum_add_distrib]
        _ = (∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P) -
                (∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P) +
            η ^ 2 * ∑ t ∈ Finset.range T, (∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P) := by
          have h_telescope : ∑ t ∈ Finset.range T, ((∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) -
                (∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P)) =
              (∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P) -
                (∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P) := by
            induction' T with T ih
            · simp
            · cases T
              · simp
              · simp_all [Finset.sum_range_succ, add_sub_cancel]
                <;> ring_nf
          rw [h_telescope]
          rw [Finset.sum_mul]
          <;> ring_nf
        _ ≤ (∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P) +
            η ^ 2 * ∑ t ∈ Finset.range T, G ^ 2 := by
          have h_nonneg : 0 ≤ ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P := by
            apply integral_nonneg
            intro ω _
            exact sq_nonneg _
          have h_bound_sum : ∑ t ∈ Finset.range T, (∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P) ≤
              ∑ t ∈ Finset.range T, G ^ 2 := by
            apply Finset.sum_le_sum
            intro t _
            exact h_bounded_integral t
          have h_eta_sq_nonneg : 0 ≤ η ^ 2 := by positivity
          nlinarith
        _ = ‖setup.w₀ - wStar‖ ^ 2 + η ^ 2 * ∑ t ∈ Finset.range T, G ^ 2 := by
          simp [SubgradientSetup.process_zero setup]
          <;> simp [setup.hP]

    -- Final calculation
    calc
      (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) =
          (1 / (2 * η * T)) * ∑ t ∈ Finset.range T, (2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)) := by
        field_simp [hη_pos', hT_pos.ne']
        <;> ring_nf
      _ ≤ (1 / (2 * η * T)) * (‖setup.w₀ - wStar‖ ^ 2 + η ^ 2 * ∑ t ∈ Finset.range T, G ^ 2) := by
        gcongr
        exact h_sum
      _ = (1 / (2 * η * T)) * ‖setup.w₀ - wStar‖ ^ 2 + (1 / (2 * η * T)) * (η ^ 2 * ∑ t ∈ Finset.range T, G ^ 2) := by
        ring_nf
      _ = ‖setup.w₀ - wStar‖ ^ 2 / (2 * η * T) + η * G ^ 2 / 2 := by
        have h_sum_const : ∑ t ∈ Finset.range T, G ^ 2 = (T : ℝ) * G ^ 2 := by
          simp [Finset.sum_const, nsmul_eq_mul]
          <;> field_simp [hT_pos.ne']
          <;> ring_nf
        rw [h_sum_const]
        field_simp [hη_pos', hT_pos.ne']
        <;> ring_nf
        <;> field_simp [hη_pos', hT_pos.ne']
        <;> ring_nf
