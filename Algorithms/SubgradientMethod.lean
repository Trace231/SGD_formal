import Main
import Lib.Glue.Algebra
import Lib.Glue.Probability
import Lib.Layer0.IndepExpect
import Lib.Glue.Staging.SubgradientMethod

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

namespace SubgradientSetup

variable (setup : SubgradientSetup E S Ω)

/-- Self-contained recursive process definition for subgradient method (Archetype B). -/
noncomputable def process : ℕ → Ω → E
  | 0, _ => setup.w₀
  | t + 1, ω => process t ω - setup.η t • setup.gradL (process t ω) (setup.ξ t ω)

@[simp] theorem process_zero (ω : Ω) : process 0 ω = w₀ := rfl
@[simp] theorem process_succ (t : ℕ) (ω : Ω) :
    process (t + 1) ω = process t ω - η t • gradL (process t ω) (ξ t ω) := rfl

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
  haveI := setup.hP
  -- STEP A: Per-step inequality for each t < T
  have hstep : ∀ t < T,
      ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P ≤
        ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P
        - 2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)
        + η ^ 2 * G ^ 2 := fun t ht => by
    -- A1. Pointwise norm expansion
    have h_expand : ∀ ω,
        ‖setup.process (t + 1) ω - wStar‖ ^ 2 =
          ‖setup.process t ω - wStar‖ ^ 2
          - 2 * setup.η t * ⟪setup.gradL (setup.process t ω) (setup.ξ t ω),
              setup.process t ω - wStar⟫_ℝ
          + (setup.η t) ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 :=
      fun ω => by
        simp [process_succ]
        rw [norm_sq_sgd_step (setup.process t ω)
          (setup.gradL (setup.process t ω) (setup.ξ t ω)) wStar (setup.η t)]
        rw [real_inner_comm]
        <;> ring
    -- A2. Subgradient inequality → inner product lower bound
    have h_inner_lb : ∀ ω,
        ⟪setup.gradL (setup.process t ω) (setup.ξ t ω),
          setup.process t ω - wStar⟫_ℝ ≥ f (setup.process t ω) - f wStar := by
      intro ω
      have h_sub := hsubgrad (setup.process t ω) (setup.ξ t ω) wStar
      have : wStar - setup.process t ω = -(setup.process t ω - wStar) := by abel
      rw [this, inner_neg_right] at h_sub
      linarith
    -- A3. Substitute lower bound into expansion
    have h_pointwise : ∀ ω,
        ‖setup.process (t + 1) ω - wStar‖ ^ 2 ≤
          ‖setup.process t ω - wStar‖ ^ 2
          - 2 * setup.η t * (f (setup.process t ω) - f wStar)
          + (setup.η t) ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := by
      intro ω
      rw [h_expand ω]
      have hηt_pos : 0 < setup.η t := by rw [hη t]; exact hη_pos
      have : -2 * setup.η t * ⟪setup.gradL (setup.process t ω) (setup.ξ t ω),
          setup.process t ω - wStar⟫_ℝ ≤
          -2 * setup.η t * (f (setup.process t ω) - f wStar) := by
        nlinarith [h_inner_lb ω, hηt_pos]
      nlinarith
    -- A4. Integrate + linearity
    have h_int_next := h_int_norm_sq (t + 1)
    have h_int_curr := h_int_norm_sq t
    have h_int_f_t := h_int_f t
    have h_int_sq_t := h_int_sq t
    have h_int_const : Integrable (fun _ : Ω => (f wStar : ℝ)) setup.P :=
      integrable_const _
    calc
      ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P
        ≤ ∫ ω, (‖setup.process t ω - wStar‖ ^ 2
            - 2 * setup.η t * (f (setup.process t ω) - f wStar)
            + (setup.η t) ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) ∂setup.P :=
          integral_mono h_int_next
            (h_int_curr.add
              ((h_int_f_t.const_mul (-2 * setup.η t)).add (h_int_const.const_mul (2 * setup.η t)))
              |>.add (h_int_sq_t.const_mul ((setup.η t) ^ 2))) h_pointwise
      _ = ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P
          - 2 * setup.η t * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)
          + (setup.η t) ^ 2 * ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P := by
        have h_int_term2 : Integrable (fun ω => -2 * setup.η t * (f (setup.process t ω) - f wStar)) setup.P :=
          (h_int_f_t.const_mul (-2 * setup.η t)).add (h_int_const.const_mul (2 * setup.η t))
        have h_int_term3 : Integrable (fun ω => (setup.η t) ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) setup.P :=
          h_int_sq_t.const_mul ((setup.η t) ^ 2)
        have h_int_sum : Integrable (fun ω => ‖setup.process t ω - wStar‖ ^ 2
            - 2 * setup.η t * (f (setup.process t ω) - f wStar)
            + (setup.η t) ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) setup.P :=
          h_int_curr.add h_int_term2 |>.add h_int_term3
        rw [integral_add, integral_sub, integral_const_mul, integral_sub, integral_const_mul, integral_const_mul]
        <;> simp [mul_assoc]
        <;> try apply integrable_const
        <;> try assumption
      _ ≤ ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P
          - 2 * setup.η t * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)
          + (setup.η t) ^ 2 * G ^ 2 := by
        -- A5. Apply Pattern I glue lemma
        have h_var_bound : ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P ≤ G ^ 2 := by
          apply integral_mono (integrable_const _) h_int_sq_t
          intro ω
          have h1 : ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ≤ G := hbounded _ _
          nlinarith [sq_nonneg (‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖), h1]
        have hηt_pos : 0 < setup.η t := by rw [hη t]; exact hη_pos
        nlinarith [h_var_bound]
    rw [hη t] at this
    exact this
  -- STEP B: Sum + telescope
  have hsum : 2 * η * ∑ t ∈ Finset.range T,
      (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
    ‖setup.w₀ - wStar‖ ^ 2 + (T : ℝ) * (η ^ 2 * G ^ 2) := by
    have hT_pos : (0 : ℝ) < T := Nat.cast_pos.mpr hT
    have h_tel : ∑ t ∈ Finset.range T,
        (∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P -
          ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) =
        ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P - ∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P := by
      rw [Finset.sum_range_sub, SubgradientSetup.process, sgdProcess_zero]
      <;> simp
    have h_tel_bound : ∑ t ∈ Finset.range T,
        (∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P -
          ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P) ≤
        ∑ t ∈ Finset.range T, (-2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) + η ^ 2 * G ^ 2) := by
      apply Finset.sum_le_sum
      intro t ht
      have hst := hstep t (Finset.mem_range.mp ht)
      linarith
    have h_nonneg : 0 ≤ ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P :=
      integral_nonneg (h_int_norm_sq T) (fun _ => norm_sq_nonneg _ _)
    have h_w0 : ∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P = ‖setup.w₀ - wStar‖ ^ 2 := by
      rw [process_zero]
      simp
    calc
      2 * η * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)
        = ∑ t ∈ Finset.range T, (2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)) := by
          rw [Finset.mul_sum]
      _ ≤ ∑ t ∈ Finset.range T, (η ^ 2 * G ^ 2 -
          (∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P -
            ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P)) := by
        apply Finset.sum_le_sum
        intro t ht
        have hst := hstep t (Finset.mem_range.mp ht)
        linarith
      _ = (T : ℝ) * (η ^ 2 * G ^ 2) -
          (∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P - ∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
        <;> simp [h_tel]
      _ ≤ (T : ℝ) * (η ^ 2 * G ^ 2) + ‖setup.w₀ - wStar‖ ^ 2 := by
        rw [h_w0]
        linarith [h_nonneg]
  -- STEP C: Final algebraic rearrangement
  have hT_pos : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  calc
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)
      = (1 / (T : ℝ)) * (1 / (2 * η)) * (2 * η * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)) := by
        field_simp [hη_pos.ne', hT_pos.ne']
        <;> ring
      _ ≤ (1 / (T : ℝ)) * (1 / (2 * η)) * (‖setup.w₀ - wStar‖ ^ 2 + (T : ℝ) * (η ^ 2 * G ^ 2)) := by
        gcongr
        exact hsum
      _ = ‖setup.w₀ - wStar‖ ^ 2 / (2 * η * T) + η * G ^ 2 / 2 := by
        field_simp [hη_pos.ne', hT_pos.ne']
        <;> ring
