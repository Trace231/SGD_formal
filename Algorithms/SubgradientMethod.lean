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

namespace SubgradientSetup

variable (setup : SubgradientSetup E S Ω)

/-- Process alias reusing SGD recursion verbatim (Archetype B pattern). -/
noncomputable def process : ℕ → Ω → E :=
  sgdProcess setup.w₀ setup.η setup.gradL setup.ξ

/-- Measurability of subgradient process (thin wrapper).
Used in: `subgradient_convergence_convex` (infrastructure for independence/variance steps) -/
theorem subgradientProcess_measurable (t : ℕ) : Measurable (setup.process t) :=
  sgdProcess_measurable setup.hξ_meas setup.hgL t

/-- Adaptedness to natural filtration (thin wrapper).
Used in: independence infrastructure (reuses `sgdFiltration` from Main.lean) -/
theorem subgradientProcess_adapted :
    Adapted (sgdFiltration setup.ξ setup.hξ_meas) (fun t => setup.process t) :=
  sgdProcess_adapted setup.hξ_meas setup.hgL

/-- Independence of process(t) from ξ(t) (thin wrapper).
Used in: `subgradient_convergence_convex` (variance bound step via `expectation_norm_sq_gradL_bound`) -/
theorem subgradientProcess_indepFun_xi (t : ℕ) :
    IndepFun (setup.process t) (setup.ξ t) setup.P :=
  sgdProcess_indepFun_xi setup.hξ_meas setup.hξ_indep setup.hgL t

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
  -- ----------------------------------------------------------------
  -- Step 1: Per-step bound via primitive subgradient inequality
  -- ----------------------------------------------------------------
  have hstep : ∀ t < T,
      ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P ≤
        ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P
        - 2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)
        + η ^ 2 * G ^ 2 := fun t ht => by
    -- Pointwise inequality derivation
    have h_ineq : ∀ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ≤
        ‖setup.process t ω - wStar‖ ^ 2
        - 2 * η * (f (setup.process t ω) - f wStar)
        + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := fun ω => by
      -- Norm expansion via Lib.Glue.Algebra.norm_sq_sgd_step
      have h_expand : ‖setup.process (t + 1) ω - wStar‖ ^ 2 =
          ‖setup.process t ω - wStar‖ ^ 2
          - 2 * setup.η t * ⟪setup.process t ω - wStar,
              setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ
          + (setup.η t) ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := by
        rw [show setup.process (t + 1) ω =
            setup.process t ω - setup.η t • setup.gradL (setup.process t ω) (setup.ξ t ω) by
              simp [SubgradientSetup.process, sgdProcess]]
        exact norm_sq_sgd_step _ _ _ _
      -- Primitive subgradient inequality at y = wStar
      have h_ineq_sub := hsubgrad (setup.process t ω) (setup.ξ t ω) wStar
      -- Rearrange: f wStar ≥ f w + ⟪g, wStar - w⟫
      -- Note: wStar - w = -(w - wStar), so ⟪g, wStar - w⟫ = -⟪g, w - wStar⟫
      have h_inner_bound : f (setup.process t ω) - f wStar ≤
          ⟪setup.gradL (setup.process t ω) (setup.ξ t ω),
            setup.process t ω - wStar⟫_ℝ := by
        have h_neg : wStar - setup.process t ω = -(setup.process t ω - wStar) := by abel
        rw [h_neg, inner_neg_right] at h_ineq_sub
        linarith
      -- Bound inner product term (critical inequality direction)
      have h_term_bound : -2 * setup.η t *
          ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ ≤
          -2 * η * (f (setup.process t ω) - f wStar) := by
        rw [hη t, real_inner_comm]
        nlinarith [h_inner_bound, hη_pos]
      -- Combine expansion and inequality
      calc ‖setup.process (t + 1) ω - wStar‖ ^ 2
          = ‖setup.process t ω - wStar‖ ^ 2
            - 2 * setup.η t * ⟪setup.process t ω - wStar,
                setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ
            + (setup.η t) ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := h_expand
        _ ≤ ‖setup.process t ω - wStar‖ ^ 2
            - 2 * η * (f (setup.process t ω) - f wStar)
            + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := by
            gcongr <;> (try rw [hη t]; try ring_nf) <;> exact h_term_bound
    -- Integrate pointwise inequality
    have h_rhs_int : Integrable (fun ω =>
        ‖setup.process t ω - wStar‖ ^ 2
        - 2 * η * (f (setup.process t ω) - f wStar)
        + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) setup.P :=
      ((h_int_norm_sq t).sub ((h_int_f t).sub (integrable_const _)).const_mul (2 * η))).add
        ((h_int_sq t).const_mul (η ^ 2))
    have h_int_ineq : ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P ≤
        ∫ ω, (‖setup.process t ω - wStar‖ ^ 2
          - 2 * η * (f (setup.process t ω) - f wStar)
          + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) ∂setup.P :=
      integral_mono (h_int_norm_sq (t + 1)) h_rhs_int h_ineq
    -- Linearity of integral
    have h_lin : ∫ ω, (‖setup.process t ω - wStar‖ ^ 2
        - 2 * η * (f (setup.process t ω) - f wStar)
        + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) ∂setup.P =
      ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P
      - 2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)
      + η ^ 2 * ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P := by
      have h1 : ∫ ω, (‖setup.process t ω - wStar‖ ^ 2 -
          2 * η * (f (setup.process t ω) - f wStar)) ∂setup.P =
          ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P -
          ∫ ω, (2 * η * (f (setup.process t ω) - f wStar)) ∂setup.P :=
        integral_sub (h_int_norm_sq t) ((h_int_f t).sub (integrable_const _)).const_mul (2 * η)
      have h2 : ∫ ω, (2 * η * (f (setup.process t ω) - f wStar)) ∂setup.P =
          2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) := by
        rw [integral_const_mul, integral_sub (h_int_f t) (integrable_const _),
            integral_const, probReal_univ, mul_one]
      have h3 : ∫ ω, (η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) ∂setup.P =
          η ^ 2 * ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P :=
        integral_const_mul _ _
      linarith [h1, h2, h3]
    rw [h_lin] at h_int_ineq
    -- Variance bound via Pattern I (GLUE_TRICKS.md §3)
    have hvar := hasBoundedVariance_of_pointwise_bound hbounded
    have h_indep := SubgradientSetup.subgradientProcess_indepFun_xi setup t
    have h_dist := (setup.hξ_ident t).map_eq
    have h_wt_meas := SubgradientSetup.subgradientProcess_measurable setup t
    have h_ξt_meas := setup.hξ_meas t
    have hE_sq : ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P ≤ G ^ 2 :=
      expectation_norm_sq_gradL_bound
        (fun w => (hvar w).2) h_indep h_dist h_wt_meas h_ξt_meas setup.hgL (h_int_sq t)
    -- Final per-step bound
    calc _ ≤ ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P
          - 2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)
          + η ^ 2 * G ^ 2 := by
        gcongr <;> linarith [hE_sq]
  -- ----------------------------------------------------------------
  -- Step 2: Sum and telescope
  -- ----------------------------------------------------------------
  have hsum : 2 * η * ∑ t ∈ Finset.range T,
      (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
    ‖setup.w₀ - wStar‖ ^ 2 -
      ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P +
      (T : ℝ) * (η ^ 2 * G ^ 2) := by
    set a := fun t => ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P
    set gap := fun t => ∫ ω, f (setup.process t ω) ∂setup.P - f wStar
    have h_rearr : ∀ t, t < T → 2 * η * gap t ≤ (a t - a (t + 1)) + η ^ 2 * G ^ 2 :=
      fun t ht => by simp only [a, gap]; linarith [hstep t ht]
    have h_sum_le := Finset.sum_le_sum (fun t ht => h_rearr t (Finset.mem_range.mp ht))
    rw [← Finset.mul_sum] at h_sum_le
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h_sum_le
    have h_tele : ∑ t ∈ Finset.range T, (a t - a (t + 1)) = a 0 - a T := by
      simp_rw [show ∀ t, a t - a (t + 1) = -(a (t + 1) - a t) from fun t => by ring]
      rw [Finset.sum_neg_distrib, Finset.sum_range_sub]; ring
    rw [h_tele] at h_sum_le
    have h_init : a 0 = ‖setup.w₀ - wStar‖ ^ 2 := by
      simp [a, SubgradientSetup.process, sgdProcess, integral_const, probReal_univ]
    rw [h_init] at h_sum_le; linarith
  -- ----------------------------------------------------------------
  -- Step 3: Drop non-negative term and rearrange
  -- ----------------------------------------------------------------
  have h_norm_nonneg : 0 ≤ ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P :=
    integral_nonneg fun ω => sq_nonneg _
  have h_drop : 2 * η * ∑ t ∈ Finset.range T,
      (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
    ‖setup.w₀ - wStar‖ ^ 2 + (T : ℝ) * (η ^ 2 * G ^ 2) := by
    linarith [hsum, h_norm_nonneg]
  have hT_pos : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hη2_pos : (0 : ℝ) < 2 * η := by linarith
  rw [one_div, inv_mul_le_iff₀ hT_pos]
  have h_rhs : (T : ℝ) * (‖setup.w₀ - wStar‖ ^ 2 / (2 * η * T) + η * G ^ 2 / 2) =
      (‖setup.w₀ - wStar‖ ^ 2 + (T : ℝ) * (η ^ 2 * G ^ 2)) / (2 * η) := by
    field_simp
  rw [h_rhs, le_div_iff₀ hη2_pos]; linarith [h_drop]