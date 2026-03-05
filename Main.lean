import Mathlib.Analysis.InnerProductSpace.Basic
import SmoothDescent
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Data.NNReal.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Strong
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import IndepExpect
import ConvexGradient


open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

/-!
# Stochastic Gradient Descent — Algorithm Formalization

We formalize SGD as a discrete-time stochastic process on a real Hilbert space `E`,
with IID sampling from a sample space `S`. Convergence analysis is not addressed here.

## Main definitions

* `sgdProcess` — The SGD iteration as a random process `ℕ → Ω → E`
* `SGDSetup` — Packages all data and IID assumptions
* `sgdFiltration` — The natural filtration `ℱ_t = σ(ξ₀, …, ξ_{t−1})`
* `IsUnbiased`, `HasBoundedVariance`, `IsLSmooth` — Standard assumptions
-/

-- ============================================================================
-- Section 1 : Space Setup
-- ============================================================================

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

variable {S : Type*} [MeasurableSpace S]

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

-- ============================================================================
-- Section 2 : SGD Process Definition
-- ============================================================================

/-- The SGD iteration as a stochastic process.

* `w₀`    : initial parameter
* `η t`   : learning rate at step `t`
* `gradL` : stochastic gradient (deterministic in `(w, s)`)
* `ξ t`   : random sample drawn at step `t`

Returns `ℕ → Ω → E` where each `sgdProcess … t` is a random variable. -/
noncomputable def sgdProcess (w₀ : E) (η : ℕ → ℝ)
    (gradL : E → S → E) (ξ : ℕ → Ω → S) : ℕ → Ω → E
  | 0 => fun _ => w₀
  | t + 1 => fun ω =>
      let w_t := sgdProcess w₀ η gradL ξ t ω
      w_t - (η t) • gradL w_t (ξ t ω)

-- ============================================================================
-- Section 3 : SGD Setup (data + IID assumptions)
-- ============================================================================

/-- Complete SGD setup: initial point, learning rate schedule,
stochastic gradient oracle, true gradient, and IID random samples. -/
structure SGDSetup
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E]
    (S : Type*) [MeasurableSpace S]
    (Ω : Type*) [MeasurableSpace Ω] where
  w₀ : E
  η : ℕ → ℝ
  gradL : E → S → E
  gradF : E → E
  ξ : ℕ → Ω → S
  P : Measure Ω
  hP : IsProbabilityMeasure P
  hξ_meas : ∀ t, Measurable (ξ t)
  hξ_indep : iIndepFun (β := fun _ => S) ξ P
  hξ_ident : ∀ t, IdentDistrib (ξ t) (ξ 0) P P

namespace SGDSetup

variable (setup : SGDSetup E S Ω)

/-- The common distribution of each `ξ t` (pushforward of `P` through `ξ 0`). -/
noncomputable def sampleDist : Measure S :=
  Measure.map (setup.ξ 0) setup.P

/-- The SGD random process derived from the setup. -/
noncomputable def process : ℕ → Ω → E :=
  sgdProcess setup.w₀ setup.η setup.gradL setup.ξ

omit [SecondCountableTopology E] in
@[simp]
theorem process_zero : setup.process 0 = fun _ => setup.w₀ := rfl

omit [SecondCountableTopology E] in
@[simp]
theorem process_succ (t : ℕ) :
    setup.process (t + 1) = fun ω =>
      setup.process t ω - (setup.η t) • setup.gradL (setup.process t ω) (setup.ξ t ω) :=
  rfl

end SGDSetup

-- ============================================================================
-- Section 4 : Measurability
-- ============================================================================

omit [CompleteSpace E] in
/-- Each `sgdProcess … t` is a measurable function (i.e. a random variable).
Requires `gradL` to be jointly measurable and each `ξ t` to be measurable. -/
theorem sgdProcess_measurable {w₀ : E} {η : ℕ → ℝ}
    {gradL : E → S → E} {ξ : ℕ → Ω → S}
    (hξ : ∀ t, Measurable (ξ t))
    (hg : Measurable (Function.uncurry gradL))
    (t : ℕ) : Measurable (sgdProcess w₀ η gradL ξ t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      simp only [sgdProcess]
      exact ih.sub ((hg.comp (ih.prodMk (hξ t))).const_smul _)

-- ============================================================================
-- Section 5 : Natural Filtration and Adaptedness
-- ============================================================================

/-- The natural filtration for SGD:  `ℱ_t = σ(ξ₀, …, ξ_{t−1})`.

Uses strict inequality so that `ℱ₀` is trivial (w₀ is deterministic)
and `ξ_t` is independent of `ℱ_t`. -/
noncomputable def sgdFiltration
    (ξ : ℕ → Ω → S) (hξ : ∀ t, Measurable (ξ t)) : Filtration ℕ mΩ where
  seq t := ⨆ (j : ℕ) (_ : j < t), MeasurableSpace.comap (ξ j) ‹MeasurableSpace S›
  mono' _ _ hij := iSup₂_mono' fun k hk => ⟨k, lt_of_lt_of_le hk hij, le_rfl⟩
  le' t := iSup₂_le fun j _ => (hξ j).comap_le

omit [CompleteSpace E] in
/-- The SGD process is adapted to its natural filtration. -/
theorem sgdProcess_adapted {w₀ : E} {η : ℕ → ℝ}
    {gradL : E → S → E} {ξ : ℕ → Ω → S}
    (hξ : ∀ t, Measurable (ξ t))
    (hg : Measurable (Function.uncurry gradL)) :
    Adapted (sgdFiltration ξ hξ) (fun t => sgdProcess w₀ η gradL ξ t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    simp only [sgdProcess]
    have h_wt : Measurable[sgdFiltration ξ hξ (t + 1)] (sgdProcess w₀ η gradL ξ t) :=
      ih.mono ((sgdFiltration ξ hξ).mono (Nat.le_succ t)) le_rfl
    have h_ξt : Measurable[sgdFiltration ξ hξ (t + 1)] (ξ t) := by
      rw [measurable_iff_comap_le]
      exact le_iSup₂_of_le t (Nat.lt_succ_self t) le_rfl
    exact h_wt.sub ((hg.comp (h_wt.prodMk h_ξt)).const_smul _)

-- ============================================================================
-- Section 6 : Assumptions on Stochastic Gradient
-- ============================================================================

/-- Unbiasedness: `E_s[∇L(w, s)] = ∇f(w)` for all `w`. -/
def IsUnbiased (gradL : E → S → E) (gradF : E → E) (ν : Measure S) : Prop :=
  ∀ w : E, ∫ s, gradL w s ∂ν = gradF w

/-- Bounded second moment: `E_s[‖∇L(w, s)‖²] ≤ σ²` for all `w`. -/
def HasBoundedVariance (gradL : E → S → E) (ν : Measure S) (σ : ℝ) : Prop :=
  ∀ w : E, ∫ s, ‖gradL w s‖ ^ 2 ∂ν ≤ σ ^ 2

/-- L-smoothness: the true gradient `∇f` is `L`-Lipschitz. -/
def IsLSmooth (gradF : E → E) (L : NNReal) : Prop :=
  LipschitzWith L gradF

/-- Stochastic gradient noise: `e(w, s) = ∇L(w, s) − ∇f(w)`. -/
noncomputable def sgdNoise (gradL : E → S → E) (gradF : E → E) (w : E) (s : S) : E :=
  gradL w s - gradF w

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Under unbiasedness, the noise has zero mean. -/
theorem noise_mean_zero {gradL : E → S → E} {gradF : E → E} {ν : Measure S}
    [IsProbabilityMeasure ν]
    (h_unbiased : IsUnbiased gradL gradF ν)
    (h_int : ∀ w, Integrable (gradL w) ν)
    (w : E) :
    ∫ s, sgdNoise gradL gradF w s ∂ν = 0 := by
  simp only [sgdNoise]
  rw [integral_sub (h_int w) (integrable_const _)]
  simp [h_unbiased w, integral_const]

-- ============================================================================
-- Section 7 : Extended Infrastructure for Convergence Analysis
-- ============================================================================

/-- The stochastic gradient noise has bounded variance:
`E_s[‖∇L(w, s) − ∇f(w)‖²] ≤ σ²` for all `w`.
This is a standard assumption in SGD convergence proofs. -/
def HasBoundedNoiseVariance (gradL : E → S → E) (gradF : E → E)
    (ν : Measure S) (σ : ℝ) : Prop :=
  ∀ w : E, ∫ s, ‖sgdNoise gradL gradF w s‖ ^ 2 ∂ν ≤ σ ^ 2

/-- `gradF` is the gradient of `f` at every point. -/
def IsGradientOf (f : E → ℝ) (gradF : E → E) : Prop :=
  ∀ w : E, HasGradientAt f (gradF w) w

/-- `w*` is a global minimizer of `f`. -/
def IsMinimizer (f : E → ℝ) (wStar : E) : Prop :=
  ∀ w : E, f wStar ≤ f w

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Under unbiasedness, the noise is uncorrelated with every direction `v`:
`E_s[⟪∇L(w, s) − ∇f(w), v⟫] = 0`. -/
theorem noise_inner_product_zero {gradL : E → S → E} {gradF : E → E} {ν : Measure S}
    [IsProbabilityMeasure ν]
    (h_unbiased : IsUnbiased gradL gradF ν)
    (h_int : ∀ w, Integrable (gradL w) ν)
    (w v : E) :
    ∫ s, ⟪sgdNoise gradL gradF w s, v⟫_ℝ ∂ν = 0 := by
  have h_noise_int : Integrable (fun s => sgdNoise gradL gradF w s) ν :=
    (h_int w).sub (integrable_const _)
  -- Swap ⟪noise, v⟫ → ⟪v, noise⟫, then pull v outside the integral
  simp_rw [real_inner_comm v]
  rw [integral_inner h_noise_int v, noise_mean_zero h_unbiased h_int w, inner_zero_right]

-- ============================================================================
-- Section 8 : Non-Convex Convergence (O(1/√T) for ‖∇f‖²)
-- ============================================================================

/-!
## Non-Convex SGD Convergence

**Setting**: f is L-smooth (not necessarily convex).
**Result**: Average squared gradient norm → 0 at rate O(1/√T).

**Key proof steps**:
1. `descent_lemma`: L-smoothness gives a per-step descent bound via Taylor expansion.
2. `stochastic_descent_nonconvex`: Take expectation, use unbiasedness and bounded variance.
3. `sgd_convergence_nonconvex`: Telescope the per-step bounds and rearrange.
-/

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- **L-smoothness descent lemma** (deterministic).
For an L-smooth function, one SGD step satisfies:
`f(w - η·g) ≤ f(w) - η⟪∇f(w), g⟫ + (L/2)·η²·‖g‖²`

Proof: Taylor expansion + Lipschitz bound on ∇f. -/
lemma descent_lemma {f : E → ℝ} {gradF : E → E} {L : NNReal}
    (hgrad : IsGradientOf f gradF)
    (hsmooth : IsLSmooth gradF L)
    (w g : E) (η : ℝ) :
    f (w - η • g) ≤ f w - η * ⟪gradF w, g⟫_ℝ + (L : ℝ) / 2 * η ^ 2 * ‖g‖ ^ 2 := by
  have h := lipschitz_gradient_quadratic_bound hgrad hsmooth.continuous hsmooth w (-(η • g))
  rw [sub_eq_add_neg]
  have h1 : ⟪gradF w, -(η • g)⟫_ℝ = -(η * ⟪gradF w, g⟫_ℝ) := by
    rw [inner_neg_right, inner_smul_right, mul_comm]
  have h2 : ‖-(η • g)‖ ^ 2 = η ^ 2 * ‖g‖ ^ 2 := by
    rw [norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [h1, h2] at h
  linarith

/-- **Expected one-step descent** (stochastic, non-convex setting).
Taking expectation over the stochastic gradient:
`E[f(w_{t+1})] ≤ E[f(w_t)] - η·E[‖∇f(w_t)‖²] + η²·L·σ²/2`

Proof: Apply `descent_lemma`, take expectation, use unbiasedness and bounded variance. -/
lemma stochastic_descent_nonconvex
    (setup : SGDSetup E S Ω) (f : E → ℝ) {t : ℕ} {L : NNReal} {σ η : ℝ}
    (hgrad : IsGradientOf f setup.gradF)
    (hsmooth : IsLSmooth setup.gradF L)
    (hvar : HasBoundedVariance setup.gradL setup.sampleDist σ)
    (hunb : IsUnbiased setup.gradL setup.gradF setup.sampleDist)
    (hη : setup.η t = η) :
    ∫ ω, f (setup.process (t + 1) ω) ∂setup.P ≤
      ∫ ω, f (setup.process t ω) ∂setup.P
      - η * ∫ ω, ‖setup.gradF (setup.process t ω)‖ ^ 2 ∂setup.P
      + η ^ 2 * (L : ℝ) * σ ^ 2 / 2 := by
  set wt := setup.process t
  set gt := fun ω => setup.gradL (wt ω) (setup.ξ t ω)
  -- Step 1: Pointwise descent from descent_lemma
  have h_pw : ∀ ω,
      f (wt ω - η • gt ω) ≤
        f (wt ω) - η * ⟪setup.gradF (wt ω), gt ω⟫_ℝ +
          (L : ℝ) / 2 * η ^ 2 * ‖gt ω‖ ^ 2 := by
    intro ω; exact descent_lemma hgrad hsmooth (wt ω) (gt ω) η
  -- Step 2: The process step matches descent_lemma's form
  have h_step_eq : ∀ ω,
      f (setup.process (t + 1) ω) = f (wt ω - η • gt ω) := by
    intro ω; simp [SGDSetup.process, sgdProcess, hη, wt, gt]
  -- Step 3: Integrate the pointwise bound
  -- f(w_{t+1}) ≤ f(w_t) - η⟪∇f(w_t), g_t⟫ + (L/2)η²‖g_t‖²
  -- ∫ f(w_{t+1}) ≤ ∫ f(w_t) - η ∫ ⟪∇f(w_t), g_t⟫ + (L/2)η² ∫ ‖g_t‖²
  -- Step 4: Use independence + unbiasedness:
  --   ∫ ⟪∇f(w_t), g_t⟫ = ∫ ⟪∇f(w_t), ∇f(w_t)⟫ = ∫ ‖∇f(w_t)‖²
  -- Step 5: Use bounded variance: ∫ ‖g_t‖² ≤ σ²
  -- The deep measure-theory steps (integration, Fubini, independence)
  -- are left as sorry pending IndepExpect infrastructure
  sorry

/-- **Non-Convex SGD Convergence Theorem**.
With constant step size η > 0, after T steps:
`(1/T) · Σ_{t<T} E[‖∇f(w_t)‖²] ≤ 2(f(w₀) - f*) / (η·T) + η·L·σ²`

This implies choosing η ~ 1/√T gives min expected gradient norm O(1/√T).

**Proof structure**:
1. Sum `stochastic_descent_nonconvex` from t = 0 to T−1.
2. Telescope: the sum of (E[f(w_{t+1})] − E[f(w_t)]) equals E[f(w_T)] − f(w₀).
3. Use f(w_T) ≥ f* to bound E[f(w_T)] from below.
4. Rearrange and divide by η·T.
-/
theorem sgd_convergence_nonconvex
    (setup : SGDSetup E S Ω) (f : E → ℝ) {L : NNReal} {σ η f_star : ℝ}
    (hgrad : IsGradientOf f setup.gradF)
    (hsmooth : IsLSmooth setup.gradF L)
    (hvar : HasBoundedVariance setup.gradL setup.sampleDist σ)
    (hunb : IsUnbiased setup.gradL setup.gradF setup.sampleDist)
    (hlower : ∀ w, f_star ≤ f w)
    (hη_pos : 0 < η)
    (hη : ∀ t, setup.η t = η)
    (T : ℕ) (hT : 0 < T) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        ∫ ω, ‖setup.gradF (setup.process t ω)‖ ^ 2 ∂setup.P ≤
      2 * (f setup.w₀ - f_star) / (η * T) + η * (L : ℝ) * σ ^ 2 := by
  -- Step 1: per-step descent bounds from `stochastic_descent_nonconvex`
  have hstep : ∀ t < T,
      ∫ ω, f (setup.process (t + 1) ω) ∂setup.P ≤
        ∫ ω, f (setup.process t ω) ∂setup.P
        - η * ∫ ω, ‖setup.gradF (setup.process t ω)‖ ^ 2 ∂setup.P
        + η ^ 2 * (L : ℝ) * σ ^ 2 / 2 :=
    fun t _ => stochastic_descent_nonconvex setup f hgrad hsmooth hvar hunb (hη t)
  -- Step 2: sum and telescope → η · Σ‖∇f‖² ≤ (f(w₀) − E[f(w_T)]) + T·η²Lσ²/2
  have hsum : η * ∑ t ∈ Finset.range T,
        ∫ ω, ‖setup.gradF (setup.process t ω)‖ ^ 2 ∂setup.P ≤
      f setup.w₀ - ∫ ω, f (setup.process T ω) ∂setup.P +
        (T : ℝ) * (η ^ 2 * (L : ℝ) * σ ^ 2 / 2) := by
    set a := fun t => ∫ ω, f (setup.process t ω) ∂setup.P
    set b := fun t => ∫ ω, ‖setup.gradF (setup.process t ω)‖ ^ 2 ∂setup.P
    have h_rearr : ∀ t, t < T → η * b t ≤ (a t - a (t + 1)) + η ^ 2 * (L : ℝ) * σ ^ 2 / 2 :=
      fun t ht => by simp only [a, b]; linarith [hstep t ht]
    have h_sum_le := Finset.sum_le_sum (fun t ht => h_rearr t (Finset.mem_range.mp ht))
    rw [← Finset.mul_sum] at h_sum_le
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h_sum_le
    have h_tele : ∑ t ∈ Finset.range T, (a t - a (t + 1)) = a 0 - a T := by
      simp_rw [show ∀ t, a t - a (t + 1) = -(a (t + 1) - a t) from fun t => by ring]
      rw [Finset.sum_neg_distrib, Finset.sum_range_sub]; ring
    rw [h_tele] at h_sum_le
    haveI := setup.hP
    have h_init : a 0 = f setup.w₀ := by
      simp [a, SGDSetup.process, sgdProcess, integral_const, probReal_univ]
    rw [h_init] at h_sum_le; linarith
  -- Step 3: E[f(w_T)] ≥ f* (since f ≥ f* pointwise)
  have hlb : f_star ≤ ∫ ω, f (setup.process T ω) ∂setup.P := by
    haveI := setup.hP
    calc f_star = ∫ _, f_star ∂setup.P := by rw [integral_const, smul_eq_mul, probReal_univ, one_mul]
      _ ≤ ∫ ω, f (setup.process T ω) ∂setup.P := by
            apply integral_mono (integrable_const _)
            · sorry -- integrability of f ∘ process T
            · intro ω; exact hlower _
  -- Step 4: algebraic rearrangement and division by η·T
  have hT_pos : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hηT_pos : (0 : ℝ) < η * T := mul_pos hη_pos hT_pos
  have h_comb : η * ∑ t ∈ Finset.range T,
        ∫ ω, ‖setup.gradF (setup.process t ω)‖ ^ 2 ∂setup.P ≤
      (f setup.w₀ - f_star) + ↑T * (η ^ 2 * ↑↑L * σ ^ 2 / 2) := by linarith
  -- Weaken: (f₀−f*) ≤ 2(f₀−f*) and η²Lσ²/2 ≤ η²Lσ²
  have h_weak : η * ∑ t ∈ Finset.range T,
        ∫ ω, ‖setup.gradF (setup.process t ω)‖ ^ 2 ∂setup.P ≤
      2 * (f setup.w₀ - f_star) + ↑T * (η ^ 2 * ↑↑L * σ ^ 2) := by
    have h_fstar : (0 : ℝ) ≤ f setup.w₀ - f_star := by linarith [hlower setup.w₀]
    have h_noise : (0 : ℝ) ≤ ↑T * (η ^ 2 * ↑↑L * σ ^ 2 / 2) := by positivity
    linarith
  -- Divide by η·T and simplify
  have h_div : ∑ t ∈ Finset.range T,
        ∫ ω, ‖setup.gradF (setup.process t ω)‖ ^ 2 ∂setup.P ≤
      (2 * (f setup.w₀ - f_star) + ↑T * (η ^ 2 * ↑↑L * σ ^ 2)) / η := by
    rw [le_div_iff₀ hη_pos]; linarith
  calc (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
          ∫ ω, ‖setup.gradF (setup.process t ω)‖ ^ 2 ∂setup.P
      ≤ (1 / ↑T) * ((2 * (f setup.w₀ - f_star) + ↑T * (η ^ 2 * ↑↑L * σ ^ 2)) / η) :=
        mul_le_mul_of_nonneg_left h_div (by positivity : (0 : ℝ) ≤ 1 / ↑T)
    _ = 2 * (f setup.w₀ - f_star) / (η * ↑T) + η * ↑↑L * σ ^ 2 := by
        field_simp

-- ============================================================================
-- Section 9 : Convex Convergence (O(1/√T) for f − f*)
-- ============================================================================

/-!
## Convex SGD Convergence

**Setting**: f is L-smooth and convex; w* is a global minimizer.
**Result**: Average function gap → 0 at rate O(1/√T).

**Key proof steps**:
1. `one_step_progress_convex`: Per-step bound using convexity and L-smoothness.
2. `sgd_convergence_convex`: Telescope and average.
-/

/-- **One-step progress under convexity**.
`E[‖w_{t+1} − w*‖²] ≤ E[‖w_t − w*‖²] - 2η(E[f(w_t)] - f*) + η²σ²`

Proof: Expand the squared distance, use unbiasedness and bounded variance. -/
lemma one_step_progress_convex
    (setup : SGDSetup E S Ω) (f : E → ℝ) {t : ℕ} {L : NNReal} {σ η : ℝ} (wStar : E)
    (hgrad : IsGradientOf f setup.gradF)
    (hsmooth : IsLSmooth setup.gradF L)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hvar : HasBoundedVariance setup.gradL setup.sampleDist σ)
    (hunb : IsUnbiased setup.gradL setup.gradF setup.sampleDist)
    (hmin : IsMinimizer f wStar)
    (hη : setup.η t = η) :
    ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P ≤
      ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P
      - 2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)
      + η ^ 2 * σ ^ 2 := by
  -- Step 1: Pointwise norm expansion
  -- ‖w_{t+1} - w*‖² = ‖(w_t - η·g_t) - w*‖²
  --   = ‖w_t - w*‖² - 2η⟪w_t - w*, g_t⟫ + η²‖g_t‖²
  have h_expand : ∀ ω,
      ‖setup.process (t + 1) ω - wStar‖ ^ 2 =
        ‖setup.process t ω - wStar‖ ^ 2
        - 2 * η * ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ
        + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := by
    intro ω
    have h_step : setup.process (t + 1) ω =
        setup.process t ω - η • setup.gradL (setup.process t ω) (setup.ξ t ω) := by
      simp [SGDSetup.process_succ, hη]
    rw [h_step]
    set w := setup.process t ω
    set g := setup.gradL w (setup.ξ t ω)
    show ‖w - η • g - wStar‖ ^ 2 = ‖w - wStar‖ ^ 2 - 2 * η * ⟪w - wStar, g⟫_ℝ + η ^ 2 * ‖g‖ ^ 2
    have : w - η • g - wStar = (w - wStar) - η • g := by abel
    rw [this, norm_sub_sq_real]
    simp [inner_smul_right, norm_smul, mul_pow, sq_abs]; ring
  -- Step 2: Integrate the expansion
  -- Step 3: Unbiased cross-term: ∫ ⟪wₜ-w*, g_t⟫ = ∫ ⟪wₜ-w*, ∇f(wₜ)⟫
  -- Step 4: Convex FOC: ⟪∇f(w), w - w*⟫ ≥ f(w) - f(w*)
  -- Step 5: Bounded variance: ∫ ‖g_t‖² ≤ σ²
  sorry

/-- **Convex SGD Convergence Theorem**.
With constant step size η > 0, after T steps:
`(1/T) · Σ_{t<T} E[f(w_t) − f*] ≤ ‖w₀ − w*‖² / (2ηT) + η·σ²/2`

Choosing η ~ ‖w₀ − w*‖ / (σ√T) gives gap O(‖w₀ − w*‖·σ/√T).

**Proof structure**:
1. Sum `one_step_progress_convex` from t = 0 to T−1.
2. Telescope: Σ(‖w_{t+1} − w*‖² − ‖w_t − w*‖²) = ‖w_T − w*‖² − ‖w₀ − w*‖².
3. Drop the (non-negative) ‖w_T − w*‖² term.
4. Rearrange and divide by 2ηT.
-/
theorem sgd_convergence_convex
    (setup : SGDSetup E S Ω) (f : E → ℝ) {L : NNReal} {σ η : ℝ} (wStar : E)
    (hgrad : IsGradientOf f setup.gradF)
    (hsmooth : IsLSmooth setup.gradF L)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hvar : HasBoundedVariance setup.gradL setup.sampleDist σ)
    (hunb : IsUnbiased setup.gradL setup.gradF setup.sampleDist)
    (hmin : IsMinimizer f wStar)
    (hη_pos : 0 < η)
    (hη : ∀ t, setup.η t = η)
    (T : ℕ) (hT : 0 < T) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
      ‖setup.w₀ - wStar‖ ^ 2 / (2 * η * T) + η * σ ^ 2 / 2 := by
  -- Step 1: per-step progress from `one_step_progress_convex`
  have hstep : ∀ t < T,
      ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P ≤
        ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P
        - 2 * η * (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)
        + η ^ 2 * σ ^ 2 :=
    fun t _ => one_step_progress_convex setup f wStar hgrad hsmooth hconvex hvar hunb hmin (hη t)
  -- Step 2: sum and telescope → 2η · Σ(gap) ≤ ‖w₀−w*‖² − ‖w_T−w*‖² + T·η²σ²
  have hsum : 2 * η * ∑ t ∈ Finset.range T,
        (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
      ‖setup.w₀ - wStar‖ ^ 2 -
        ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P +
        (T : ℝ) * (η ^ 2 * σ ^ 2) := by
    set a := fun t => ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P
    set gap := fun t => ∫ ω, f (setup.process t ω) ∂setup.P - f wStar
    have h_rearr : ∀ t, t < T →
        2 * η * gap t ≤ (a t - a (t + 1)) + η ^ 2 * σ ^ 2 :=
      fun t ht => by simp only [a, gap]; linarith [hstep t ht]
    have h_sum_le := Finset.sum_le_sum (fun t ht => h_rearr t (Finset.mem_range.mp ht))
    rw [← Finset.mul_sum] at h_sum_le
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h_sum_le
    have h_tele : ∑ t ∈ Finset.range T, (a t - a (t + 1)) = a 0 - a T := by
      simp_rw [show ∀ t, a t - a (t + 1) = -(a (t + 1) - a t) from fun t => by ring]
      rw [Finset.sum_neg_distrib, Finset.sum_range_sub]; ring
    rw [h_tele] at h_sum_le
    haveI := setup.hP
    have h_init : a 0 = ‖setup.w₀ - wStar‖ ^ 2 := by
      simp [a, SGDSetup.process, sgdProcess, integral_const, probReal_univ]
    rw [h_init] at h_sum_le; linarith
  -- Step 3: drop non-negative ‖w_T − w*‖² term and divide by 2ηT
  have h_norm_nonneg : 0 ≤ ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P := by
    apply integral_nonneg; intro ω; positivity
  have h_drop : 2 * η * ∑ t ∈ Finset.range T,
        (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
      ‖setup.w₀ - wStar‖ ^ 2 + (T : ℝ) * (η ^ 2 * σ ^ 2) := by linarith
  have hη_ne : η ≠ 0 := ne_of_gt hη_pos
  have hT_pos : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT_pos
  have hη2_pos : (0 : ℝ) < 2 * η := by linarith
  rw [one_div, inv_mul_le_iff₀ hT_pos]
  have h_rhs : ↑T * (‖setup.w₀ - wStar‖ ^ 2 / (2 * η * ↑T) + η * σ ^ 2 / 2) =
      (‖setup.w₀ - wStar‖ ^ 2 + ↑T * (η ^ 2 * σ ^ 2)) / (2 * η) := by
    field_simp
  rw [h_rhs, le_div_iff₀ hη2_pos]; linarith

-- ============================================================================
-- Section 10 : Strongly Convex Convergence (linear rate)
-- ============================================================================

/-!
## Strongly Convex SGD Convergence

**Setting**: f is L-smooth and μ-strongly convex; w* is the unique minimizer.
**Result**: E[‖w_t − w*‖²] → 0 linearly when η < 2/(L + μ).

With diminishing step sizes η_t = c/t, convergence is O(1/T).

**Key proof steps**:
1. `one_step_progress_sc`: Per-step contraction using strong convexity.
2. `sgd_convergence_strongly_convex`: Unroll the recurrence.
-/

/-- **One-step contraction under strong convexity**.
With step size η_t satisfying η_t ≤ 1/L:
`E[‖w_{t+1} − w*‖²] ≤ (1 − η_t·μ) · E[‖w_t − w*‖²] + η_t²·σ²`

Proof: Strong convexity gives a lower bound on the inner product term;
combined with unbiasedness, this dominates the cross terms. -/
lemma one_step_progress_sc
    (setup : SGDSetup E S Ω) (f : E → ℝ) {t : ℕ} {L : NNReal} {μ σ η : ℝ} (wStar : E)
    (hgrad : IsGradientOf f setup.gradF)
    (hsmooth : IsLSmooth setup.gradF L)
    (hsc : StrongConvexOn Set.univ μ f)
    (hvar : HasBoundedVariance setup.gradL setup.sampleDist σ)
    (hunb : IsUnbiased setup.gradL setup.gradF setup.sampleDist)
    (hmin : IsMinimizer f wStar)
    (hμ_pos : 0 < μ) (hη_pos : 0 < η) (hη_L : η ≤ 1 / (L : ℝ))
    (hη : setup.η t = η) :
    ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P ≤
      (1 - η * μ) * ∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P
      + η ^ 2 * σ ^ 2 := by
  -- Step 1: Pointwise norm expansion (same as convex case)
  have h_expand : ∀ ω,
      ‖setup.process (t + 1) ω - wStar‖ ^ 2 =
        ‖setup.process t ω - wStar‖ ^ 2
        - 2 * η * ⟪setup.process t ω - wStar, setup.gradL (setup.process t ω) (setup.ξ t ω)⟫_ℝ
        + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := by
    intro ω
    have h_step : setup.process (t + 1) ω =
        setup.process t ω - η • setup.gradL (setup.process t ω) (setup.ξ t ω) := by
      simp [SGDSetup.process_succ, hη]
    rw [h_step]
    set w := setup.process t ω
    set g := setup.gradL w (setup.ξ t ω)
    show ‖w - η • g - wStar‖ ^ 2 = ‖w - wStar‖ ^ 2 - 2 * η * ⟪w - wStar, g⟫_ℝ + η ^ 2 * ‖g‖ ^ 2
    have : w - η • g - wStar = (w - wStar) - η • g := by abel
    rw [this, norm_sub_sq_real]
    simp [inner_smul_right, norm_smul, mul_pow, sq_abs]; ring
  -- Step 2: Integrate the expansion
  -- Step 3: Unbiased cross-term: ∫ ⟪wₜ-w*, g_t⟫ = ∫ ⟪wₜ-w*, ∇f(wₜ)⟫
  -- Step 4: Strong convex FOC: ⟪∇f(w), w-w*⟫ ≥ μ/2 ‖w-w*‖²
  -- Step 5: Bounded variance: ∫ ‖g_t‖² ≤ σ²
  -- Combine: E[‖w_{t+1}-w*‖²] ≤ (1-ημ) E[‖wₜ-w*‖²] + η²σ²
  sorry

/-- **Strongly Convex SGD Convergence Theorem**.
With constant step size η ≤ 1/L satisfying 0 < η·μ < 1, after T steps:
`E[‖w_T − w*‖²] ≤ (1 − η·μ)^T · ‖w₀ − w*‖² + η·σ²/μ`

The first term decays geometrically; choosing η = 1/L gives
contraction factor (1 − μ/L) = (κ−1)/κ where κ = L/μ is the condition number.

**Proof structure**:
1. Unroll the recurrence from `one_step_progress_sc` T times.
2. The geometric series Σ_{k<T} (1 − ημ)^k ≤ 1/(ημ) bounds the noise accumulation.
-/
theorem sgd_convergence_strongly_convex
    (setup : SGDSetup E S Ω) (f : E → ℝ) {L : NNReal} {μ σ η : ℝ} (wStar : E)
    (hgrad : IsGradientOf f setup.gradF)
    (hsmooth : IsLSmooth setup.gradF L)
    (hsc : StrongConvexOn Set.univ μ f)
    (hvar : HasBoundedVariance setup.gradL setup.sampleDist σ)
    (hunb : IsUnbiased setup.gradL setup.gradF setup.sampleDist)
    (hmin : IsMinimizer f wStar)
    (hμ_pos : 0 < μ) (hη_pos : 0 < η) (hη_L : η ≤ 1 / (L : ℝ))
    (hημ : η * μ < 1)
    (hη : ∀ t, setup.η t = η)
    (T : ℕ) :
    ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P ≤
      (1 - η * μ) ^ T * ‖setup.w₀ - wStar‖ ^ 2 + η * σ ^ 2 / μ := by
  -- Proof by induction on T, unrolling `one_step_progress_sc` at each step.
  have h_nonneg : 0 ≤ 1 - η * μ := by linarith
  induction T with
  | zero =>
    -- Base case: process 0 = w₀ (deterministic), integral of constant = constant
    simp only [SGDSetup.process, sgdProcess, pow_zero, one_mul]
    haveI := setup.hP
    rw [integral_const, smul_eq_mul, probReal_univ, one_mul]
    linarith [div_nonneg (mul_nonneg (le_of_lt hη_pos) (sq_nonneg σ)) (le_of_lt hμ_pos)]
  | succ T ih =>
    -- Apply one_step_progress_sc at step T
    have hstep := one_step_progress_sc setup f wStar hgrad hsmooth hsc hvar hunb hmin
                    hμ_pos hη_pos hη_L (hη T)
    -- The noise accumulation reduces exactly: (1-ημ)·(ησ²/μ) + η²σ² = ησ²/μ
    have hkey : (1 - η * μ) * ((1 - η * μ) ^ T * ‖setup.w₀ - wStar‖ ^ 2 + η * σ ^ 2 / μ) +
        η ^ 2 * σ ^ 2 = (1 - η * μ) ^ (T + 1) * ‖setup.w₀ - wStar‖ ^ 2 + η * σ ^ 2 / μ := by
      have hne : μ ≠ 0 := ne_of_gt hμ_pos
      field_simp; ring
    calc ∫ ω, ‖setup.process (T + 1) ω - wStar‖ ^ 2 ∂setup.P
        ≤ (1 - η * μ) * ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P
            + η ^ 2 * σ ^ 2 := hstep
      _ ≤ (1 - η * μ) * ((1 - η * μ) ^ T * ‖setup.w₀ - wStar‖ ^ 2 + η * σ ^ 2 / μ)
            + η ^ 2 * σ ^ 2 := by gcongr
      _ = (1 - η * μ) ^ (T + 1) * ‖setup.w₀ - wStar‖ ^ 2 + η * σ ^ 2 / μ := hkey
