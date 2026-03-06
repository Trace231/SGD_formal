import Lib.Layer0.GradientFTC
import Lib.Layer0.IndepExpect
import Lib.Layer0.ConvexFOC
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Data.NNReal.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Strong

/-!
# One-Step Stochastic Descent Meta-Theorems (Layer 1)

Layer: 1 (stochastic optimization abstractions; no specific algorithm)

This file defines the `StochasticDescentHyps` structure and proves three
one-step meta-theorems covering the non-convex, convex, and strongly convex
settings. All three share the same 5-step proof structure:
  Step 1. Pointwise bound (deterministic)
  Step 2. Integrate the bound (integral_mono)
  Step 3. Linearize the expectation (integral_add/sub/const_mul)
  Step 4. Unbiasedness (expectation_inner_gradL_eq)
  Step 5. Variance bound (expectation_norm_sq_gradL_bound)

## Design philosophy

`StochasticDescentHyps` encapsulates exactly the probabilistic and measurability
conditions needed for a single stochastic gradient step, with no reference to
any algorithm's iteration structure (no `sgdProcess`, no step index `t`).
This makes the meta-theorems reusable for SGD, SVRG, Adam, etc. — any algorithm
whose update has the form `wₜ₊₁ = wₜ − η · gradL(wₜ, ξₜ)`.

## Main results

* `StochasticDescentHyps` — one-step stochastic setup structure
* `descent_lemma'` — deterministic L-smooth per-step bound
* `stochastic_descent_nonconvex'` — expected one-step descent (non-convex)
* `stochastic_descent_convex'` — one-step distance progress (convex)
* `stochastic_descent_strongly_convex'` — one-step contraction (strongly convex)

## Gap analysis

* `descent_lemma'`: Layer 0 by nature; Gap Level 2+3 composite.
* All three meta-theorems: Layer 1; Gap Level 2 — compose Layer 0 lemmas
  (IndepExpect + ConvexFOC) with integral linearity facts.
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {S : Type*} [MeasurableSpace S]
variable {Ω : Type*} [MeasurableSpace Ω]

-- ============================================================================
-- Predicate definitions (algorithm-independent)
-- These will be consolidated into Lib/Layer0/ in a future refactor.
-- ============================================================================

/-- Unbiasedness: `E_ν[gradL(w, ·)] = gradF(w)` for all `w`. -/
def IsUnbiased' (gradL : E → S → E) (gradF : E → E) (ν : Measure S) : Prop :=
  ∀ w : E, ∫ s, gradL w s ∂ν = gradF w

/-- Bounded second moment: `E_ν[‖gradL(w, ·)‖²] ≤ σ²` for all `w`. -/
def HasBoundedVariance' (gradL : E → S → E) (ν : Measure S) (σ : ℝ) : Prop :=
  ∀ w : E, ∫ s, ‖gradL w s‖ ^ 2 ∂ν ≤ σ ^ 2

/-- L-smoothness: the true gradient `gradF` is `L`-Lipschitz. -/
def IsLSmooth' (gradF : E → E) (L : NNReal) : Prop :=
  LipschitzWith L gradF

/-- `gradF` is the gradient of `f` at every point. -/
def IsGradientOf' (f : E → ℝ) (gradF : E → E) : Prop :=
  ∀ w : E, HasGradientAt f (gradF w) w

/-- `wStar` is a global minimizer of `f`. -/
def IsMinimizer' (f : E → ℝ) (wStar : E) : Prop :=
  ∀ w : E, f wStar ≤ f w

-- ============================================================================
-- StochasticDescentHyps structure
-- ============================================================================

/-- Minimal one-step probabilistic setup for stochastic gradient descent.

Captures the independence structure, distribution, and oracle properties
for a single step, without reference to any specific algorithm or step index.
This abstraction allows meta-theorems to be stated and proved once and then
instantiated for any algorithm whose update has the form
  `wₜ₊₁ = wₜ − η · gradL(wₜ, ξₜ)`.

Fields:
* `P`, `hP`    : probability space on `Ω`
* `ν`          : sample distribution (= `Measure.map ξ₀ P` for SGD's `sampleDist`)
* `wt`         : current iterate as a random variable `Ω → E`
* `ξt`         : current sample `Ω → S`
* `gradL`      : stochastic gradient oracle
* `gradF`      : true gradient (deterministic)
* `η`          : step size for this one step
* `h_indep`    : independence `wt ⊥ ξt` (for SGD: from `sgdProcess_indepFun_xi`)
* `h_dist`     : pushforward distribution `map(ξt)P = ν`
* `h_wt_meas`  : measurability of `wt`
* `h_ξt_meas`  : measurability of `ξt`
* `hgL`        : joint measurability of `gradL`
* `hgF_meas`   : measurability of `gradF` (needed for unbiasedness step)
* `hunb`       : oracle unbiasedness `E_ν[gradL(w,·)] = gradF(w)` -/
structure StochasticDescentHyps
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (S : Type*) [MeasurableSpace S]
    (Ω : Type*) [MeasurableSpace Ω] where
  P         : Measure Ω
  hP        : IsProbabilityMeasure P
  ν         : Measure S
  wt        : Ω → E
  ξt        : Ω → S
  gradL     : E → S → E
  gradF     : E → E
  η         : ℝ
  h_indep   : IndepFun wt ξt P
  h_dist    : Measure.map ξt P = ν
  h_wt_meas : Measurable wt
  h_ξt_meas : Measurable ξt
  hgL       : Measurable (Function.uncurry gradL)
  hgF_meas  : Measurable gradF
  hunb      : IsUnbiased' gradL gradF ν

-- ============================================================================
-- Deterministic stepping stone: L-smooth descent lemma
-- ============================================================================

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- L-smoothness descent lemma (deterministic).

Layer: 0 (by nature) | Gap: Level 2+3 composite
Technique: apply `lipschitz_gradient_quadratic_bound` then algebraic rewriting
  — `inner_neg_right`, `inner_smul_right`, `norm_neg`, `norm_smul`.
Proof steps:
  [dep: lipschitz_gradient_quadratic_bound at direction -(η•g)]
  [L3: inner_neg_right + inner_smul_right to match sign/scalar form]
  [L3: norm_neg + norm_smul + sq_abs to match norm-squared form]
  [L0: linarith]
Used in: `stochastic_descent_nonconvex` (Step 1 — pointwise bound)

For an L-smooth function and any direction `g`, one gradient step satisfies:
`f(w − η·g) ≤ f(w) − η·⟪∇f(w), g⟫ + (L/2)·η²·‖g‖²` -/
lemma descent_lemma' {f : E → ℝ} {gradF : E → E} {L : NNReal}
    (hgrad : IsGradientOf' f gradF)
    (hsmooth : IsLSmooth' gradF L)
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

-- ============================================================================
-- Meta-theorem 1: Non-convex setting
-- ============================================================================

/-- Expected one-step descent for L-smooth functions (non-convex setting).

Layer: 1 | Gap: Level 2 (composition of Layer 0 infrastructure)
Technique: (1) pointwise descent via `descent_lemma'`; (2) integrate and linearize;
  (3) replace ∫⟪∇f(wt), gt⟫ with ∫‖∇f(wt)‖² via unbiasedness;
  (4) bound ∫‖gt‖² ≤ σ² via variance bound.
Proof steps:
  [dep: descent_lemma' pointwise at each ω]
  [L0: integral_mono to integrate the pointwise bound]
  [L0: integral_add + integral_sub + integral_const_mul (linearity)]
  [dep: expectation_inner_gradL_eq with h = gradF]
  [dep: expectation_norm_sq_gradL_bound]
  [L0: linarith to combine]
Used in: Algorithms/SGD.lean `sgd_convergence_nonconvex_v2`

`E[f(wt − η·gradL(wt, ξt))] ≤ E[f(wt)] − η·E[‖∇f(wt)‖²] + η²·L·σ²/2` -/
theorem stochastic_descent_nonconvex'
    (hyps : StochasticDescentHyps E S Ω) (f : E → ℝ) {L : NNReal} {σ : ℝ}
    (hgrad : IsGradientOf' f hyps.gradF)
    (hsmooth : IsLSmooth' hyps.gradF L)
    (hvar : HasBoundedVariance' hyps.gradL hyps.ν σ)
    (h_intL : ∀ w, Integrable (hyps.gradL w) hyps.ν)
    (h_int_ft  : Integrable (fun ω => f (hyps.wt ω)) hyps.P)
    (h_int_ft1 : Integrable
        (fun ω => f (hyps.wt ω - hyps.η • hyps.gradL (hyps.wt ω) (hyps.ξt ω))) hyps.P)
    (h_int_inner : Integrable
        (fun ω => ⟪hyps.gradF (hyps.wt ω), hyps.gradL (hyps.wt ω) (hyps.ξt ω)⟫_ℝ) hyps.P)
    (h_int_sq : Integrable
        (fun ω => ‖hyps.gradL (hyps.wt ω) (hyps.ξt ω)‖ ^ 2) hyps.P) :
    ∫ ω, f (hyps.wt ω - hyps.η • hyps.gradL (hyps.wt ω) (hyps.ξt ω)) ∂hyps.P ≤
      ∫ ω, f (hyps.wt ω) ∂hyps.P
      - hyps.η * ∫ ω, ‖hyps.gradF (hyps.wt ω)‖ ^ 2 ∂hyps.P
      + hyps.η ^ 2 * (L : ℝ) * σ ^ 2 / 2 := by
  haveI := hyps.hP
  set wt := hyps.wt with hwt_def
  set gt := fun ω => hyps.gradL (wt ω) (hyps.ξt ω) with hgt_def
  -- Step 1: Pointwise descent
  have h_pw : ∀ ω,
      f (wt ω - hyps.η • gt ω) ≤
        f (wt ω) - hyps.η * ⟪hyps.gradF (wt ω), gt ω⟫_ℝ +
          (L : ℝ) / 2 * hyps.η ^ 2 * ‖gt ω‖ ^ 2 :=
    fun ω => descent_lemma' hgrad hsmooth (wt ω) (gt ω) hyps.η
  -- Integrability of the RHS pointwise bound
  have h_int_rhs : Integrable (fun ω =>
      f (wt ω) - hyps.η * ⟪hyps.gradF (wt ω), gt ω⟫_ℝ +
        (L : ℝ) / 2 * hyps.η ^ 2 * ‖gt ω‖ ^ 2) hyps.P :=
    (h_int_ft.sub (h_int_inner.const_mul hyps.η)).add
      (h_int_sq.const_mul ((L : ℝ) / 2 * hyps.η ^ 2))
  -- Step 2: Integrate the pointwise bound
  have h_int3 : ∫ ω, f (wt ω - hyps.η • gt ω) ∂hyps.P ≤
      ∫ ω, (f (wt ω) - hyps.η * ⟪hyps.gradF (wt ω), gt ω⟫_ℝ +
        (L : ℝ) / 2 * hyps.η ^ 2 * ‖gt ω‖ ^ 2) ∂hyps.P :=
    integral_mono h_int_ft1 h_int_rhs h_pw
  -- Step 3: Linearity of integral
  have h_rhs_lin :
      ∫ ω, (f (wt ω) - hyps.η * ⟪hyps.gradF (wt ω), gt ω⟫_ℝ +
        (L : ℝ) / 2 * hyps.η ^ 2 * ‖gt ω‖ ^ 2) ∂hyps.P =
      ∫ ω, f (wt ω) ∂hyps.P
      - hyps.η * ∫ ω, ⟪hyps.gradF (wt ω), gt ω⟫_ℝ ∂hyps.P
      + (L : ℝ) / 2 * hyps.η ^ 2 * ∫ ω, ‖gt ω‖ ^ 2 ∂hyps.P := by
    have h1 : ∫ ω, (f (wt ω) - hyps.η * ⟪hyps.gradF (wt ω), gt ω⟫_ℝ +
        (L : ℝ) / 2 * hyps.η ^ 2 * ‖gt ω‖ ^ 2) ∂hyps.P =
        ∫ ω, (f (wt ω) - hyps.η * ⟪hyps.gradF (wt ω), gt ω⟫_ℝ) ∂hyps.P +
        ∫ ω, ((L : ℝ) / 2 * hyps.η ^ 2 * ‖gt ω‖ ^ 2) ∂hyps.P :=
      integral_add (h_int_ft.sub (h_int_inner.const_mul hyps.η)) (h_int_sq.const_mul _)
    have h2 : ∫ ω, (f (wt ω) - hyps.η * ⟪hyps.gradF (wt ω), gt ω⟫_ℝ) ∂hyps.P =
        ∫ ω, f (wt ω) ∂hyps.P - ∫ ω, (hyps.η * ⟪hyps.gradF (wt ω), gt ω⟫_ℝ) ∂hyps.P :=
      integral_sub h_int_ft (h_int_inner.const_mul hyps.η)
    have h3 : ∫ ω, (hyps.η * ⟪hyps.gradF (wt ω), gt ω⟫_ℝ) ∂hyps.P =
        hyps.η * ∫ ω, ⟪hyps.gradF (wt ω), gt ω⟫_ℝ ∂hyps.P :=
      integral_const_mul hyps.η _
    have h4 : ∫ ω, ((L : ℝ) / 2 * hyps.η ^ 2 * ‖gt ω‖ ^ 2) ∂hyps.P =
        (L : ℝ) / 2 * hyps.η ^ 2 * ∫ ω, ‖gt ω‖ ^ 2 ∂hyps.P :=
      integral_const_mul _ _
    linarith
  -- Step 4: Unbiasedness — ∫⟪∇f(wt), gt⟫ = ∫‖∇f(wt)‖²
  have h_unb : ∫ ω, ⟪hyps.gradF (wt ω), gt ω⟫_ℝ ∂hyps.P =
      ∫ ω, ‖hyps.gradF (wt ω)‖ ^ 2 ∂hyps.P := by
    rw [show ∫ ω, ‖hyps.gradF (wt ω)‖ ^ 2 ∂hyps.P =
        ∫ ω, ⟪hyps.gradF (wt ω), hyps.gradF (wt ω)⟫_ℝ ∂hyps.P from by
          congr 1; ext ω; exact (real_inner_self_eq_norm_sq _).symm]
    exact expectation_inner_gradL_eq
      hyps.hunb hyps.h_indep hyps.h_dist (fun w => hyps.gradF w)
      hyps.h_wt_meas hyps.h_ξt_meas
      hyps.hgL hyps.hgF_meas hyps.hgF_meas h_intL h_int_inner
  -- Step 5: Bounded variance — ∫‖gt‖² ≤ σ²
  have h_var : ∫ ω, ‖gt ω‖ ^ 2 ∂hyps.P ≤ σ ^ 2 :=
    expectation_norm_sq_gradL_bound
      hvar hyps.h_indep hyps.h_dist
      hyps.h_wt_meas hyps.h_ξt_meas hyps.hgL h_int_sq
  -- Combine all steps
  calc ∫ ω, f (hyps.wt ω - hyps.η • hyps.gradL (hyps.wt ω) (hyps.ξt ω)) ∂hyps.P
      ≤ ∫ ω, f (wt ω) ∂hyps.P
        - hyps.η * ∫ ω, ⟪hyps.gradF (wt ω), gt ω⟫_ℝ ∂hyps.P
        + (L : ℝ) / 2 * hyps.η ^ 2 * ∫ ω, ‖gt ω‖ ^ 2 ∂hyps.P :=
          h_int3.trans_eq h_rhs_lin
    _ = ∫ ω, f (wt ω) ∂hyps.P
        - hyps.η * ∫ ω, ‖hyps.gradF (wt ω)‖ ^ 2 ∂hyps.P
        + (L : ℝ) / 2 * hyps.η ^ 2 * ∫ ω, ‖gt ω‖ ^ 2 ∂hyps.P := by rw [h_unb]
    _ ≤ ∫ ω, f (wt ω) ∂hyps.P
        - hyps.η * ∫ ω, ‖hyps.gradF (wt ω)‖ ^ 2 ∂hyps.P
        + hyps.η ^ 2 * (L : ℝ) * σ ^ 2 / 2 := by
          have h_var_mul := mul_le_mul_of_nonneg_left h_var
            (show (0 : ℝ) ≤ (L : ℝ) / 2 * hyps.η ^ 2 by positivity)
          linarith

-- ============================================================================
-- Meta-theorem 2: Convex setting
-- ============================================================================

/-- One-step distance progress under convexity.

Layer: 1 | Gap: Level 2 (composition of Layer 0 infrastructure)
Technique: expand ‖wₜ₊₁ − w*‖², integrate, then apply:
  (3) unbiasedness to replace gt with gradF(wt);
  (4) convex FOC (`convex_inner_lower_bound`) to lower-bound
      ∫⟪wt−w*, ∇f(wt)⟫ by E[f(wt)] − f(w*);
  (5) variance bound.
Proof steps:
  [L0: norm_sub_sq_real + inner_smul_right expansion pointwise]
  [L0: integral_congr_ae + integral_add/sub/const_mul (linearity)]
  [dep: expectation_inner_gradL_eq with h = (· − w*)]
  [dep: convex_inner_lower_bound + integral_mono]
  [dep: expectation_norm_sq_gradL_bound]
  [L0: nlinarith to combine]
Note: no L-smoothness needed — convexity alone suffices for the distance bound.
Used in: Algorithms/SGD.lean `one_step_progress_convex`

`E[‖wₜ₊₁ − w*‖²] ≤ E[‖wₜ − w*‖²] − 2η(E[f(wₜ)] − f(w*)) + η²σ²` -/
theorem stochastic_descent_convex'
    (hyps : StochasticDescentHyps E S Ω) (f : E → ℝ) {σ : ℝ} (wStar : E)
    (hgrad : IsGradientOf' f hyps.gradF)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hvar : HasBoundedVariance' hyps.gradL hyps.ν σ)
    (hη_pos : 0 < hyps.η)
    (h_intL : ∀ w, Integrable (hyps.gradL w) hyps.ν)
    (h_int_inner : Integrable (fun ω =>
        ⟪hyps.wt ω - wStar, hyps.gradL (hyps.wt ω) (hyps.ξt ω)⟫_ℝ) hyps.P)
    (h_int_sq : Integrable (fun ω =>
        ‖hyps.gradL (hyps.wt ω) (hyps.ξt ω)‖ ^ 2) hyps.P)
    (h_int_norm_sq : Integrable (fun ω => ‖hyps.wt ω - wStar‖ ^ 2) hyps.P)
    (h_int_ft : Integrable (fun ω => f (hyps.wt ω)) hyps.P)
    (h_int_gF_inner : Integrable (fun ω =>
        ⟪hyps.wt ω - wStar, hyps.gradF (hyps.wt ω)⟫_ℝ) hyps.P) :
    ∫ ω, ‖(hyps.wt ω - hyps.η • hyps.gradL (hyps.wt ω) (hyps.ξt ω)) - wStar‖ ^ 2 ∂hyps.P ≤
      ∫ ω, ‖hyps.wt ω - wStar‖ ^ 2 ∂hyps.P
      - 2 * hyps.η * (∫ ω, f (hyps.wt ω) ∂hyps.P - f wStar)
      + hyps.η ^ 2 * σ ^ 2 := by
  haveI := hyps.hP
  set wt := hyps.wt with hwt_def
  set gt := fun ω => hyps.gradL (wt ω) (hyps.ξt ω) with hgt_def
  -- Step 1: Pointwise norm expansion
  have h_expand : ∀ ω,
      ‖wt ω - hyps.η • gt ω - wStar‖ ^ 2 =
        ‖wt ω - wStar‖ ^ 2
        - 2 * hyps.η * ⟪wt ω - wStar, gt ω⟫_ℝ
        + hyps.η ^ 2 * ‖gt ω‖ ^ 2 := by
    intro ω
    have : wt ω - hyps.η • gt ω - wStar = (wt ω - wStar) - hyps.η • gt ω := by abel
    rw [this, norm_sub_sq_real]
    simp [inner_smul_right, norm_smul, mul_pow, sq_abs]; ring
  -- Integrability of the expanded form
  have h_int_exp : Integrable (fun ω =>
      ‖wt ω - wStar‖ ^ 2 - 2 * hyps.η * ⟪wt ω - wStar, gt ω⟫_ℝ
      + hyps.η ^ 2 * ‖gt ω‖ ^ 2) hyps.P :=
    (h_int_norm_sq.sub (h_int_inner.const_mul (2 * hyps.η))).add
      (h_int_sq.const_mul (hyps.η ^ 2))
  -- Step 2: Integrate the expansion
  have h_int_eq :
      ∫ ω, ‖wt ω - hyps.η • gt ω - wStar‖ ^ 2 ∂hyps.P =
        ∫ ω, ‖wt ω - wStar‖ ^ 2 ∂hyps.P
        - 2 * hyps.η * ∫ ω, ⟪wt ω - wStar, gt ω⟫_ℝ ∂hyps.P
        + hyps.η ^ 2 * ∫ ω, ‖gt ω‖ ^ 2 ∂hyps.P := by
    have hkey : ∫ ω, ‖wt ω - hyps.η • gt ω - wStar‖ ^ 2 ∂hyps.P =
        ∫ ω, (‖wt ω - wStar‖ ^ 2 - 2 * hyps.η * ⟪wt ω - wStar, gt ω⟫_ℝ
          + hyps.η ^ 2 * ‖gt ω‖ ^ 2) ∂hyps.P :=
      integral_congr_ae (Filter.Eventually.of_forall h_expand)
    have h1 : ∫ ω, (‖wt ω - wStar‖ ^ 2 - 2 * hyps.η * ⟪wt ω - wStar, gt ω⟫_ℝ +
        hyps.η ^ 2 * ‖gt ω‖ ^ 2) ∂hyps.P =
        ∫ ω, (‖wt ω - wStar‖ ^ 2 - 2 * hyps.η * ⟪wt ω - wStar, gt ω⟫_ℝ) ∂hyps.P +
        ∫ ω, (hyps.η ^ 2 * ‖gt ω‖ ^ 2) ∂hyps.P :=
      integral_add (h_int_norm_sq.sub (h_int_inner.const_mul _)) (h_int_sq.const_mul _)
    have h2 : ∫ ω, (‖wt ω - wStar‖ ^ 2 - 2 * hyps.η * ⟪wt ω - wStar, gt ω⟫_ℝ) ∂hyps.P =
        ∫ ω, ‖wt ω - wStar‖ ^ 2 ∂hyps.P -
        ∫ ω, (2 * hyps.η * ⟪wt ω - wStar, gt ω⟫_ℝ) ∂hyps.P :=
      integral_sub h_int_norm_sq (h_int_inner.const_mul _)
    have h3 : ∫ ω, (2 * hyps.η * ⟪wt ω - wStar, gt ω⟫_ℝ) ∂hyps.P =
        2 * hyps.η * ∫ ω, ⟪wt ω - wStar, gt ω⟫_ℝ ∂hyps.P :=
      integral_const_mul (2 * hyps.η) _
    have h4 : ∫ ω, (hyps.η ^ 2 * ‖gt ω‖ ^ 2) ∂hyps.P =
        hyps.η ^ 2 * ∫ ω, ‖gt ω‖ ^ 2 ∂hyps.P :=
      integral_const_mul (hyps.η ^ 2) _
    linarith [hkey, h1, h2, h3, h4]
  -- Step 3: Unbiasedness — ∫⟪wt−w*, gt⟫ = ∫⟪wt−w*, ∇f(wt)⟫
  have h_unb_cross :
      ∫ ω, ⟪wt ω - wStar, gt ω⟫_ℝ ∂hyps.P =
        ∫ ω, ⟪wt ω - wStar, hyps.gradF (wt ω)⟫_ℝ ∂hyps.P :=
    expectation_inner_gradL_eq
      hyps.hunb hyps.h_indep hyps.h_dist (fun w => w - wStar)
      hyps.h_wt_meas hyps.h_ξt_meas hyps.hgL
      (measurable_id.sub_const wStar) hyps.hgF_meas h_intL h_int_inner
  -- Step 4: Convex FOC — ∫⟪wt−w*, ∇f(wt)⟫ ≥ E[f(wt)] − f(w*)
  have h_foc : ∫ ω, ⟪wt ω - wStar, hyps.gradF (wt ω)⟫_ℝ ∂hyps.P ≥
      ∫ ω, f (wt ω) ∂hyps.P - f wStar := by
    have h_const : ∫ _ : Ω, f wStar ∂hyps.P = f wStar := by
      simp [integral_const, probReal_univ]
    rw [ge_iff_le, ← h_const, ← integral_sub h_int_ft (integrable_const _)]
    exact integral_mono (h_int_ft.sub (integrable_const _)) h_int_gF_inner
      fun ω => (convex_inner_lower_bound hconvex hgrad (wt ω) wStar).trans_eq
                (real_inner_comm _ _)
  -- Step 5: Bounded variance — ∫‖gt‖² ≤ σ²
  have h_var : ∫ ω, ‖gt ω‖ ^ 2 ∂hyps.P ≤ σ ^ 2 :=
    expectation_norm_sq_gradL_bound
      hvar hyps.h_indep hyps.h_dist
      hyps.h_wt_meas hyps.h_ξt_meas hyps.hgL h_int_sq
  -- Combine
  rw [h_int_eq, h_unb_cross]
  nlinarith [h_foc, h_var, sq_nonneg hyps.η,
             mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hη_pos.le)
               (by linarith [h_foc] : 0 ≤ ∫ ω, ⟪wt ω - wStar, hyps.gradF (wt ω)⟫_ℝ ∂hyps.P
                   - (∫ ω, f (wt ω) ∂hyps.P - f wStar)),
             mul_nonneg (sq_nonneg hyps.η) (by linarith [h_var] : (0:ℝ) ≤ σ ^ 2 -
                   ∫ ω, ‖gt ω‖ ^ 2 ∂hyps.P)]

-- ============================================================================
-- Meta-theorem 3: Strongly convex setting
-- ============================================================================

/-- One-step contraction under strong convexity.

Layer: 1 | Gap: Level 2 (composition of Layer 0 infrastructure)
Technique: same norm expansion as convex case, but Step 4 uses
  `strong_convex_inner_lower_bound` to lower-bound ∫⟪wt−w*, ∇f(wt)⟫ by
  μ/2 · E[‖wt−w*‖²], yielding a (1−ημ) contraction factor.
Proof steps:
  [L0: norm_sub_sq_real + inner_smul_right expansion pointwise]
  [L0: integral_congr_ae + integral_add/sub/const_mul (linearity)]
  [dep: expectation_inner_gradL_eq with h = (· − w*)]
  [dep: strong_convex_inner_lower_bound + integral_mono]
  [dep: expectation_norm_sq_gradL_bound]
  [L0: nlinarith to combine]
Note: no L-smoothness needed — the η ≤ 1/L condition is vestigial in this step.
Used in: Algorithms/SGD.lean `one_step_progress_sc`

`E[‖wₜ₊₁ − w*‖²] ≤ (1 − η·μ)·E[‖wₜ − w*‖²] + η²·σ²` -/
theorem stochastic_descent_strongly_convex'
    (hyps : StochasticDescentHyps E S Ω) (f : E → ℝ) {μ σ : ℝ} (wStar : E)
    (hgrad : IsGradientOf' f hyps.gradF)
    (hsc : StrongConvexOn Set.univ μ f)
    (hvar : HasBoundedVariance' hyps.gradL hyps.ν σ)
    (hmin : IsMinimizer' f wStar)
    (hμ_pos : 0 < μ) (hη_pos : 0 < hyps.η)
    (h_intL : ∀ w, Integrable (hyps.gradL w) hyps.ν)
    (h_int_inner : Integrable (fun ω =>
        ⟪hyps.wt ω - wStar, hyps.gradL (hyps.wt ω) (hyps.ξt ω)⟫_ℝ) hyps.P)
    (h_int_sq : Integrable (fun ω =>
        ‖hyps.gradL (hyps.wt ω) (hyps.ξt ω)‖ ^ 2) hyps.P)
    (h_int_norm_sq : Integrable (fun ω => ‖hyps.wt ω - wStar‖ ^ 2) hyps.P)
    (h_int_gF_inner : Integrable (fun ω =>
        ⟪hyps.wt ω - wStar, hyps.gradF (hyps.wt ω)⟫_ℝ) hyps.P) :
    ∫ ω, ‖(hyps.wt ω - hyps.η • hyps.gradL (hyps.wt ω) (hyps.ξt ω)) - wStar‖ ^ 2 ∂hyps.P ≤
      (1 - hyps.η * μ) * ∫ ω, ‖hyps.wt ω - wStar‖ ^ 2 ∂hyps.P
      + hyps.η ^ 2 * σ ^ 2 := by
  haveI := hyps.hP
  set wt := hyps.wt with hwt_def
  set gt := fun ω => hyps.gradL (wt ω) (hyps.ξt ω) with hgt_def
  -- Step 1: Pointwise norm expansion (same as convex case)
  have h_expand : ∀ ω,
      ‖wt ω - hyps.η • gt ω - wStar‖ ^ 2 =
        ‖wt ω - wStar‖ ^ 2
        - 2 * hyps.η * ⟪wt ω - wStar, gt ω⟫_ℝ
        + hyps.η ^ 2 * ‖gt ω‖ ^ 2 := by
    intro ω
    have : wt ω - hyps.η • gt ω - wStar = (wt ω - wStar) - hyps.η • gt ω := by abel
    rw [this, norm_sub_sq_real]
    simp [inner_smul_right, norm_smul, mul_pow, sq_abs]; ring
  -- Integrability of the expanded form
  have h_int_exp : Integrable (fun ω =>
      ‖wt ω - wStar‖ ^ 2 - 2 * hyps.η * ⟪wt ω - wStar, gt ω⟫_ℝ
      + hyps.η ^ 2 * ‖gt ω‖ ^ 2) hyps.P :=
    (h_int_norm_sq.sub (h_int_inner.const_mul (2 * hyps.η))).add
      (h_int_sq.const_mul (hyps.η ^ 2))
  -- Step 2: Integrate the expansion
  have h_int_eq :
      ∫ ω, ‖wt ω - hyps.η • gt ω - wStar‖ ^ 2 ∂hyps.P =
        ∫ ω, ‖wt ω - wStar‖ ^ 2 ∂hyps.P
        - 2 * hyps.η * ∫ ω, ⟪wt ω - wStar, gt ω⟫_ℝ ∂hyps.P
        + hyps.η ^ 2 * ∫ ω, ‖gt ω‖ ^ 2 ∂hyps.P := by
    have hkey : ∫ ω, ‖wt ω - hyps.η • gt ω - wStar‖ ^ 2 ∂hyps.P =
        ∫ ω, (‖wt ω - wStar‖ ^ 2 - 2 * hyps.η * ⟪wt ω - wStar, gt ω⟫_ℝ
          + hyps.η ^ 2 * ‖gt ω‖ ^ 2) ∂hyps.P :=
      integral_congr_ae (Filter.Eventually.of_forall h_expand)
    have h1 : ∫ ω, (‖wt ω - wStar‖ ^ 2 - 2 * hyps.η * ⟪wt ω - wStar, gt ω⟫_ℝ +
        hyps.η ^ 2 * ‖gt ω‖ ^ 2) ∂hyps.P =
        ∫ ω, (‖wt ω - wStar‖ ^ 2 - 2 * hyps.η * ⟪wt ω - wStar, gt ω⟫_ℝ) ∂hyps.P +
        ∫ ω, (hyps.η ^ 2 * ‖gt ω‖ ^ 2) ∂hyps.P :=
      integral_add (h_int_norm_sq.sub (h_int_inner.const_mul _)) (h_int_sq.const_mul _)
    have h2 : ∫ ω, (‖wt ω - wStar‖ ^ 2 - 2 * hyps.η * ⟪wt ω - wStar, gt ω⟫_ℝ) ∂hyps.P =
        ∫ ω, ‖wt ω - wStar‖ ^ 2 ∂hyps.P -
        ∫ ω, (2 * hyps.η * ⟪wt ω - wStar, gt ω⟫_ℝ) ∂hyps.P :=
      integral_sub h_int_norm_sq (h_int_inner.const_mul _)
    have h3 : ∫ ω, (2 * hyps.η * ⟪wt ω - wStar, gt ω⟫_ℝ) ∂hyps.P =
        2 * hyps.η * ∫ ω, ⟪wt ω - wStar, gt ω⟫_ℝ ∂hyps.P :=
      integral_const_mul (2 * hyps.η) _
    have h4 : ∫ ω, (hyps.η ^ 2 * ‖gt ω‖ ^ 2) ∂hyps.P =
        hyps.η ^ 2 * ∫ ω, ‖gt ω‖ ^ 2 ∂hyps.P :=
      integral_const_mul (hyps.η ^ 2) _
    linarith [hkey, h1, h2, h3, h4]
  -- Step 3: Unbiasedness — ∫⟪wt−w*, gt⟫ = ∫⟪wt−w*, ∇f(wt)⟫
  have h_unb_cross :
      ∫ ω, ⟪wt ω - wStar, gt ω⟫_ℝ ∂hyps.P =
        ∫ ω, ⟪wt ω - wStar, hyps.gradF (wt ω)⟫_ℝ ∂hyps.P :=
    expectation_inner_gradL_eq
      hyps.hunb hyps.h_indep hyps.h_dist (fun w => w - wStar)
      hyps.h_wt_meas hyps.h_ξt_meas hyps.hgL
      (measurable_id.sub_const wStar) hyps.hgF_meas h_intL h_int_inner
  -- Step 4: Strong convex FOC — ∫⟪wt−w*, ∇f(wt)⟫ ≥ μ/2 · E[‖wt−w*‖²]
  have h_sc_foc : ∫ ω, ⟪wt ω - wStar, hyps.gradF (wt ω)⟫_ℝ ∂hyps.P ≥
      μ / 2 * ∫ ω, ‖wt ω - wStar‖ ^ 2 ∂hyps.P := by
    rw [ge_iff_le, ← integral_const_mul (μ / 2)]
    exact integral_mono (h_int_norm_sq.const_mul _) h_int_gF_inner
      fun ω => (strong_convex_inner_lower_bound hsc hgrad hmin (wt ω)).trans_eq
                (real_inner_comm _ _)
  -- Step 5: Bounded variance — ∫‖gt‖² ≤ σ²
  have h_var : ∫ ω, ‖gt ω‖ ^ 2 ∂hyps.P ≤ σ ^ 2 :=
    expectation_norm_sq_gradL_bound
      hvar hyps.h_indep hyps.h_dist
      hyps.h_wt_meas hyps.h_ξt_meas hyps.hgL h_int_sq
  -- norm_sq is non-negative (needed by nlinarith)
  have h_norm_sq_nonneg : (0 : ℝ) ≤ ∫ ω, ‖wt ω - wStar‖ ^ 2 ∂hyps.P :=
    integral_nonneg fun ω => sq_nonneg _
  -- Combine
  rw [h_int_eq, h_unb_cross]
  nlinarith [h_sc_foc, h_var, sq_nonneg hyps.η,
             mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hη_pos.le)
               (by linarith [h_sc_foc] : 0 ≤ ∫ ω, ⟪wt ω - wStar, hyps.gradF (wt ω)⟫_ℝ ∂hyps.P
                   - μ / 2 * ∫ ω, ‖wt ω - wStar‖ ^ 2 ∂hyps.P),
             mul_nonneg (sq_nonneg hyps.η) (by linarith [h_var] : (0:ℝ) ≤ σ ^ 2 -
                   ∫ ω, ‖gt ω‖ ^ 2 ∂hyps.P),
             h_norm_sq_nonneg]
