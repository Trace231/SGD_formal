import Lib.Layer0.GradientFTC
import Lib.Layer0.IndepExpect
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Data.NNReal.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# One-Step Stochastic Descent Meta-Theorems (Layer 1)

Layer: 1 (stochastic optimization abstractions; no specific algorithm)

This file defines the `StochasticDescentHyps` structure and proves the
non-convex one-step stochastic descent meta-theorem.

## Design philosophy

`StochasticDescentHyps` encapsulates exactly the probabilistic and measurability
conditions needed for a single stochastic gradient step, with no reference to
any algorithm's iteration structure (no `sgdProcess`, no step index `t`).
This makes the meta-theorem reusable for SGD, SVRG, Adam, etc. — any algorithm
whose update has the form `wₜ₊₁ = wₜ − η · gradL(wₜ, ξₜ)`.

## Main results

* `StochasticDescentHyps` — one-step stochastic setup structure
* `descent_lemma` — deterministic L-smooth per-step bound
* `stochastic_descent_nonconvex` — expected one-step descent (non-convex setting)

## Gap analysis

* `descent_lemma`: Layer 0 by nature (pure deterministic analysis);
  placed here as a local stepping stone. Gap: Level 2+3 composite.
* `stochastic_descent_nonconvex`: Layer 1 meta-theorem.
  Gap: Level 2 — composes `descent_lemma`, `expectation_inner_gradL_eq`,
  `expectation_norm_sq_gradL_bound` with integral linearity.
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
* `P`, `hP`  : probability space on `Ω`
* `ν`        : sample distribution (= `Measure.map ξ₀ P` for SGD's `sampleDist`)
* `wt`       : current iterate as a random variable `Ω → E`
* `ξt`       : current sample `Ω → S`
* `gradL`    : stochastic gradient oracle
* `gradF`    : true gradient (deterministic)
* `η`        : step size for this one step
* `h_indep`  : independence `wt ⊥ ξt` (for SGD: from `sgdProcess_indepFun_xi`)
* `h_dist`   : pushforward distribution `map(ξt)P = ν`
* `hunb`     : oracle unbiasedness `E_ν[gradL(w,·)] = gradF(w)` -/
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
-- Meta-theorem: stochastic_descent_nonconvex
-- ============================================================================

/-- Expected one-step descent for L-smooth functions (non-convex setting).

Layer: 1 | Gap: Level 2 (composition of Layer 0 infrastructure)
Technique: (1) pointwise descent via `descent_lemma'`; (2) integrate and linearize;
  (3) replace ∫⟪∇f(wt), gt⟫ with ∫‖∇f(wt)‖² via unbiasedness (`expectation_inner_gradL_eq`);
  (4) bound ∫‖gt‖² ≤ σ² via variance bound (`expectation_norm_sq_gradL_bound`).
Proof steps:
  [dep: descent_lemma' pointwise at each ω]
  [L0: integral_mono to integrate the pointwise bound]
  [L0: integral_add + integral_sub + integral_const_mul (linearity)]
  [dep: expectation_inner_gradL_eq with h = gradF (unbiasedness replaces gt with gradF)]
  [dep: expectation_norm_sq_gradL_bound (variance bound)]
  [L0: linarith to combine]
Used in: `stochastic_descent_nonconvex` in Algorithms/SGD.lean (instantiated with
  `wt = setup.process t`, `ξt = setup.ξ t`, `η = setup.η t`)

Key simplification vs. SGD-specific version: no `t : ℕ`, no `sgdProcess`,
no `sgdProcess_indepFun_xi` call — independence and distribution are direct fields.

`E[f(wt − η·gradL(wt, ξt))] ≤ E[f(wt)] − η·E[‖∇f(wt)‖²] + η²·L·σ²/2` -/
theorem stochastic_descent_nonconvex
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
      hyps.hgL hsmooth.continuous.measurable hsmooth.continuous.measurable h_intL h_int_inner
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
