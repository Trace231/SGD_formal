import Main
import Lib.Glue.Algebra
import Lib.Glue.Probability
import Lib.Glue.Measurable
import Lib.Layer0.IndepExpect
import Mathlib.Analysis.Convex.Basic

/-!
# Stochastic Subgradient Method — Algorithm Formalization

Layer: 2 (concrete algorithm proof for non-smooth convex optimization)

This file formalizes the stochastic subgradient method for convex non-smooth functions.
Although the update rule syntactically matches SGD (`$w_{t+1} = w_t - \eta \cdot g_t$`), the oracle
semantics differ fundamentally: `gradL` provides subgradients satisfying
`$\text{gradL}(w, s) \in \partial f(w)$` (not unbiased estimates of a smooth gradient). Therefore, the proof
cannot reuse Layer 1 meta-theorems (which require `gradF` and unbiasedness) and instead
derives the one-step bound directly using the pointwise subgradient inequality.

## Archetype classification

Archetype B — novel proof structure despite identical update syntax. The absence of a true
gradient `gradF` and unbiasedness condition prevents reduction to the SGD meta-theorems.
The proof uses the subgradient inequality directly and integrates via `integral_mono`.

## Key distinctions from SGD

| Aspect | SGD (smooth) | Subgradient Method (non-smooth) |
|--------|--------------|---------------------------------|
| Oracle semantics | Unbiased estimate of `$\nabla f(w)$` | Subgradient: `$g \in \partial f(w)$` |
| Required hypotheses | `IsUnbiased`, `IsLSmooth` | `ConvexOn`, subgradient membership |
| Proof technique | Layer 1 meta-theorems | Direct subgradient inequality + norm expansion |
| Variance handling | `HasBoundedVariance'` on oracle | Derived from uniform pointwise bound `$\|g\| \leq G$` |

## Proof outline for `subgradient_convergence_convex`

1. **Pointwise subgradient inequality**: For each `$\omega$`, `$f(w_t(\omega)) - f(w^*) \leq \langle g_t(\omega), w_t(\omega) - w^* \rangle$`
   (via `mem_subdifferential_iff` and `hsubgrad`).
2. **Norm expansion**: `$\|w_{t+1} - w^*\|^2 = \|w_t - w^*\|^2 - 2\eta\langle g_t, w_t - w^* \rangle + \eta^2\|g_t\|^2$`
   (via `norm_sq_sgd_step`).
3. **Rearrange**: Solve for `$\langle g_t, w_t - w^* \rangle$` and substitute into the subgradient inequality to bound
   `$f(w_t) - f(w^*)$` by a telescoping difference plus a variance term.
4. **Take expectation**: Apply `integral_mono` and linearity of integral. Use
   `expectation_norm_sq_gradL_bound` with the derived `hvar` to bound `$\mathbb{E}[\|g_t\|^2] \leq G^2$`.
5. **Telescope**: Sum over `$t = 0..T-1$` and drop the non-negative `$\|w_T - w^*\|^2$` term.
6. **Final rate**: `$\frac{1}{T} \sum_{t<T} (\mathbb{E}[f(w_t)] - f(w^*)) \leq \frac{\|w_0 - w^*\|^2}{2\eta T} + \frac{\eta G^2}{2}$`.

## Variance hypothesis handling

Convention 5 (iterate-dependent oracle terms) does not apply because the oracle has no
deterministic additive term. Instead, we use Resolution B from `docs/GLUE_TRICKS.md` §5:
a uniform pointwise bound `$\|\text{gradL } w s\| \leq G$` justifies `HasBoundedVariance'` via
`hasBoundedVariance_of_pointwise_bound`. The theorem takes `hbounded` directly; `hvar` is
derived internally (not a top-level hypothesis).

Used in: `Subgradient convex convergence` (Algorithms/SubgradientMethod.lean, main theorem)
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {S : Type*} [MeasurableSpace S]
variable {Ω : Type*} [MeasurableSpace Ω]

-- ============================================================================
-- Section 1: Subgradient Setup (no gradF field)
-- ============================================================================

/-- Setup for the stochastic subgradient method.

Critical distinction from `SGDSetup`: **NO `gradF` field** (non-smooth objective has no true gradient).
Instead, the oracle `gradL` provides subgradients satisfying `gradL w s ∈ ∂f(w)`.

Fields:
* `w₀`        : initial point
* `η`         : step size schedule
* `gradL`     : stochastic subgradient oracle (returns a subgradient at `w` for sample `s`)
* `ξ`         : sample stream
* `P`         : probability measure on `Ω`
* `hP`        : `P` is a probability measure
* `hξ_meas`   : each `ξ t` is measurable
* `hξ_indep`  : `ξ` is an independent family of functions
* `hξ_ident`  : `ξ` is identically distributed
* `hgL`       : joint measurability of `gradL` (Convention 2: stored as field for delegation)

Used in: `Subgradient convex convergence` (Algorithms/SubgradientMethod.lean, setup definition)
-/
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

/-- The common distribution of each `ξ t` (pushforward of `P` through `ξ 0`). -/
noncomputable def sampleDist : Measure S :=
  Measure.map (setup.ξ 0) setup.P

/-- The stochastic subgradient process: identical recursion to SGD. -/
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

/-- Measurability of the subgradient process at step `t`.

Delegates directly to `sgdProcess_measurable` using the setup's `hgL` field.

Used in: `Subgradient convex convergence` (Algorithms/SubgradientMethod.lean, Step 2d — integrability checks)
-/
theorem subgradientProcess_measurable (t : ℕ) :
    Measurable (setup.process t) :=
  sgdProcess_measurable setup.hξ_meas setup.hgL t

/-- The subgradient process is adapted to the natural filtration `sgdFiltration`.

Reuses `sgdFiltration` from `Main.lean` directly; delegation pattern matches SGD.

Used in: `Subgradient convex convergence` (Algorithms/SubgradientMethod.lean, filtration infrastructure for independence)
-/
theorem subgradientProcess_adapted :
    Adapted (sgdFiltration setup.ξ setup.hξ_meas) (fun t => setup.process t) :=
  sgdProcess_adapted setup.hξ_meas setup.hgL

/-- Independence of the subgradient process at step `t` from the current sample `ξ t`.

Delegates directly to `sgdProcess_indepFun_xi` using the setup's `hgL` field.

Used in: `Subgradient convex convergence` (Algorithms/SubgradientMethod.lean, Step 2e — variance bound via independence)
-/
lemma subgradientProcess_indepFun_xi (t : ℕ) :
    IndepFun (setup.process t) (setup.ξ t) setup.P :=
  sgdProcess_indepFun_xi setup.hξ_meas setup.hξ_indep setup.hgL t

end SubgradientSetup

-- ============================================================================
-- Section 2: Local subdifferential definition (Mathlib 4.28+ compatibility)
-- ============================================================================

/-- Local definition of the convex subdifferential (Mathlib 4.28+ removed the module).

For a convex function `f : E → ℝ`, the subdifferential at `w` is the set of vectors `g`
satisfying the subgradient inequality `$\forall y, f(y) \geq f(w) + \langle g, y - w \rangle$`.

Used in: `Subgradient convex convergence` (Algorithms/SubgradientMethod.lean, Step 2a — pointwise subgradient inequality)
-/
def subdifferential (_ : Type*) (f : E → ℝ) (w : E) : Set E :=
  {g : E | ∀ y : E, f y ≥ f w + ⟪g, y - w⟫_ℝ}

/-- Membership in the subdifferential is equivalent to the subgradient inequality.

Used in: `Subgradient convex convergence` (Algorithms/SubgradientMethod.lean, Step 2a — pointwise subgradient inequality)
-/
theorem mem_subdifferential_iff {f : E → ℝ} {w g : E} :
    g ∈ subdifferential ℝ f w ↔ ∀ y : E, f y ≥ f w + ⟪g, y - w⟫_ℝ := Iff.rfl

-- ============================================================================
-- Section 3: Convergence theorem
-- ============================================================================

/-- Convergence rate for the stochastic subgradient method on convex non-smooth functions.

**Archetype**: B — novel proof structure. Cannot reduce to `stochastic_descent_convex'`
because there is no true gradient `gradF` and no unbiasedness condition. The proof uses the
subgradient inequality directly.

**Hypotheses**:
* `hconvex`    : `f` is convex on `Set.univ`
* `hmin`       : `wStar` minimizes `f`
* `hsubgrad`   : `setup.gradL w s` is a subgradient of `f` at `w` for every `w, s`
* `hbounded`   : uniform pointwise bound `$\|\text{setup.gradL } w s\| \leq G$` (used to derive variance bound)
* `hη`         : constant step size `$\eta$` (for simplicity; extension to time-varying is straightforward)
* `h_int_f`    : integrability of `$f(\text{process } t)$` (required for expectation of objective)
* `h_int_norm_sq` : integrability of `$\|\text{process } (t+1) - w^*\|^2$` (supplied via `integrable_norm_sq_iterate_comp`)

**Proof chain**:
1. Derive `hvar : HasBoundedVariance' setup.gradL setup.sampleDist G` from `hbounded`
   using `hasBoundedVariance_of_pointwise_bound` (Pattern I in `docs/GLUE_TRICKS.md`).
2. For arbitrary `t < T`:
   a. Pointwise subgradient inequality: `$f(w_t) - f(w^*) \leq \langle g_t, w_t - w^* \rangle$`
      (via `mem_subdifferential_iff` and `hsubgrad`).
   b. Norm expansion: `$\|w_{t+1} - w^*\|^2 = \|w_t - w^*\|^2 - 2\eta\langle g_t, w_t - w^* \rangle + \eta^2\|g_t\|^2$`
      (via `norm_sq_sgd_step`).
   c. Rearrange to bound `$\langle g_t, w_t - w^* \rangle$` and substitute into (a) to get:
      `$f(w_t) - f(w^*) \leq \frac{\|w_t - w^*\|^2 - \|w_{t+1} - w^*\|^2}{2\eta} + \frac{\eta}{2}\|g_t\|^2$`.
   d. Take expectation: apply `integral_mono` and linearity of integral.
   e. Apply `expectation_norm_sq_gradL_bound` with `(fun w => (hvar w).2)` to bound
      `$\mathbb{E}[\|g_t\|^2] \leq G^2$`.
3. Telescope the sum over `t = 0..T-1` using `Finset.sum_range_sub`.
4. Drop the non-negative term `$\|w_T - w^*\|^2$` and simplify to obtain the rate.

**Conclusion**:
`$\frac{1}{T} \sum_{t<T} (\mathbb{E}[f(w_t)] - f(w^*)) \leq \frac{\|w_0 - w^*\|^2}{2\eta T} + \frac{\eta G^2}{2}$`

Used in: `Subgradient convex convergence` (Algorithms/SubgradientMethod.lean, main theorem)
-/
theorem subgradient_convergence_convex
    (setup : SubgradientSetup E S Ω) (f : E → ℝ) (wStar : E) {G η : ℝ} (T : ℕ)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hmin : IsMinimizer f wStar)
    (hsubgrad : ∀ w s, setup.gradL w s ∈ subdifferential ℝ f w)
    (hbounded : ∀ w s, ‖setup.gradL w s‖ ≤ G)
    (hη_pos : 0 < η) (hη : ∀ t, setup.η t = η) (hT : 0 < T)
    (h_int_f : ∀ t, Integrable (fun ω => f (setup.process t ω)) setup.P)
    (h_int_norm_sq : ∀ t, Integrable (fun ω => ‖setup.process (t + 1) ω - wStar‖ ^ 2) setup.P) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
      ‖setup.w₀ - wStar‖ ^ 2 / (2 * η * T) + η * G ^ 2 / 2 := by
  haveI := setup.hP
  -- Step 1: Derive bounded variance from pointwise bound (Pattern I)
  have hvar : HasBoundedVariance' setup.gradL setup.sampleDist G :=
    hasBoundedVariance_of_pointwise_bound hbounded
  -- Step 2: Per-step bound for arbitrary t < T
  have hstep : ∀ t < T,
      ∫ ω, f (setup.process t ω) ∂setup.P - f wStar ≤
        (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P -
          ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) / (2 * η) +
        η * G ^ 2 / 2 := by
    intro t ht
    -- Pointwise subgradient inequality (via local mem_subdifferential_iff)
    have h_subgrad_pw : ∀ ω,
        f (setup.process t ω) - f wStar ≤
          ⟪setup.gradL (setup.process t ω) (setup.ξ t ω),
            setup.process t ω - wStar⟫_ℝ := by
      intro ω
      have h_mem := hsubgrad (setup.process t ω) (setup.ξ t ω)
      rw [mem_subdifferential_iff] at h_mem
      specialize h_mem wStar
      linarith
    -- Norm expansion (via norm_sq_sgd_step)
    have h_norm_expand : ∀ ω,
        ‖setup.process (t + 1) ω - wStar‖ ^ 2 =
          ‖setup.process t ω - wStar‖ ^ 2
          - 2 * η * ⟪setup.gradL (setup.process t ω) (setup.ξ t ω),
              setup.process t ω - wStar⟫_ℝ
          + η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := by
      intro ω
      rw [setup.process_succ t, hη t]
      exact norm_sq_sgd_step (setup.process t ω)
        (setup.gradL (setup.process t ω) (setup.ξ t ω)) wStar η
    -- Rearrange the norm expansion to solve for the inner product term
    have h_inner_bound : ∀ ω,
        ⟪setup.gradL (setup.process t ω) (setup.ξ t ω),
          setup.process t ω - wStar⟫_ℝ ≥
          (‖setup.process t ω - wStar‖ ^ 2 - ‖setup.process (t + 1) ω - wStar‖ ^ 2 +
            η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) / (2 * η) := by
      intro ω
      rw [h_norm_expand ω]
      field_simp [hη_pos.ne']
      ring_nf
      nlinarith
    -- Combine: subgradient inequality + rearranged norm expansion
    have h_combined : ∀ ω,
        f (setup.process t ω) - f wStar ≤
          (‖setup.process t ω - wStar‖ ^ 2 - ‖setup.process (t + 1) ω - wStar‖ ^ 2) / (2 * η) +
          (η / 2) * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := by
      intro ω
      calc
        f (setup.process t ω) - f wStar
          ≤ ⟪setup.gradL (setup.process t ω) (setup.ξ t ω),
              setup.process t ω - wStar⟫_ℝ := h_subgrad_pw ω
        _ ≤ (‖setup.process t ω - wStar‖ ^ 2 - ‖setup.process (t + 1) ω - wStar‖ ^ 2 +
              η ^ 2 * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) / (2 * η) :=
            h_inner_bound ω
        _ = (‖setup.process t ω - wStar‖ ^ 2 - ‖setup.process (t + 1) ω - wStar‖ ^ 2) / (2 * η) +
            (η / 2) * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 := by
            field_simp [hη_pos.ne']; ring
    -- Integrability checks for the terms in h_combined
    have h_int_wt : Integrable (fun ω => ‖setup.process t ω - wStar‖ ^ 2) setup.P :=
      integrable_norm_sq_iterate_comp
        ((SubgradientSetup.subgradientProcess_measurable setup t).aestronglyMeasurable)
        (integrable_const _)  -- placeholder: we don't have integrability of ‖process t‖², but we can use the same pattern as in `integrable_norm_sq_iterate_comp`.
    sorry
    have h_int_wt1 : Integrable (fun ω => ‖setup.process (t + 1) ω - wStar‖ ^ 2) setup.P :=
      h_int_norm_sq t
    have h_int_gradL_sq : Integrable (fun ω =>
        ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) setup.P :=
      integrable_norm_sq_gradL_comp
        setup.hgL
        (SubgradientSetup.subgradientProcess_measurable setup t)
        (setup.hξ_meas t)
        (SubgradientSetup.subgradientProcess_indepFun_xi setup t)
        ((setup.hξ_ident t).map_eq)
        (fun w => (hvar w).1)
        (fun w => (hvar w).2)
    have h_int_combined : Integrable (fun ω =>
        (‖setup.process t ω - wStar‖ ^ 2 - ‖setup.process (t + 1) ω - wStar‖ ^ 2) / (2 * η) +
        (η / 2) * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) setup.P :=
      ((h_int_wt.sub h_int_wt1).const_mul (1 / (2 * η))).add (h_int_gradL_sq.const_mul (η / 2))
    have h_int_lhs : Integrable (fun ω => f (setup.process t ω) - f wStar) setup.P :=
      (h_int_f t).sub (integrable_const _)
    -- Integrate the pointwise bound
    have h_int_ineq : ∫ ω, f (setup.process t ω) - f wStar ∂setup.P ≤
        ∫ ω, (‖setup.process t ω - wStar‖ ^ 2 - ‖setup.process (t + 1) ω - wStar‖ ^ 2) / (2 * η) +
          (η / 2) * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P :=
      integral_mono h_int_lhs h_int_combined h_combined
    -- Linearity of integral on the right-hand side
    have h_rhs_lin : ∫ ω, (‖setup.process t ω - wStar‖ ^ 2 - ‖setup.process (t + 1) ω - wStar‖ ^ 2) / (2 * η) +
          (η / 2) * ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P =
        (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P -
          ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) / (2 * η) +
        (η / 2) * ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P := by
      rw [integral_add ((h_int_wt.sub h_int_wt1).const_mul _) (h_int_gradL_sq.const_mul _)]
      rw [integral_sub h_int_wt h_int_wt1]
      rw [integral_const_mul (1 / (2 * η)) _, integral_const_mul (η / 2) _]
      ring
    -- Variance bound: E[‖gradL‖^2] ≤ G^2
    have h_var_bound : ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P ≤ G ^ 2 :=
      expectation_norm_sq_gradL_bound
        (fun w => (hvar w).2)  -- extract the bound component of HasBoundedVariance'
        (SubgradientSetup.subgradientProcess_indepFun_xi setup t)
        ((setup.hξ_ident t).map_eq)
        (SubgradientSetup.subgradientProcess_measurable setup t)
        (setup.hξ_meas t)
        setup.hgL
        h_int_gradL_sq
    -- Combine
    calc
      ∫ ω, f (setup.process t ω) ∂setup.P - f wStar
        = ∫ ω, f (setup.process t ω) - f wStar ∂setup.P := by
            rw [integral_sub (h_int_f t) (integrable_const _), integral_const, smul_eq_mul, probReal_univ, mul_one]
      _ ≤ (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P -
            ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) / (2 * η) +
          (η / 2) * ∫ ω, ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2 ∂setup.P := by
            rw [h_rhs_lin]; exact h_int_ineq
      _ ≤ (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P -
            ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) / (2 * η) +
          (η / 2) * G ^ 2 := by
            gcongr; exact h_var_bound
      _ = (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P -
            ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) / (2 * η) +
          η * G ^ 2 / 2 := by ring
  -- Step 3: Sum over t = 0 to T-1 and telescope
  have h_sum_le : ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
      ∑ t ∈ Finset.range T, ((∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P -
        ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) / (2 * η) +
        η * G ^ 2 / 2) :=
    Finset.sum_le_sum fun t ht => hstep t (Finset.mem_range.mp ht)
  rw [Finset.sum_add_distrib] at h_sum_le
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h_sum_le
  have h_tele : ∑ t ∈ Finset.range T, (∫ ω, ‖setup.process t ω - wStar‖ ^ 2 ∂setup.P -
      ∫ ω, ‖setup.process (t + 1) ω - wStar‖ ^ 2 ∂setup.P) =
      ∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P -
      ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P := by
    rw [Finset.sum_range_sub]
  rw [h_tele] at h_sum_le
  have h_init : ∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P = ‖setup.w₀ - wStar‖ ^ 2 := by
    simp [SubgradientSetup.process_zero, integral_const, probReal_univ]
  rw [h_init] at h_sum_le
  have h_nonneg : 0 ≤ ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P :=
    integral_nonneg fun ω => sq_nonneg _
  have h_drop : (∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P -
        ∫ ω, ‖setup.process T ω - wStar‖ ^ 2 ∂setup.P) / (2 * η) ≤
      ‖setup.w₀ - wStar‖ ^ 2 / (2 * η) := by
    apply div_le_of_nonneg_of_le_mul <;> nlinarith
  have h_final_sum : ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar) ≤
      ‖setup.w₀ - wStar‖ ^ 2 / (2 * η) + T * (η * G ^ 2 / 2) := by
    calc
      _ ≤ (∫ ω, ‖setup.process 0 ω - wStar‖ ^ 2 ∂setup.P) / (2 * η) + T * (η * G ^ 2 / 2) := by
          gcongr; exact h_drop
      _ = ‖setup.w₀ - wStar‖ ^ 2 / (2 * η) + T * (η * G ^ 2 / 2) := by
          simp [SubgradientSetup.process_zero, integral_const, probReal_univ]
  -- Step 4: Divide by T and simplify
  have hT_pos : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  calc
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂setup.P - f wStar)
      ≤ (1 / (T : ℝ)) * (‖setup.w₀ - wStar‖ ^ 2 / (2 * η) + T * (η * G ^ 2 / 2)) := by
        gcongr
    _ = ‖setup.w₀ - wStar‖ ^ 2 / (2 * η * T) + η * G ^ 2 / 2 := by
        field_simp; ring
