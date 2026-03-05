# SGD Convergence Proofs — Strategy and Structure

This document explains the proof strategies for the three classic SGD convergence theorems formalized in this project, along with the supporting infrastructure.

## Overview

We formalize SGD convergence for three settings on a real Hilbert space `E`:

| Theorem | Setting | Rate | File Location |
|---------|---------|------|---------------|
| `sgd_convergence_nonconvex` | L-smooth | O(1/√T) for E[‖∇f‖²] | Main.lean §8 |
| `sgd_convergence_convex` | L-smooth + convex | O(1/√T) for E[f−f*] | Main.lean §9 |
| `sgd_convergence_strongly_convex` | L-smooth + μ-strongly convex | Linear rate for E[‖w−w*‖²] | Main.lean §10 |

Each convergence theorem follows a two-layer structure:
1. **One-step lemma**: A per-iteration bound on expected progress.
2. **Convergence theorem**: Sum/telescope the per-step bounds across T iterations.

## Supporting Infrastructure

### ConvexGradient.lean — First-Order Conditions

Mathlib lacks multivariate first-order conditions for convex/strongly convex functions in Hilbert spaces. We prove them by reduction to the scalar case:

- **`convex_first_order_condition`**: For convex f with gradient ∇f,
  `f(y) ≥ f(x) + ⟪∇f(x), y − x⟫` for all x, y.

  *Strategy*: Define `g(t) = f(x + t·(y−x))` along the line segment. By `ConvexOn.comp_affineMap`, g is convex on ℝ. Apply `ConvexOn.le_slope_of_hasDerivAt` to get `g'(0) ≤ (g(1) − g(0))/(1 − 0)`. The derivative `g'(0) = ⟪∇f(x), y − x⟫` comes from `hasDerivAt_comp_lineSegment` (in SmoothDescent.lean).

- **`strong_convex_first_order_condition`**: For μ-strongly convex f,
  `f(y) ≥ f(x) + ⟪∇f(x), y − x⟫ + μ/2 · ‖y − x‖²`.

  *Strategy*: By `strongConvexOn_iff_convex`, the function `h(w) = f(w) − μ/2 · ‖w‖²` is convex. Apply the convex FOC to h, whose gradient is `∇h(w) = ∇f(w) − μ·w` (proven via `HasFDerivAt` and `hasStrictFDerivAt_norm_sq`). An algebraic identity relating `⟪x, y − x⟫` to norms (using `norm_sub_sq_real`, `real_inner_self_eq_norm_sq`, `real_inner_comm`) yields the result.

- **Corollaries for minimizers**:
  - `convex_inner_lower_bound`: `⟪∇f(w), w − w*⟫ ≥ f(w) − f(w*)`
  - `strong_convex_inner_lower_bound`: `⟪∇f(w), w − w*⟫ ≥ μ/2 · ‖w − w*‖²`

### IndepExpect.lean — Measure-Theoretic Infrastructure

The "take expectation" step in SGD proofs requires:
1. Independence of wₜ from ξₜ (since wₜ depends only on ξ₀,...,ξₜ₋₁)
2. Fubini's theorem to decompose joint expectations
3. Unbiasedness to simplify conditional expectations

Two key lemmas (currently stated with `sorry` for the deep measure theory):

- **`expectation_inner_gradL_eq`**: For independent wₜ, ξₜ with unbiased gradients,
  `E[⟪h(wₜ), ∇L(wₜ, ξₜ)⟫] = E[⟪h(wₜ), ∇f(wₜ)⟫]`

- **`expectation_norm_sq_gradL_bound`**: Under bounded second moment,
  `E[‖∇L(wₜ, ξₜ)‖²] ≤ σ²`

These are the deepest measure-theoretic components and require Fubini's theorem with conditional expectations — an area where Mathlib's probability theory library is still developing.

### SmoothDescent.lean — L-Smoothness Bounds

Provides:
- `lipschitz_gradient_quadratic_bound`: The fundamental quadratic upper bound from L-smoothness:
  `f(y) ≤ f(x) + ⟪∇f(x), y − x⟫ + L/2 · ‖y − x‖²`
- `hasDerivAt_comp_lineSegment`: Derivative of f composed with a line segment, used in the convex FOC proof.

## Theorem 1: Non-Convex Convergence

### One-Step Lemma (`stochastic_descent_nonconvex`)

**Statement**: `E[f(w_{t+1})] ≤ E[f(wₜ)] − η · E[‖∇f(wₜ)‖²] + η²Lσ²/2`

**Proof strategy**:
1. Apply `descent_lemma` pointwise: for each ω,
   `f(wₜ − η·gₜ) ≤ f(wₜ) − η⟪∇f(wₜ), gₜ⟫ + L/2 · η²‖gₜ‖²`
2. Integrate over Ω and use linearity of expectation.
3. Unbiased cross-term (from `expectation_inner_gradL_eq` with `h = gradF`):
   `E[⟪∇f(wₜ), gₜ⟫] = E[⟪∇f(wₜ), ∇f(wₜ)⟫] = E[‖∇f(wₜ)‖²]`
4. Bounded variance (from `expectation_norm_sq_gradL_bound`):
   `E[‖gₜ‖²] ≤ σ²`

**Status**: Steps 1 (pointwise descent) fully proven. Steps 2–4 require IndepExpect infrastructure (currently `sorry`).

### Convergence Theorem (`sgd_convergence_nonconvex`)

**Statement**: `(1/T) · Σₜ E[‖∇f(wₜ)‖²] ≤ 2(f(w₀) − f*)/(ηT) + ηLσ²`

**Proof strategy** (fully formalized):
1. Sum the one-step bounds over t = 0,...,T−1.
2. **Telescope** using `Finset.sum_range_sub`: the function value sums collapse to `f(w₀) − E[f(w_T)]`.
3. **Lower bound**: `E[f(w_T)] ≥ f*` via `integral_mono` (with `sorry` for integrability).
4. **Weaken and divide**: From `η · Σ ≤ (f₀−f*) + Tη²Lσ²/2`, weaken to `η · Σ ≤ 2(f₀−f*) + Tη²Lσ²` using non-negativity of both terms, then divide by ηT.

## Theorem 2: Convex Convergence

### One-Step Lemma (`one_step_progress_convex`)

**Statement**: `E[‖w_{t+1}−w*‖²] ≤ E[‖wₜ−w*‖²] − 2η(E[f(wₜ)]−f*) + η²σ²`

**Proof strategy**:
1. **Norm expansion** (fully proven): For each ω,
   `‖w_{t+1} − w*‖² = ‖wₜ − w*‖² − 2η⟪wₜ−w*, gₜ⟫ + η²‖gₜ‖²`
   via `norm_sub_sq_real` after rewriting `w_{t+1} = wₜ − η·gₜ`.
2. Integrate and use unbiased cross-term:
   `E[⟪wₜ−w*, gₜ⟫] = E[⟪wₜ−w*, ∇f(wₜ)⟫]`
3. Apply convex FOC (`convex_inner_lower_bound`):
   `⟪∇f(w), w−w*⟫ ≥ f(w) − f(w*)`
4. Bounded variance: `E[‖gₜ‖²] ≤ σ²`

**Status**: Step 1 (norm expansion) fully proven. Steps 2–4 require IndepExpect infrastructure (currently `sorry`).

### Convergence Theorem (`sgd_convergence_convex`)

**Statement**: `(1/T) · Σₜ (E[f(wₜ)]−f*) ≤ ‖w₀−w*‖²/(2ηT) + ησ²/2`

**Proof strategy** (fully formalized):
1. Sum the one-step bounds over t = 0,...,T−1.
2. **Telescope**: The distance sums collapse to `‖w₀−w*‖² − E[‖w_T−w*‖²]`.
3. **Drop non-negative term**: `E[‖w_T−w*‖²] ≥ 0` by `integral_nonneg` + `positivity`.
4. **Divide by 2ηT** and simplify using `field_simp`.

## Theorem 3: Strongly Convex Convergence

### One-Step Lemma (`one_step_progress_sc`)

**Statement**: `E[‖w_{t+1}−w*‖²] ≤ (1−ημ) · E[‖wₜ−w*‖²] + η²σ²`

**Proof strategy**:
1. **Norm expansion** (fully proven, same as convex case).
2. Integrate and use unbiased cross-term.
3. Apply strong convex FOC (`strong_convex_inner_lower_bound`):
   `⟪∇f(w), w−w*⟫ ≥ μ/2 · ‖w−w*‖²`
4. Bounded variance: `E[‖gₜ‖²] ≤ σ²`
5. Combine: `E[‖w_{t+1}−w*‖²] ≤ ‖wₜ−w*‖² − ημ‖wₜ−w*‖² + η²σ² = (1−ημ)‖wₜ−w*‖² + η²σ²`

**Status**: Step 1 (norm expansion) fully proven. Steps 2–5 require IndepExpect infrastructure (currently `sorry`).

### Convergence Theorem (`sgd_convergence_strongly_convex`)

**Statement**: `E[‖w_T−w*‖²] ≤ (1−ημ)^T · ‖w₀−w*‖² + ησ²/μ`

**Proof strategy** (fully formalized):
1. **Induction on T**:
   - Base case: `process 0 = w₀` (deterministic), `∫ ‖w₀−w*‖² = ‖w₀−w*‖²` via `integral_const`.
   - Inductive step: Apply `one_step_progress_sc` then use induction hypothesis via `gcongr`.
2. **Noise accumulation**: The key algebraic identity
   `(1−ημ) · ((1−ημ)^T · ‖w₀−w*‖² + ησ²/μ) + η²σ² = (1−ημ)^{T+1} · ‖w₀−w*‖² + ησ²/μ`
   is verified by `field_simp; ring` (the geometric series Σ (1−ημ)^k ≤ 1/(ημ) is embedded in the algebraic identity).

## Remaining `sorry` Summary

| Location | Description | Difficulty |
|----------|-------------|------------|
| Main.lean:300 | `stochastic_descent_nonconvex` integration steps | High (Fubini + independence) |
| Main.lean:360 | Integrability of f ∘ process T | Medium (measurability chain) |
| Main.lean:442 | `one_step_progress_convex` integration steps | High (Fubini + independence) |
| Main.lean:573 | `one_step_progress_sc` integration steps | High (Fubini + independence) |
| IndepExpect.lean:51 | `expectation_inner_gradL_eq` | High (conditional expectation + Fubini) |
| IndepExpect.lean:67 | `expectation_norm_sq_gradL_bound` | High (Fubini + pushforward) |

All remaining `sorry`s are concentrated in the measure-theoretic infrastructure for handling independence and conditional expectations in the stochastic setting. The algebraic and analytic components (descent lemma, norm expansions, convex/strong-convex FOCs, telescoping, geometric series) are fully formalized.
