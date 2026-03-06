# StochOptLib Lemma Catalog

This catalog documents every non-trivial lemma in `Lib/`, giving the proof step
sequence, gap classification, and usage context for each entry.

**Gap taxonomy:**
- **Level 1** — result completely absent from Mathlib
- **Level 2** — Mathlib has the parts but not the composition
- **Level 3** — Mathlib has the result in a different form (type/curry/dimension mismatch)

**Proof step labels:**
- `[L0: ...]` — direct Mathlib lemma application
- `[L1: ...]` — calls another Level-1 library lemma
- `[L2: ...]` — bridges two Mathlib lemmas (composition gap)
- `[L3: ...]` — type/form rewriting to match Mathlib

---

## Layer 0 — Pure Math Infrastructure

### `GradientFTC.lean`

---

#### `hasDerivAt_comp_lineSegment`

| Field | Value |
|---|---|
| File | `Lib/Layer0/GradientFTC.lean` |
| Layer | 0 |
| Gap | Level 3 (form mismatch — needs `InnerProductSpace.toDual_apply_apply` bridge) |
| Triggered by | `integral_inner_gradient_segment`, `convex_first_order_condition` |

**Statement:** If `f : E → ℝ` has gradient `gradF w` at every `w`, then
`φ(t) = f(x + t • d)` has derivative `⟪gradF(x + t•d), d⟫` at `t`.

**Proof step sequence:**
1. `[L0: HasGradientAt → HasFDerivAt]` (unwrap gradient to Fréchet derivative)
2. `[L0: HasFDerivAt.comp HasDerivAt (chain rule along line)]`
3. `[L3: InnerProductSpace.toDual_apply_apply]` (convert CLM evaluation to inner product)

---

#### `integral_inner_gradient_segment`

| Field | Value |
|---|---|
| File | `Lib/Layer0/GradientFTC.lean` |
| Layer | 0 |
| Gap | Level 3 (Mathlib has scalar FTC, not Hilbert gradient form) |
| Triggered by | `lipschitz_gradient_quadratic_bound` |

**Statement:** `f(x + d) - f(x) = ∫ t ∈ [0,1], ⟪gradF(x + t•d), d⟫ dt`

**Proof step sequence:**
1. `[dep: hasDerivAt_comp_lineSegment]` (get derivative of φ)
2. `[L0: intervalIntegral.integral_eq_sub_of_hasDerivAt]` (scalar FTC applied to φ)
3. `[L3: simp / ring to match endpoint form]`

---

#### `lipschitz_gradient_quadratic_bound`

| Field | Value |
|---|---|
| File | `Lib/Layer0/GradientFTC.lean` |
| Layer | 0 |
| Gap | Level 2+3 composite (FTC composition + Lipschitz integral estimate) |
| Triggered by | `descent_lemma'` (Layer 1) |

**Statement:** `f(x + d) ≤ f(x) + ⟪gradF(x), d⟫ + L/2 · ‖d‖²`

**Proof step sequence:**
1. `[dep: integral_inner_gradient_segment]` (rewrite f(x+d) - f(x) as integral)
2. `[L0: integral_inner + integral_sub]` (split ⟪gradF(x+t•d), d⟫ = ⟪gradF(x), d⟫ + ⟪gradF(x+t•d) - gradF(x), d⟫)
3. `[L2: LipschitzWith → norm bound on gradient difference]`
4. `[L0: inner_le_iff / Cauchy-Schwarz + norm estimate]`
5. `[L0: linarith to combine]`

---

### `ConvexFOC.lean`

---

#### `convex_first_order_condition`

| Field | Value |
|---|---|
| File | `Lib/Layer0/ConvexFOC.lean` |
| Layer | 0 |
| Gap | Level 1 (multivariate Hilbert-space FOC absent from Mathlib) |
| Triggered by | `convex_inner_lower_bound`, `stochastic_descent_convex'` |

**Statement:** If `f` is convex and `gradF` is its gradient, then `f(y) ≥ f(x) + ⟪gradF(x), y−x⟫`.

**Proof step sequence:**
1. `[L3: f ∘ AffineMap.lineMap = g (line parametrization, form matching via ext+simp+abel)]`
2. `[L0: ConvexOn.comp_affineMap]` (scalar convexity of g)
3. `[L2: hasDerivAt_comp_lineSegment at t=0]` (gradient → scalar derivative)
4. `[L0: ConvexOn.le_slope_of_hasDerivAt]` (scalar FOC)
5. `[L0: simp + linarith]`

---

#### `strong_convex_first_order_condition`

| Field | Value |
|---|---|
| File | `Lib/Layer0/ConvexFOC.lean` |
| Layer | 0 |
| Gap | Level 1 (multivariate strongly convex FOC absent from Mathlib) |
| Triggered by | `strong_convex_inner_lower_bound`, `stochastic_descent_strongly_convex'` |

**Statement:** If `f` is μ-strongly convex, then `f(y) ≥ f(x) + ⟪gradF(x), y−x⟫ + μ/2·‖y−x‖²`.

**Proof step sequence:**
1. `[L0: strongConvexOn_iff_convex]` (reduce to h = f − μ/2·‖·‖² convex)
2. `[L3: gradient of h via hasStrictFDerivAt_norm_sq + CLM smul matching]`
3. `[dep: convex_first_order_condition applied to h]`
4. `[L0: norm_sub_sq_real + inner_sub_right + linarith]`

---

#### `convex_inner_lower_bound`

| Field | Value |
|---|---|
| File | `Lib/Layer0/ConvexFOC.lean` |
| Layer | 0 |
| Gap | Level 1 corollary |
| Triggered by | `stochastic_descent_convex'` Step 4 |

**Statement:** `f(w) − f(w*) ≤ ⟪gradF(w), w − w*⟫`

**Proof step sequence:**
1. `[dep: convex_first_order_condition at (w, wStar)]`
2. `[L0: inner_neg_right + linarith]`

---

#### `strong_convex_inner_lower_bound`

| Field | Value |
|---|---|
| File | `Lib/Layer0/ConvexFOC.lean` |
| Layer | 0 |
| Gap | Level 1 corollary |
| Triggered by | `stochastic_descent_strongly_convex'` Step 4 |

**Statement:** `μ/2 · ‖w − w*‖² ≤ ⟪gradF(w), w − w*⟫` (when f is μ-strongly convex)

**Proof step sequence:**
1. `[dep: strong_convex_first_order_condition at (w, wStar)]`
2. `[L0: norm_neg + linarith]`

---

### `IndepExpect.lean`

---

#### `expectation_norm_sq_gradL_bound`

| Field | Value |
|---|---|
| File | `Lib/Layer0/IndepExpect.lean` |
| Layer | 0 |
| Gap | Level 2 (Mathlib has IndepFun + Fubini separately, not their composition for this purpose) |
| Triggered by | All three Layer 1 meta-theorems (Step 5 — variance bound) |

**Statement:** If `E_ν[‖gradL(w,·)‖²] ≤ σ²` and `wt ⊥ ξt`, then `E_P[‖gradL(wt, ξt)‖²] ≤ σ²`.

**Proof step sequence:**
1. `[L2: indepFun_iff_map_prod_eq_prod_map_map → product measure]`
2. `[L0: integrable_map_measure → push integrability to product measure]`
3. `[L0: integral_map (change of variables, joint → product)]`
4. `[L0: integral_prod (Fubini)]`
5. `[L2: integral_mono + hvar pointwise]`
6. `[L3: integral_const + probReal_univ → σ²]`

---

#### `expectation_inner_gradL_eq`

| Field | Value |
|---|---|
| File | `Lib/Layer0/IndepExpect.lean` |
| Layer | 0 |
| Gap | Level 2 |
| Triggered by | All three Layer 1 meta-theorems (Step 4 — unbiasedness) |

**Statement:** If `E_ν[gradL(w,·)] = gradF(w)` and `wt ⊥ ξt`, then
`E[⟪h(wt), gradL(wt,ξt)⟫] = E[⟪h(wt), gradF(wt)⟫]` for any measurable `h`.

The free parameter `h : E → E` makes this reusable across all three settings:
- Non-convex: `h = gradF`
- Convex/strongly convex: `h = (· − w*)`

**Proof step sequence:**
1. `[L2: same IndepFun → product measure setup as above]`
2. `[L0: integral_map (LHS to product measure)]`
3. `[L0: integral_prod (Fubini)]`
4. `[L2: integral_inner (h_intL w) (h w)]` — extracts direction `h(w)` from inner product integral
5. `[L0: hunb w]` — unbiasedness: `∫ gradL w s ∂ν = gradF w`
6. `[L0: integral_map (RHS back to P)]`

---

## Layer 1 — Stochastic Optimization Meta-Theorems

### `StochasticDescent.lean`

The structure `StochasticDescentHyps` (15 fields) encapsulates one-step
probabilistic setup: `P`, `ν`, `wt`, `ξt`, `gradL`, `gradF`, `η`, independence
`h_indep`, distribution `h_dist`, measurability fields, and unbiasedness `hunb`.

All three meta-theorems below share the 5-step proof skeleton:
1. Pointwise deterministic bound
2. Integrate (integral_mono or integral_congr_ae)
3. Linearity (integral_add/sub/const_mul)
4. Unbiasedness (expectation_inner_gradL_eq)
5. Variance bound (expectation_norm_sq_gradL_bound)

---

#### `stochastic_descent_nonconvex'`

| Field | Value |
|---|---|
| File | `Lib/Layer1/StochasticDescent.lean` |
| Layer | 1 |
| Gap | Level 2 |
| Requires | `IsGradientOf'`, `IsLSmooth'`, `HasBoundedVariance'` |
| Triggered by | SGD non-convex O(1/√T) convergence |

**Statement:** `E[f(wt − η·gradL(wt,ξt))] ≤ E[f(wt)] − η·E[‖∇f(wt)‖²] + η²Lσ²/2`

**Proof step sequence:**
1. `[dep: descent_lemma' pointwise]` — L-smooth quadratic upper bound
2. `[L0: integral_mono]`
3. `[L0: integral_add/sub/const_mul]`
4. `[dep: expectation_inner_gradL_eq with h = gradF]` — ∫⟪∇f, gt⟫ → ∫‖∇f‖²
5. `[dep: expectation_norm_sq_gradL_bound]` — ∫‖gt‖² ≤ σ²
6. `[L0: linarith]`

---

#### `stochastic_descent_convex'`

| Field | Value |
|---|---|
| File | `Lib/Layer1/StochasticDescent.lean` |
| Layer | 1 |
| Gap | Level 2 |
| Requires | `IsGradientOf'`, `ConvexOn`, `HasBoundedVariance'` |
| Note | No L-smoothness needed — convexity alone suffices for the distance bound |
| Triggered by | SGD convex O(1/√T) convergence |

**Statement:** `E[‖wt₊₁ − w*‖²] ≤ E[‖wt − w*‖²] − 2η(E[f(wt)] − f(w*)) + η²σ²`

**Proof step sequence:**
1. `[L0: norm_sub_sq_real + inner_smul_right]` — expand ‖wt₊₁ − w*‖² pointwise
2. `[L0: integral_congr_ae + integral_add/sub/const_mul]`
3. `[dep: expectation_inner_gradL_eq with h = (· − w*)]` — ∫⟪wt−w*, gt⟫ → ∫⟪wt−w*, ∇f⟫
4. `[dep: convex_inner_lower_bound + integral_mono]` — ∫⟪wt−w*, ∇f⟫ ≥ E[f(wt)] − f(w*)
5. `[dep: expectation_norm_sq_gradL_bound]` — ∫‖gt‖² ≤ σ²
6. `[L0: nlinarith]`

**Design note:** The `h = (· − w*)` in `expectation_inner_gradL_eq` requires
`measurable_id.sub_const wStar` (not `hyps.h_wt_meas.sub_const wStar` — the latter
would give measurability of `ω ↦ wt(ω) − w*`, not the pure `w ↦ w − w*` needed).

---

#### `stochastic_descent_strongly_convex'`

| Field | Value |
|---|---|
| File | `Lib/Layer1/StochasticDescent.lean` |
| Layer | 1 |
| Gap | Level 2 |
| Requires | `IsGradientOf'`, `StrongConvexOn`, `HasBoundedVariance'`, `IsMinimizer'` |
| Note | No L-smoothness needed. `hμ_pos` is documented but unused in the proof body |
| Triggered by | SGD strongly convex linear convergence |

**Statement:** `E[‖wt₊₁ − w*‖²] ≤ (1 − ημ)·E[‖wt − w*‖²] + η²σ²`

**Proof step sequence:**
1. `[L0: norm_sub_sq_real + inner_smul_right]` — same expansion as convex case
2. `[L0: integral_congr_ae + integral_add/sub/const_mul]`
3. `[dep: expectation_inner_gradL_eq with h = (· − w*)]`
4. `[dep: strong_convex_inner_lower_bound + integral_mono]` — ∫⟪wt−w*, ∇f⟫ ≥ μ/2·E[‖wt−w*‖²]
5. `[dep: expectation_norm_sq_gradL_bound]`
6. `[L0: nlinarith]` (contraction factor (1−ημ) emerges from combining steps 4+5)
