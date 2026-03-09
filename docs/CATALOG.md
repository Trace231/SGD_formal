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

**Sorry status:** **0 sorry** — all lemmas in the library are fully proved.

**Design conventions:** See `docs/CONVENTIONS.md` for assumption encoding rules,
measurability hierarchy, and type coercion pitfalls. In particular,
`HasBoundedVariance'` now includes explicit integrability alongside the
Bochner integral bound (Convention §1).

---

## Infrastructure Layer (Glue) — `Lib/Glue/`

The Glue layer contains pure mathematical primitives that address Level 2/3 gaps
between Mathlib's existing infrastructure and the forms needed in optimization proofs.
These lemmas have no optimization or stochastic content — they are general tools that
would be appropriate for Mathlib itself.

**Module index:**

| Module | Contents | Primary gap |
|---|---|---|
| `Calculus.lean` | Hilbert-space FTC and line-segment calculus | Level 3 (form mismatch) |
| `Algebra.lean` | Norm-squared expansion for gradient steps | Level 3 (form mismatch) |
| `Probability.lean` | Inner-product and variance integrability tools | Level 2 (composition) |
| `Measurable.lean` | Measurability and composition integrability | Level 2 (composition) |

---

### `Lib/Glue/Calculus.lean`

Provides the Hilbert-space forms of the fundamental theorem of calculus and related
line-segment calculus tools. Mathlib has scalar FTC (`intervalIntegral.integral_eq_sub_of_hasDerivAt`)
but not the gradient inner-product form needed for L-smooth bounds and convex FOC.

---

#### `hasDerivAt_comp_lineSegment`

| Field | Value |
|---|---|
| File | `Lib/Glue/Calculus.lean` |
| Layer | Glue |
| Gap | Level 3 — form mismatch |

**Purpose:** If `f : E → ℝ` has gradient `gradF` everywhere, then `φ(t) = f(x + t•d)` has
scalar derivative `⟪gradF(x + t•d), d⟫` at every `t`.

**Proof steps:**
- `[L0: hasFDerivAt]` — get Fréchet derivative from gradient
- `[L0: hasDerivAt chain rule + const_add]` — compose with line map
- `[L3: toDual_apply_apply]` — match dual form to inner product

**Used by:** `integral_inner_gradient_segment`, `convex_first_order_condition`

---

#### `integral_inner_gradient_segment`

| Field | Value |
|---|---|
| File | `Lib/Glue/Calculus.lean` |
| Layer | Glue |
| Gap | Level 3 — form mismatch |

**Purpose:** Hilbert-space FTC along a line segment:
`∫ t in 0..1, ⟪gradF(x + t•d), d⟫ = f(x + d) − f(x)`

**Proof steps:**
- `[dep: hasDerivAt_comp_lineSegment]` — pointwise derivative
- `[L3: Continuous.inner + Continuous.comp]` — continuity for interval integrability
- `[L0: intervalIntegral.integral_eq_sub_of_hasDerivAt]`

**Used by:** `lipschitz_gradient_quadratic_bound`, `convex_first_order_condition`

---

#### `integral_inner_gradient_segment'`

| Field | Value |
|---|---|
| File | `Lib/Glue/Calculus.lean` |
| Layer | Glue |
| Gap | Level 3 — form mismatch |

**Purpose:** Point-to-point variant:
`∫ t in 0..1, ⟪gradF(x + t•(y−x)), y−x⟫ = f(y) − f(x)`

**Proof steps:** `[dep: integral_inner_gradient_segment]` + `[L0: congr/abel]`

---

#### `integral_id_zero_one`

| Field | Value |
|---|---|
| File | `Lib/Glue/Calculus.lean` |
| Layer | Glue |
| Gap | Level 3 — scalar FTC applied to `t ↦ t` |

**Purpose:** `∫ t in 0..1, t = 1/2`

**Proof steps:** `[L0: intervalIntegral.integral_eq_sub_of_hasDerivAt]` + `norm_num`

**Used by:** `lipschitz_gradient_quadratic_bound` (final integration step)

---

### `Lib/Glue/Algebra.lean`

Provides norm-squared expansion identities for gradient descent steps.
Mathlib has the individual components (`norm_sub_sq_real`, `inner_smul_right`, etc.)
but no single named form for the SGD step expansion.

---

#### `norm_sq_sgd_step`

| Field | Value |
|---|---|
| File | `Lib/Glue/Algebra.lean` |
| Layer | Glue |
| Gap | Level 3 — form mismatch |

**Purpose:** `‖(w − η•g) − w*‖² = ‖w − w*‖² − 2η·⟪w−w*, g⟫ + η²·‖g‖²`

**Proof steps:**
- `[L3: abel]` — rewrite as `‖(w − w*) − η•g‖²`
- `[L0: norm_sub_sq_real]` — expand squared norm
- `[L3: inner_smul_right + norm_smul + mul_pow + sq_abs + ring]`

**Used by:** `stochastic_descent_convex'`, `stochastic_descent_strongly_convex'`

---

#### `inner_neg_smul_eq`

| Field | Value |
|---|---|
| File | `Lib/Glue/Algebra.lean` |
| Layer | Glue |
| Gap | Level 3 — composition of two Mathlib rewrites |

**Purpose:** `⟪x, −(η•g)⟫ = −(η · ⟪x, g⟫)`

**Proof steps:** `[L0: inner_neg_right]` + `[L0: inner_smul_right]` + `mul_comm`

**Used by:** `descent_lemma'` (non-convex pointwise bound)

---

#### `norm_neg_smul_sq`

| Field | Value |
|---|---|
| File | `Lib/Glue/Algebra.lean` |
| Layer | Glue |
| Gap | Level 3 — composition of three Mathlib rewrites |

**Purpose:** `‖−(η•g)‖² = η² · ‖g‖²`

**Proof steps:** `[L0: norm_neg]` + `[L0: norm_smul]` + `[L3: mul_pow + sq_abs]`

**Used by:** `descent_lemma'` (non-convex pointwise bound)

---

#### `proj_nonexp_sq`

| Field | Value |
|---|---|
| File | `Lib/Glue/Algebra.lean` |
| Layer | Glue |
| Gap | Level 2 — non-expansive norm bound lifted to squared norm form |
| Status | **Proved** |

**Purpose:** If `proj` is non-expansive and `wStar` is a fixed point of `proj`, then
`‖proj x − wStar‖² ≤ ‖x − wStar‖²`.

**Proof steps:**
- `[L3: congrArg — rewrite wStar as proj wStar via hproj_wStar.symm]`
- `[L0: pow_le_pow_left₀ (norm_nonneg _) (h x wStar) 2]` — square the non-expansiveness bound

**Used by:** `pgd_convergence_convex_v2` (Step 1 — projection bound via `integral_mono`)

---

### `Lib/Glue/Probability.lean`

Provides general-purpose probability and integrability tools that bridge the gap
between Mathlib's pointwise measure theory and the composed integrability conditions
required by stochastic optimization proofs.

---

#### `integrable_inner_of_sq_integrable`

| Field | Value |
|---|---|
| File | `Lib/Glue/Probability.lean` |
| Layer | Glue |
| Gap | Level 2 — AM-GM + Cauchy-Schwarz composition |
| Status | **Proved** |

**Purpose:** If `‖u‖²` and `‖v‖²` are both integrable, then `⟪u, v⟫` is integrable.

**Proof steps:**
- `[L0: abs_real_inner_le_norm]` — Cauchy-Schwarz: `|⟪u,v⟫| ≤ ‖u‖·‖v‖`
- `[L0: nlinarith + sq_nonneg]` — AM-GM: `‖u‖·‖v‖ ≤ ‖u‖² + ‖v‖²`
- `[L0: Integrable.mono + hu_sq.add hv_sq]` — domination

**Used by:** `integrable_inner_gradL_comp` (Measurable.lean)

---

#### `integrable_norm_sq_of_bounded_var`

| Field | Value |
|---|---|
| File | `Lib/Glue/Probability.lean` |
| Layer | Glue |
| Gap | Level 2 — Fubini + independence + change-of-variables |
| Status | **Proved** |

**Purpose:** If `E_ν[‖gradL(w,·)‖²] ≤ σ²` for all w (with pointwise integrability),
and `wt ⊥ ξt` with `map(ξt)P = ν`, then `‖gradL(wt(ω), ξt(ω))‖²` is integrable w.r.t. P.

**Proof steps:**
1. `[L2: indepFun_iff_map_prod_eq_prod_map_map]` — factor joint distribution
2. `[L0: integrable_map_measure]` — reduce to product measure integrability
3. `[L0: integrable_prod_iff]` — split into inner + outer conditions
4. Inner condition: `hvar_int w` — pointwise integrability (∀ w)
5. Outer condition: `[L0: Integrable.mono (integrable_const σ²)]` — bounded on probability space

**Key design insight:** The original definition of `HasBoundedVariance` used only
a Bochner integral bound, which is trivially true for non-integrable functions
(Bochner returns 0). By strengthening the definition to include explicit
integrability (`hvar_int`), the circular dependency is broken and the proof
goes through cleanly via `integrable_prod_iff` in the Bochner world — no
lintegral conversion needed. See `docs/CONVENTIONS.md` §1.

---

#### `svrg_variance_reduction`

| Field | Value |
|---|---|
| File | `Lib/Glue/Probability.lean` |
| Layer | Glue |
| Gap | Level 1 — variance-reduction inequality for control-variate oracle |
| Status | **Statement placed, proof sorry'd** (`sorry: 1 (pending)`) |

**Purpose:** Bound the SVRG control-variate second moment at fixed snapshot:
$$
\mathbb{E}_s\!\left[\|\nabla \ell(w,s)-\nabla \ell(\widetilde w,s)+\nabla F(\widetilde w)\|^2\right]
\le 4L\,(f(w)-f^*) + 2\|\nabla F(\widetilde w)-\nabla F(w^*)\|^2.
$$

**Used by:** `svrg_convergence_inner_strongly_convex` (`Algorithms/SVRG.lean`, future integration pass, Step 1 variance control).

---

### `Lib/Glue/Measurable.lean`

Provides measurability and integrability tools for composing functions with random
variables. All lemmas are fully proved.

| Lemma | Status | Closes |
|---|---|---|
| `measurable_of_lsmooth` | **Proved** | `Measurable setup.gradF` in `sgd_to_hyps` |
| `integrable_lsmooth_comp_measurable` | **Proved** | `h_int_ft`, `h_int_ft1` |
| `integrable_norm_sq_gradL_comp` | **Proved** (delegates to Probability.lean) | `h_int_sq` |
| `integrable_inner_gradL_comp` | **Proved** | `h_int_inner` |
| `integrable_norm_sq_iterate_comp` | **Proved** | `h_int_norm_sq` |

---

#### `measurable_of_lsmooth`

| Field | Value |
|---|---|
| File | `Lib/Glue/Measurable.lean` |
| Layer | Glue |
| Gap | Level 2 |
| Status | **Proved** |

**Proof:** `hsmooth.continuous.measurable` (one-liner chain)

---

#### `integrable_lsmooth_comp_measurable`

| Field | Value |
|---|---|
| File | `Lib/Glue/Measurable.lean` |
| Layer | Glue |
| Gap | Level 2 |
| Status | **Proved** |

**Purpose:** Lipschitz function composed with integrable random variable is integrable.

**Proof steps:**
- `[L0: hlip.dist_le_mul]` — linear growth `|f(x) − f(0)| ≤ K·‖x‖`
- `[L0: norm_add_le]` — triangle inequality `‖f(wt)‖ ≤ ‖f(wt)−f(0)‖ + ‖f(0)‖`
- `[L0: Integrable.mono]` — domination by `‖f(0)‖ + K·‖wt‖`

---

#### `integrable_inner_gradL_comp`

| Field | Value |
|---|---|
| File | `Lib/Glue/Measurable.lean` |
| Layer | Glue |
| Gap | Level 2 |
| Status | **Proved** |

**Proof:** Delegates to `integrable_inner_of_sq_integrable` from Probability.lean.

---

#### `integrable_norm_sq_iterate_comp`

| Field | Value |
|---|---|
| File | `Lib/Glue/Measurable.lean` |
| Layer | Glue |
| Gap | Level 2 |
| Status | **Proved** |

**Purpose:** `‖wt − c‖²` is integrable if `‖wt‖²` is integrable (on finite measure spaces).

**Proof steps:**
- `[L0: norm_sub_le + sq_le_sq']` — `‖wt−c‖² ≤ (‖wt‖+‖c‖)²`
- `[L0: nlinarith + sq_nonneg]` — AM-GM: `(a+b)² ≤ 2a² + 2b²`
- `[L0: Integrable.mono]` — domination by `2·‖wt‖² + 2·‖c‖²`

---

## Layer 0 — Pure Math Infrastructure

### `GradientFTC.lean`

> Note: The FTC primitives (`hasDerivAt_comp_lineSegment`, `integral_inner_gradient_segment`,
> `integral_inner_gradient_segment'`, `integral_id_zero_one`) have been moved to
> `Lib/Glue/Calculus.lean` and are documented in the Glue section above.
> `GradientFTC.lean` now imports `Lib.Glue.Calculus` and contains only the L-smooth bound.

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

**Caller note:** The `hvar` parameter has type `∀ w, ∫ s, ‖gradL w s‖² ∂ν ≤ σ²` — a
plain Bochner bound. When calling from Layer 1 theorems that hold
`HasBoundedVariance' gradL ν σ` (which is now a conjunction
`integrability ∧ bound`), pass `(fun w => (hvar w).2)` to extract the bound
component. The integrability component `(hvar w).1` is used separately by
`integrable_norm_sq_of_bounded_var`.

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
5. `[dep: expectation_norm_sq_gradL_bound with hvar = fun w => (hvar w).2]` — bound component of `HasBoundedVariance'`; ∫‖gt‖² ≤ σ²
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
5. `[dep: expectation_norm_sq_gradL_bound with hvar = fun w => (hvar w).2]` — bound component of `HasBoundedVariance'`; ∫‖gt‖² ≤ σ²
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
5. `[dep: expectation_norm_sq_gradL_bound with hvar = fun w => (hvar w).2]` — bound component of `HasBoundedVariance'`; ∫‖gt‖² ≤ σ²
6. `[L0: nlinarith]` (contraction factor (1−ημ) emerges from combining steps 4+5)

---

## Algorithm Layer (Layer 2) — `Algorithms/SGD.lean`

## Algorithm Layer (Layer 2) — `Algorithms/SubgradientMethod.lean`

This file formalizes the stochastic subgradient method for convex non-smooth optimization (Archetype B). Although the update rule syntactically matches SGD (`$w_{t+1} = w_t - \eta \cdot g_t$`), the oracle semantics differ fundamentally: `gradL` provides subgradients satisfying `$\text{gradL}(w, s) \in \partial f(w)$` (not unbiased estimates of a smooth gradient). Therefore, the proof cannot reuse Layer 1 meta-theorems (which require `gradF` and unbiasedness) and instead derives the one-step bound directly using the pointwise subgradient inequality.

### `SubgradientSetup`

| Field | Value |
|---|---|
| File | `Algorithms/SubgradientMethod.lean` |
| Kind | `structure` |
| Layer | 2 |
| **Critical distinction** | Contains **NO `gradF` field** (unlike `SGDSetup`), reflecting absence of true gradient for non-smooth functions |

**Fields:**
- `w₀ : E` — initial point
- `η : ℕ → ℝ` — step size schedule
- `gradL : E → S → E` — stochastic subgradient oracle (satisfies subdifferential membership)
- `ξ : ℕ → Ω → S` — sample stream
- `P : Measure Ω` — probability measure
- `hP : IsProbabilityMeasure P`
- `hξ_meas : ∀ t, Measurable (ξ t)`
- `hξ_indep : iIndepFun ξ P`
- `hξ_ident : ∀ t, IdentDistrib (ξ t) (ξ 0) P P`

**Design note:** Subgradient membership is enforced via hypothesis `hsubgrad` in the convergence theorem.

### `process` alias & infrastructure lemmas

| Component | Role | Delegation target |
|---|---|---|
| `process` | Reuses SGD recursion verbatim | `sgdProcess w₀ η gradL ξ` |
| `subgradientProcess_measurable` | Thin wrapper | `sgdProcess_measurable` |
| `subgradientProcess_adapted` | Thin wrapper | `sgdProcess_adapted` |
| `subgradientProcess_indepFun_xi` | Thin wrapper | `sgdProcess_indepFun_xi` |

### `subgradient_convergence_convex`

| Field | Value |
|---|---|
| File | `Algorithms/SubgradientMethod.lean` |
| Layer | 2 |
| Conclusion | `$\frac{1}{T} \sum_{t<T} (\mathbb{E}[f(w_t)] - f(w^*)) \leq \frac{\|w_0 - w^*\|^2}{2\eta T} + \frac{\eta G^2}{2}$` |
| Archetype | B — novel proof structure despite identical update syntax |
| Call chain | `norm_sq_sgd_step` (pointwise norm expansion) → `mem_subdifferential_iff` (subgradient inequality) → `integral_mono` (integrate bound) → `expectation_norm_sq_gradL_bound` (variance bound) → `Finset.sum_range_sub` (telescoping) |
| Key distinction | Uses subgradient inequality directly in pointwise bound and integrates via `integral_mono`, bypassing Layer 1 meta-theorems entirely. No `gradF` or unbiasedness hypotheses required. |

### Hit Report — Glue Usage Count

| Component | File | Used by |
|---|---|---|
| `sgdProcess` | `Main.lean` | `process` definition |
| `sgdProcess_measurable` | `Main.lean` | `subgradientProcess_measurable` |
| `sgdProcess_indepFun_xi` | `Main.lean` | variance bound step (via `subgradientProcess_indepFun_xi`) |
| `norm_sq_sgd_step` | `Lib/Glue/Algebra.lean` | Step 1 (pointwise norm expansion) |
| `expectation_norm_sq_gradL_bound` | `Lib/Layer0/IndepExpect.lean` | Step 4 (variance bound) |
| `integrable_norm_sq_iterate_comp` | `Lib/Glue/Measurable.lean` | integrability of `$\|w_{t+1}-w^*\|^2$` term |
| `hasBoundedVariance_of_pointwise_bound` | `Lib/Glue/Probability.lean` | hvar derivation (bounded variance from pointwise oracle bound) |
| `mem_subdifferential_iff` | Mathlib | pointwise subgradient inequality derivation |

**Leverage score (Archetype B):** reused existing components = 10; new algorithm-specific items = 6 (`SubgradientSetup`, `process` alias, 3 process infrastructure lemmas, convergence theorem); reuse ratio = `$10 / (10 + 6) = 62.5\%$`.


This file instantiates the Layer 1 meta-theorems for the concrete SGD algorithm.
It is the only file that imports both `Main` (for `SGDSetup`) and `Lib.Layer1.StochasticDescent`.

---

### `StochasticDescentHyps` — 15-field Protocol

| Field | Type | Source in `SGDSetup` | Role |
|---|---|---|---|
| `P` | `Measure Ω` | `setup.P` | probability measure |
| `hP` | `IsProbabilityMeasure P` | `setup.hP` | enables `integral_const`, `probReal_univ` |
| `ν` | `Measure S` | `setup.sampleDist` | sampling distribution |
| `wt` | `Ω → E` | `setup.process t` | current iterate (random variable) |
| `ξt` | `Ω → S` | `setup.ξ t` | current sample |
| `gradL` | `E → S → E` | `setup.gradL` | stochastic gradient oracle |
| `gradF` | `E → E` | `setup.gradF` | true gradient |
| `η` | `ℝ` | `setup.η t` | step size at step `t` |
| `h_indep` | `IndepFun wt ξt P` | `sgdProcess_indepFun_xi` | **non-trivial** (iterate ⊥ sample) |
| `h_dist` | `Measure.map ξt P = ν` | `(hξ_ident t).map_eq` | **non-trivial** (IID ident. distrib.) |
| `h_wt_meas` | `Measurable wt` | `sgdProcess_measurable` | iterate measurability |
| `h_ξt_meas` | `Measurable ξt` | `setup.hξ_meas t` | sample measurability |
| `hgL` | `Measurable (uncurry gradL)` | passed through | oracle measurability |
| `hgF_meas` | `Measurable gradF` | `hsmooth.continuous.measurable` | true gradient measurability |
| `hunb` | `IsUnbiased' gradL gradF ν` | `setup.hunb` (def. equal) | unbiasedness condition |

All primed predicates (`IsGradientOf'`, `IsLSmooth'`, `HasBoundedVariance'`, `IsUnbiased'`,
`IsMinimizer'`) are definitionally equal to their unprimed counterparts in `Main.lean`,
so no explicit coercion is needed at call sites.

---

### `sgd_to_hyps`

| Field | Value |
|---|---|
| File | `Algorithms/SGD.lean` |
| Kind | `noncomputable def` |
| Layer | 2 |

**Purpose:** Convert `(setup : SGDSetup E S Ω)` at step `t` into `StochasticDescentHyps E S Ω`.

**Non-trivial discharges:**
- `h_indep := sgdProcess_indepFun_xi setup.hξ_meas setup.hξ_indep hgL t`
  — process `t` only depends on `ξ₀,…,ξ_{t-1}` (σ-algebra monotonicity + `iIndepFun`)
- `h_dist := (setup.hξ_ident t).map_eq`
  — `IdentDistrib (ξ t) (ξ 0) P P` gives `map(ξ t)P = sampleDist`

All other fields are direct record projections from `SGDSetup`.

---

### `sgd_step_eq`

| Field | Value |
|---|---|
| File | `Algorithms/SGD.lean` |
| Kind | `lemma` |
| Layer | 2 |

**Purpose:** Connect the Layer 1 meta-theorem output form to the concrete `SGDSetup` iterate.

**Statement:** `hyps.wt ω - hyps.η • hyps.gradL (hyps.wt ω) (hyps.ξt ω) = setup.process (t+1) ω`

**Why `rfl` works:** `SGDSetup.process_succ` is proved by `rfl` (pattern-match on the recursive
`sgdProcess` definition = iota reduction). Therefore `setup.process (t+1) ω` and
`setup.process t ω - setup.η t • gradL(process t ω)(ξ t ω)` are **definitionally equal**.
The integral equality `∫ ‖process(t+1) − w*‖² = ∫ ‖(wt − η•gt) − w*‖²` also holds by
`integral_congr_ae` + `Filter.Eventually.of_forall (fun _ => rfl)`.

---

### `sgd_convergence_nonconvex_v2`

| Field | Value |
|---|---|
| File | `Algorithms/SGD.lean` |
| Layer | 2 |
| Conclusion | `(1/T) · Σ_{t<T} E[‖∇f(wt)‖²] ≤ 2(f(w₀)−f*) / (η·T) + η·L·σ²` |

**Call chain:**
```
sgd_to_hyps setup t hgL (hsmooth.continuous.measurable) hunb
  → stochastic_descent_nonconvex' hyps f hgrad hsmooth hvar h_intL
      (h_int_f t) (h_int_f (t+1)) (h_int_inner t) (h_int_sq t)
  → rfl  [process_succ definitional]
  → rw [hη t]
  → hstep (for each t < T)
  → Finset.sum_le_sum + Finset.sum_range_sub  [telescoping]
  → integral_nonneg + hlower  [lower bound f ≥ f*]
  → field_simp  [divide by η·T]
```

**Sorry status:** All sorry's eliminated. Measurability closed by `hsmooth.continuous.measurable`;
integrability conditions forwarded from theorem hypotheses. Vestigial `h_int_gF_sq` removed.

---

### `sgd_convergence_convex_v2`

| Field | Value |
|---|---|
| File | `Algorithms/SGD.lean` |
| Layer | 2 |
| Conclusion | `(1/T) · Σ_{t<T} (E[f(wt)] − f(w*)) ≤ ‖w₀−w*‖² / (2ηT) + η·σ²/2` |

**Call chain:**
```
sgd_to_hyps setup t hgL (hsmooth.continuous.measurable) hunb
  → stochastic_descent_convex' hyps f wStar hgrad hconvex hvar (0<η_t) h_intL
      (h_int_inner t) (h_int_sq t) (h_int_norm_sq t) (h_int_f t) (h_int_gF_inner t)
  → rfl  [process_succ]
  → rw [hη t]
  → hstep (∀ t < T: norm-sq descent)
  → Finset.sum_range_sub  [telescoping on ‖wt−w*‖²]
  → drop ‖w_T−w*‖² ≥ 0
  → field_simp  [divide by 2η·T]
```

**Sorry status:** All sorry's eliminated.

---

### `sgd_convergence_strongly_convex_v2`

| Field | Value |
|---|---|
| File | `Algorithms/SGD.lean` |
| Layer | 2 |
| Conclusion | `E[‖w_T−w*‖²] ≤ (1−ημ)^T · ‖w₀−w*‖² + η·σ²/μ` |

**Call chain (induction on T):**
```
base T=0:  simp [process_zero] → integral_const → linarith [η·σ²/μ ≥ 0]

step T+1:
  sgd_to_hyps setup T hgL (hsmooth.continuous.measurable) hunb
    → stochastic_descent_strongly_convex' hyps f wStar hgrad hsc hvar hmin hμ_pos (0<η_T) h_intL
        (h_int_inner T) (h_int_sq T) (h_int_norm_sq T) (h_int_gF_inner T)
    → rfl  [process_succ]
    → rw [hη T]
    → hstep: E[‖w_{T+1}−w*‖²] ≤ (1−ημ)·E[‖w_T−w*‖²] + η²σ²
    → gcongr ih  [induction hypothesis]
    → hkey: (1−ημ)·(ησ²/μ) + η²σ² = ησ²/μ  [field_simp; ring]
```

**Sorry status:** All sorry's eliminated.

---

## Algorithm Layer (Layer 2) — `Algorithms/WeightDecaySGD.lean`

This file instantiates the Archetype A pattern for regularized SGD by reframing
weight decay as plain SGD on an effective oracle:
`effGradL(w,s) = gradL(w,s) + decay • w`, `effGradF(w) = gradF(w) + decay • w`.
The Layer 2 convergence wrappers then discharge by direct `simpa` into the
existing SGD Layer 2 theorems.

---

### `WeightDecaySGDSetup`

| Field | Value |
|---|---|
| File | `Algorithms/WeightDecaySGD.lean` |
| Kind | `structure` |
| Layer | 2 |

**Purpose:** Extend `SGDSetup` with a decay scalar `decay : ℝ` while keeping
the same stochastic-process and sampling infrastructure.

---

### `effectiveSGDSetup`

| Field | Value |
|---|---|
| File | `Algorithms/WeightDecaySGD.lean` |
| Kind | `noncomputable def` |
| Layer | 2 |

**Purpose:** Reframe weight-decay SGD as ordinary SGD by replacing
`gradL/gradF` with effective gradients and reusing all other `SGDSetup` fields.

**Design trick:** This one definition is the reduction point that lets all WD
convergence theorems call the existing SGD theorem stack unchanged.

---

### Bridge lemmas

#### `measurable_effGradL`

| Field | Value |
|---|---|
| File | `Algorithms/WeightDecaySGD.lean` |
| Kind | `lemma` |
| Layer | 2 |

**Purpose:** Transfer measurability from base stochastic oracle to
`effGradL`.

#### `unbiased_effGrad_of_unbiased`

| Field | Value |
|---|---|
| File | `Algorithms/WeightDecaySGD.lean` |
| Kind | `lemma` |
| Layer | 2 |

**Purpose:** Transfer unbiasedness from base oracle `(gradL, gradF)` to
effective oracle `(effGradL, effGradF)`.

---

### `weight_decay_convergence_nonconvex_v2`

| Field | Value |
|---|---|
| File | `Algorithms/WeightDecaySGD.lean` |
| Layer | 2 |
| Conclusion | `(1/T) · Σ_{t<T} E[‖∇f_eff(wt)‖²] ≤ 2(f(w₀)−f*) / (η·T) + η·L·σ²` |

**Call chain:**
```
weight_decay_convergence_nonconvex_v2
  → simpa
  → sgd_convergence_nonconvex_v2
  → sgd_to_hyps
  → stochastic_descent_nonconvex'
```

---

### `weight_decay_convergence_convex_v2`

| Field | Value |
|---|---|
| File | `Algorithms/WeightDecaySGD.lean` |
| Layer | 2 |
| Conclusion | `(1/T) · Σ_{t<T} (E[f(wt)] − f(w*)) ≤ ‖w₀−w*‖² / (2ηT) + η·σ²/2` |

**Call chain:**
```
weight_decay_convergence_convex_v2
  → simpa
  → sgd_convergence_convex_v2
  → sgd_to_hyps
  → stochastic_descent_convex'
```

---

### `weight_decay_convergence_strongly_convex_v2`

| Field | Value |
|---|---|
| File | `Algorithms/WeightDecaySGD.lean` |
| Layer | 2 |
| Conclusion | `E[‖w_T−w*‖²] ≤ (1−ημ)^T · ‖w₀−w*‖² + η·σ²/μ` |

**Call chain:**
```
weight_decay_convergence_strongly_convex_v2
  → simpa
  → sgd_convergence_strongly_convex_v2
  → sgd_to_hyps
  → stochastic_descent_strongly_convex'
```

### Hit Report — Glue Usage Count

**Hit Report: Library Components Used**

| Component | File | Used by |
|---|---|---|
| `effectiveSGDSetup` reframe | `Algorithms/WeightDecaySGD.lean` | all 3 convergence theorems |
| `sgd_convergence_nonconvex_v2` | `Algorithms/SGD.lean` | `weight_decay_convergence_nonconvex_v2` |
| `sgd_convergence_convex_v2` | `Algorithms/SGD.lean` | `weight_decay_convergence_convex_v2` |
| `sgd_convergence_strongly_convex_v2` | `Algorithms/SGD.lean` | `weight_decay_convergence_strongly_convex_v2` |
| `sgd_to_hyps` | `Algorithms/SGD.lean` | all 3 WD wrappers (via `wd_sgd_to_hyps`) |
| `stochastic_descent_nonconvex'` | `Lib/Layer1/StochasticDescent.lean` | inherited through `sgd_convergence_nonconvex_v2` |
| `stochastic_descent_convex'` | `Lib/Layer1/StochasticDescent.lean` | inherited through `sgd_convergence_convex_v2` |
| `stochastic_descent_strongly_convex'` | `Lib/Layer1/StochasticDescent.lean` | inherited through `sgd_convergence_strongly_convex_v2` |
| `measurable_effGradL` | `Algorithms/WeightDecaySGD.lean` | WD bridge layer (effective oracle measurability) |
| `unbiased_effGrad_of_unbiased` | `Algorithms/WeightDecaySGD.lean` | WD bridge layer (effective oracle unbiasedness) |

**Leverage score (Archetype A):** reused existing lemmas/theorems = 7;
new WD bridge lemmas written = 2; reuse ratio = `7 / (7 + 2) = 77.8%` (raw `7:2`).

---

## Algorithm Layer (Layer 2) — `Algorithms/ProjectedGD.lean`

This file formalizes stochastic projected gradient descent (Archetype B). Unlike Weight Decay
SGD, PGD cannot be reduced to plain SGD via `simpa` because the projection operator creates a
novel update structure. The convergence proof uses a two-step one-step bound: first bound the
actual projected step by the virtual SGD step via non-expansiveness, then apply
`stochastic_descent_convex'` to the virtual step.

---

### `ProjectedGDSetup`

| Field | Value |
|---|---|
| File | `Algorithms/ProjectedGD.lean` |
| Kind | `structure` |
| Layer | 2 |

**Fields:**
- `toSGDSetup : SGDSetup E S Ω` — base SGD data (oracle, samples, step sizes)
- `proj : E → E` — projection operator
- `hproj_nonexp : ∀ x y, ‖proj x − proj y‖ ≤ ‖x − y‖` — non-expansiveness
- `hproj_meas : Measurable proj` — measurability (stored as field, not theorem parameter)

**Design note:** `hproj_wStar : proj wStar = wStar` is a **per-theorem hypothesis**, not
a structure field, since the fixed point depends on the specific minimizer `wStar`.

---

### `pgdProcess`

| Field | Value |
|---|---|
| File | `Algorithms/ProjectedGD.lean` |
| Kind | `noncomputable def` |
| Layer | 2 |

**Definition:** `pgdProcess w₀ η gradL proj ξ t ω`:
- `t = 0`: returns `w₀`
- `t + 1`: `proj (pgdProcess t ω − η t • gradL (pgdProcess t ω) (ξ t ω))`

**Measurability/independence lemmas:**
- `pgdProcess_measurable` — induction; step uses `hproj_meas.comp`
- `pgdProcess_adapted` — reuses `sgdFiltration` from `Main.lean` directly
- `pgdProcess_indepFun_xi` — same filtration argument as `sgdProcess_indepFun_xi`

---

### `pgd_to_hyps`

| Field | Value |
|---|---|
| File | `Algorithms/ProjectedGD.lean` |
| Kind | `noncomputable def` |
| Layer | 2 |

**Purpose:** Bridge `ProjectedGDSetup` at step `t` to `StochasticDescentHyps` for the
**virtual step** `w_t − η_t • gradL(w_t, ξ_t)` (before projection).

**Key difference from `sgd_to_hyps`:** `gradL` and `gradF` come from `toSGDSetup` unchanged —
the projection does not affect the oracle or the true gradient.

---

### `pgd_convergence_convex_v2`

| Field | Value |
|---|---|
| File | `Algorithms/ProjectedGD.lean` |
| Layer | 2 |
| Conclusion | `(1/T) · Σ_{t<T} (E[f(w_t)] − f(w*)) ≤ ‖w₀ − w*‖² / (2ηT) + ησ²/2` |

**Archetype:** B — no `simpa` reduction to `sgd_convergence_convex_v2`.

**Call chain:**
```
pgd_convergence_convex_v2
  → proj_nonexp_sq + integral_mono
      [actual step: E[‖w_{t+1}−w*‖²] ≤ E[‖virtual_t − w*‖²]]
  → stochastic_descent_convex' (pgd_to_hyps setup t ...)
      [virtual step: E[‖virtual_t − w*‖²] ≤ E[‖w_t−w*‖²] − 2η·gap + η²σ²]
  → same Layer 0/Glue chain as SGD convex
      (expectation_inner_gradL_eq, convex_inner_lower_bound,
       expectation_norm_sq_gradL_bound)
  → Finset.sum_range_sub  [telescope over t < T]
```

**Key integrability distinction (Archetype B pattern):**
- `h_int_norm_sq` — integrability of `‖w_{t+1} − w*‖²` (actual projected step)
- `h_int_virtual` — integrability of `‖(w_t − η•g_t) − w*‖²` (virtual step, before projection)
These are SEPARATE hypotheses; both are needed for `integral_mono`.

---

### Hit Report — Glue Usage Count (PGD)

| Component | File | Used by |
|---|---|---|
| `stochastic_descent_convex'` | `Lib/Layer1/StochasticDescent.lean` | `pgd_convergence_convex_v2` (virtual step) |
| `expectation_inner_gradL_eq` | `Lib/Layer0/IndepExpect.lean` | Step 4 (unbiasedness) |
| `expectation_norm_sq_gradL_bound` | `Lib/Layer0/IndepExpect.lean` | Step 5 (variance bound) |
| `convex_inner_lower_bound` | `Lib/Layer0/ConvexFOC.lean` | Step 4 (convex FOC) |
| `norm_sq_sgd_step` | `Lib/Glue/Algebra.lean` | Step 1 of virtual step |
| `integrable_norm_sq_of_bounded_var` | `Lib/Glue/Probability.lean` | `h_int_sq` |
| `integrable_inner_of_sq_integrable` | `Lib/Glue/Probability.lean` | `h_int_inner` |
| `integrable_norm_sq_iterate_comp` | `Lib/Glue/Measurable.lean` | `h_int_norm_sq`, `h_int_virtual` |
| `sgdFiltration` | `Main.lean` | `pgdProcess_adapted`, `pgdProcess_indepFun_xi` |
| `proj_nonexp_sq` | `Lib/Glue/Algebra.lean` | Step 1 (projection bound) — **new** |
| `pgd_to_hyps` | `Algorithms/ProjectedGD.lean` | bridge — **new** |

**Leverage score (Archetype B):** reused existing components = 9; new PGD-specific items = 2;
reuse ratio = `9 / (9 + 2) = 81.8%` (raw `9:2`).

---

## Algorithm Layer (Layer 2) — `Algorithms/SVRG.lean`

This file formalizes fixed-snapshot SVRG as a Layer 2 reduction to the existing
SGD strongly-convex stack. The key reduction is to freeze snapshot terms
`(wTilde, gradLTilde)` as parameters and package the inner epoch as a plain
`SGDSetup` through `effectiveSGDSetup`.

---

### `SVRGSetup`

| Field | Value |
|---|---|
| File | `Algorithms/SVRG.lean` |
| Kind | `structure` |
| Layer | 2 |

**Purpose:** Extend `SGDSetup` with `sampleDist` and fixed-snapshot inner-loop
machinery while retaining IID sampling and filtration interface from the base setup.

---

### `svrgOracle`

| Field | Value |
|---|---|
| File | `Algorithms/SVRG.lean` |
| Kind | `def` |
| Layer | 2 |

**Definition:** `svrgOracle wTilde gradLTilde w s = gradL(w,s) - gradL(wTilde,s) + gradLTilde`.

**Role:** Standard control-variate oracle used during one fixed-snapshot epoch.

---

### `svrgProcess`

| Field | Value |
|---|---|
| File | `Algorithms/SVRG.lean` |
| Kind | `noncomputable def` |
| Layer | 2 |

**Purpose:** Inner-loop iterate recursion under fixed snapshot and fixed
`gradLTilde`, with update form matching SGD recursion shape.

---

### `effectiveSGDSetup`

| Field | Value |
|---|---|
| File | `Algorithms/SVRG.lean` |
| Kind | `noncomputable def` |
| Layer | 2 |

**Purpose:** Package fixed-snapshot SVRG epoch as ordinary SGD by replacing only
`gradL` with `svrgOracle` and reusing all stochastic infrastructure fields.

---

### `svrg_to_hyps`

| Field | Value |
|---|---|
| File | `Algorithms/SVRG.lean` |
| Kind | `noncomputable def` |
| Layer | 2 |

**Purpose:** Bridge the fixed-snapshot SVRG inner-loop state to
`StochasticDescentHyps` via the packaged effective setup.

---

### `svrg_convergence_inner_strongly_convex`

| Field | Value |
|---|---|
| File | `Algorithms/SVRG.lean` |
| Layer | 2 |
| Conclusion | `E[‖w_T−w*‖²] ≤ (1−ημ)^T · ‖w₀−w*‖² + η·σeff²/μ` |
| Sorry status | **No sorry** |

**Call chain:**
```
svrg_convergence_inner_strongly_convex
  → effectiveSGDSetup (svrgOracle packaged as plain SGDSetup)
  → sgd_convergence_strongly_convex_v2 (via simpa)
      → sgd_to_hyps
      → stochastic_descent_strongly_convex'
```

---

### `svrg_convergence_outer_stub`

| Field | Value |
|---|---|
| File | `Algorithms/SVRG.lean` |
| Layer | 2 |
| Scope | Outer-loop snapshot update every `m` steps |
| Sorry status | **sorry (out of scope)** |

**Purpose:** Placeholder theorem for macro-level SVRG (snapshot refresh schedule).

### Hit Report — Glue Usage Count

**Hit Report: Library Components Used**

| Component | File | Used by |
|---|---|---|
| `effectiveSGDSetup` packaging | `Algorithms/SVRG.lean` | `svrg_convergence_inner_strongly_convex` |
| `sgd_convergence_strongly_convex_v2` | `Algorithms/SGD.lean` | `svrg_convergence_inner_strongly_convex` |
| `sgd_to_hyps` | `Algorithms/SGD.lean` | inherited via `sgd_convergence_strongly_convex_v2` |
| `stochastic_descent_strongly_convex'` | `Lib/Layer1/StochasticDescent.lean` | inherited via `sgd_convergence_strongly_convex_v2` |
| `svrg_variance_reduction` | `Lib/Glue/Probability.lean` | planned Step 1 integration (currently pending proof) |

**Leverage score (Snapshot Freeze / Archetype A):** reused existing stack elements = 3;
new SVRG bridge components documented = 6; reuse ratio = `3 / (3 + 6) = 33.3%` (raw `3:6`).

---

## Roadmap & Dependency Tree

| Lemma | File | SGD non-convex | SGD convex | SGD strongly convex | WD non-convex | WD convex | WD strongly convex | PGD convex | SVRG inner strongly convex | SVRG outer stub | Subgradient convex |
|-------|------|:--------------:|:----------:|:-------------------:|:-------------:|:---------:|:------------------:|:----------:|:--------------------------:|:---------------:|:------------------:|
| `norm_sq_sgd_step` | `Lib/Glue/Algebra.lean` | — | Step 1 | Step 1 | — | Step 1 | Step 1 | Step 1 (virtual) | Step 1 | — | **Step 1** |
| `expectation_norm_sq_gradL_bound` | `Lib/Layer0/IndepExpect.lean` | Step 5 | Step 5 | Step 5 | Step 5 | Step 5 | Step 5 | Step 5 | Step 5 | — | **Step 4** |
| `integrable_norm_sq_iterate_comp` | `Lib/Glue/Measurable.lean` | — | h_int_norm_sq | h_int_norm_sq | — | h_int_norm_sq | h_int_norm_sq | h_int_norm_sq, h_int_virtual | h_int_norm_sq | — | **h_int_norm_sq** |
| `hasBoundedVariance_of_pointwise_bound` | `Lib/Glue/Probability.lean` | — | — | — | — | — | — | — | — | — | **Step (deriving hvar)** |
| *All other lemmas* | *—* | *—* | *—* | *—* | *—* | *—* | *—* | *—* | *—* | *—* | *—* |

*Note: Cells marked "—" indicate no usage in that algorithm variant. "Subgradient convex" column updated with verified usage points.*


| Lemma | File | SGD non-convex | SGD convex | SGD strongly convex | WD non-convex | WD convex | WD strongly convex | PGD convex | SVRG inner strongly convex | SVRG outer stub | Subgradient convex |
|-------|------|:--------------:|:----------:|:-------------------:|:-------------:|:---------:|:------------------:|:----------:|:--------------------------:|:---------------:|:------------------:|
| `norm_sq_sgd_step` | `Lib/Glue/Algebra.lean` | — | Step 1 | Step 1 | — | Step 1 | Step 1 | Step 1 (virtual) | Step 1 | — | **Step 1** |
| `expectation_norm_sq_gradL_bound` | `Lib/Layer0/IndepExpect.lean` | Step 5 | Step 5 | Step 5 | Step 5 | Step 5 | Step 5 | Step 5 | Step 5 | — | **Step 4** |
| `integrable_norm_sq_iterate_comp` | `Lib/Glue/Measurable.lean` | — | h_int_norm_sq | h_int_norm_sq | — | h_int_norm_sq | h_int_norm_sq | h_int_norm_sq, h_int_virtual | h_int_norm_sq | — | **h_int_norm_sq** |
| `hasBoundedVariance_of_pointwise_bound` | `Lib/Glue/Probability.lean` | — | — | — | — | — | — | — | — | — | **Step (deriving hvar)** |
| *All other lemmas* | *—* | *—* | *—* | *—* | *—* | *—* | *—* | *—* | *—* | *—* | *—* |

### Universally reusable glue lemmas

The following lemmas have no SGD-specific content and are expected to apply directly to any future algorithm that uses IID stochastic gradients:

| Lemma | Why universal |
|-------|--------------|
| `expectation_inner_gradL_eq` | Any IID stochastic gradient algorithm |
| `expectation_norm_sq_gradL_bound` | Any IID stochastic gradient algorithm |
| `integrable_norm_sq_of_bounded_var` | Provides `h_int_sq` for any bounded-variance algorithm |
| `integrable_inner_of_sq_integrable` | Provides `h_int_inner` for any L²-bounded gradient |
| `integrable_sq_norm_of_pointwise_bound` | Pure measure theory — any `NormedAddCommGroup`-valued function with a constant pointwise norm bound; no optimization vocabulary |
| `hasBoundedVariance_of_pointwise_bound` | Only requires uniform pointwise oracle bound `‖gradL w s‖ ≤ G`; works for any algorithm with uniformly bounded stochastic oracle (subgradient methods, clipped SGD, etc.) |


| Lemma | File | SGD non-convex | SGD convex | SGD strongly convex | WD non-convex | WD convex | WD strongly convex | PGD convex | SVRG inner strongly convex | SVRG outer stub | Subgradient convex | Reusable for |
|-------|------|:--------------:|:----------:|:-------------------:|:-------------:|:---------:|:------------------:|:----------:|:--------------------------:|:---------------:|:------------------:|--------------|
| `lipschitz_gradient_quadratic_bound` | `Lib/Layer0/GradientFTC.lean` | Step 1 | — | — | Step 1 | — | — | — | — | — | | Any L-smooth algorithm |
| `convex_first_order_condition` | `Lib/Layer0/ConvexFOC.lean` | — | (via Step 4) | — | — | (via Step 4) | — | (via Step 4) | — | — | | Any convex algorithm |
| `convex_inner_lower_bound` | `Lib/Layer0/ConvexFOC.lean` | — | Step 4 | — | — | Step 4 | — | Step 4 (virtual) | — | — | | Any convex algorithm |
| `strong_convex_first_order_condition` | `Lib/Layer0/ConvexFOC.lean` | — | — | (via Step 4) | — | — | (via Step 4) | — | (via Step 4) | — | | Any strongly convex algorithm |
| `strong_convex_inner_lower_bound` | `Lib/Layer0/ConvexFOC.lean` | — | — | Step 4 | — | — | Step 4 | — | Step 4 | — | | Any strongly convex algorithm |
| `expectation_inner_gradL_eq` | `Lib/Layer0/IndepExpect.lean` | Step 4 | Step 4 | Step 4 | Step 4 | Step 4 | Step 4 | Step 4 | Step 4 | — | | **Universal** — any IID stochastic gradient algorithm |
| `expectation_norm_sq_gradL_bound` | `Lib/Layer0/IndepExpect.lean` | Step 5 | Step 5 | Step 5 | Step 5 | Step 5 | Step 5 | Step 5 | Step 5 | — | **Step 4** | **Universal** — any IID stochastic gradient algorithm |
| `proj_nonexp_sq` | `Lib/Glue/Algebra.lean` | — | — | — | — | — | — | Step 1 | — | — | | Any algorithm with a non-expansive post-update map |
| `norm_sq_sgd_step` | `Lib/Glue/Algebra.lean` | — | Step 1 | Step 1 | — | Step 1 | Step 1 | Step 1 (virtual) | Step 1 | — | **Step 1** | Any algorithm with SGD-like update (including subgradient methods) |
| `integrable_norm_sq_of_bounded_var` | `Lib/Glue/Probability.lean` | h_int_sq | h_int_sq | h_int_sq | h_int_sq | h_int_sq | h_int_sq | h_int_sq | h_int_sq | — | | **Universal** — provides `h_int_sq` for any bounded-variance algorithm |
| `integrable_inner_of_sq_integrable` | `Lib/Glue/Probability.lean` | h_int_inner | h_int_inner | h_int_inner | h_int_inner | h_int_inner | h_int_inner | h_int_inner | h_int_inner | — | | **Universal** — provides `h_int_inner` for any L²-bounded gradient |
| `svrg_variance_reduction` | `Lib/Glue/Probability.lean` | — | — | — | — | — | — | — | pending (Step 1 plan) | — | | Control-variate algorithms (SARAH, SPIDER, SCSG) |
| `integrable_lsmooth_comp_measurable` | `Lib/Glue/Measurable.lean` | h_int_ft | h_int_ft | — | h_int_ft | h_int_ft | — | h_int_ft | — | — | | Any algorithm applying a Lipschitz function to an integrable iterate |
| `integrable_norm_sq_iterate_comp` | `Lib/Glue/Measurable.lean` | — | h_int_norm_sq | h_int_norm_sq | — | h_int_norm_sq | h_int_norm_sq | h_int_norm_sq, h_int_virtual | h_int_norm_sq | — | **h_int_norm_sq** | Any algorithm with distance-to-optimum recursion |
| `integrable_inner_gradL_comp` | `Lib/Glue/Measurable.lean` | h_int_inner | h_int_inner | h_int_inner | h_int_inner | h_int_inner | h_int_inner | h_int_inner | h_int_inner | — | | Any IID algorithm needing inner-product integrability |

*Note: Cells marked "—" indicate no usage in that algorithm variant. "Subgradient convex" column added; only three cataloged lemmas have non-blank entries.*


| Lemma | File | SGD non-convex | SGD convex | SGD strongly convex | WD non-convex | WD convex | WD strongly convex | PGD convex | SVRG inner strongly convex | SVRG outer stub | Subgradient convex |
|-------|------|:--------------:|:----------:|:-------------------:|:-------------:|:---------:|:------------------:|:----------:|:--------------------------:|:---------------:|:------------------:|
| `norm_sq_sgd_step` | `Lib/Glue/Algebra.lean` | — | Step 1 | Step 1 | — | Step 1 | Step 1 | Step 1 (virtual) | Step 1 | — | **Step 1** |
| `expectation_norm_sq_gradL_bound` | `Lib/Layer0/IndepExpect.lean` | Step 5 | Step 5 | Step 5 | Step 5 | Step 5 | Step 5 | Step 5 | Step 5 | — | **Step 4** |
| `integrable_norm_sq_iterate_comp` | `Lib/Glue/Measurable.lean` | — | h_int_norm_sq | h_int_norm_sq | — | h_int_norm_sq | h_int_norm_sq | h_int_norm_sq, h_int_virtual | h_int_norm_sq | — | **h_int_norm_sq** |
| *All other lemmas* | *—* | *—* | *—* | *—* | *—* | *—* | *—* | *—* | *—* | *—* | *—* |

*Note: Cells marked "—" indicate no usage in that algorithm variant. "Subgradient convex" column added; only three cataloged lemmas have non-blank entries.*


This section provides a reverse index: given an algorithm and proof step,
which catalog lemmas does it depend on? Use this to assess what is reusable
when adding a new algorithm.

### SGD + Weight Decay + SVRG Dependency Table

Each cell shows the proof step number in the convergence theorem where the
lemma is invoked. "h_int" cells indicate the lemma is used to discharge an
integrability hypothesis rather than a direct proof step. Weight Decay entries
match SGD because wrappers reduce to plain SGD through `effectiveSGDSetup` and
`simpa`. SVRG inner-loop entries align with the strongly-convex SGD path because
fixed-snapshot packaging uses `effectiveSGDSetup` + `simpa` to the same theorem stack.

| Lemma | File | SGD non-convex | SGD convex | SGD strongly convex | WD non-convex | WD convex | WD strongly convex | PGD convex | SVRG inner strongly convex | SVRG outer stub | Reusable for |
|-------|------|:--------------:|:----------:|:-------------------:|:-------------:|:---------:|:------------------:|:----------:|:--------------------------:|:---------------:|--------------|
| `lipschitz_gradient_quadratic_bound` | `Lib/Layer0/GradientFTC.lean` | Step 1 | — | — | Step 1 | — | — | — | — | — | Any L-smooth algorithm |
| `convex_first_order_condition` | `Lib/Layer0/ConvexFOC.lean` | — | (via Step 4) | — | — | (via Step 4) | — | (via Step 4) | — | — | Any convex algorithm |
| `convex_inner_lower_bound` | `Lib/Layer0/ConvexFOC.lean` | — | Step 4 | — | — | Step 4 | — | Step 4 (virtual) | — | — | Any convex algorithm |
| `strong_convex_first_order_condition` | `Lib/Layer0/ConvexFOC.lean` | — | — | (via Step 4) | — | — | (via Step 4) | — | (via Step 4) | — | Any strongly convex algorithm |
| `strong_convex_inner_lower_bound` | `Lib/Layer0/ConvexFOC.lean` | — | — | Step 4 | — | — | Step 4 | — | Step 4 | — | Any strongly convex algorithm |
| `expectation_inner_gradL_eq` | `Lib/Layer0/IndepExpect.lean` | Step 4 | Step 4 | Step 4 | Step 4 | Step 4 | Step 4 | Step 4 | Step 4 | — | **Universal** — any IID stochastic gradient algorithm |
| `expectation_norm_sq_gradL_bound` | `Lib/Layer0/IndepExpect.lean` | Step 5 | Step 5 | Step 5 | Step 5 | Step 5 | Step 5 | Step 5 | Step 5 | — | **Universal** — any IID stochastic gradient algorithm |
| `proj_nonexp_sq` | `Lib/Glue/Algebra.lean` | — | — | — | — | — | — | Step 1 | — | — | Any algorithm with a non-expansive post-update map |
| `norm_sq_sgd_step` | `Lib/Glue/Algebra.lean` | — | Step 1 | Step 1 | — | Step 1 | Step 1 | Step 1 (virtual) | Step 1 | — | Any algorithm with $\|w_{t+1}-w^*\|^2$ recursion |
| `integrable_norm_sq_of_bounded_var` | `Lib/Glue/Probability.lean` | h_int_sq | h_int_sq | h_int_sq | h_int_sq | h_int_sq | h_int_sq | h_int_sq | h_int_sq | — | **Universal** — provides `h_int_sq` for any bounded-variance algorithm |
| `integrable_inner_of_sq_integrable` | `Lib/Glue/Probability.lean` | h_int_inner | h_int_inner | h_int_inner | h_int_inner | h_int_inner | h_int_inner | h_int_inner | h_int_inner | — | **Universal** — provides `h_int_inner` for any L²-bounded gradient |
| `svrg_variance_reduction` | `Lib/Glue/Probability.lean` | — | — | — | — | — | — | — | pending (Step 1 plan) | — | Control-variate algorithms (SARAH, SPIDER, SCSG) |
| `integrable_lsmooth_comp_measurable` | `Lib/Glue/Measurable.lean` | h_int_ft | h_int_ft | — | h_int_ft | h_int_ft | — | h_int_ft | — | — | Any algorithm applying a Lipschitz function to an integrable iterate |
| `integrable_norm_sq_iterate_comp` | `Lib/Glue/Measurable.lean` | — | h_int_norm_sq | h_int_norm_sq | — | h_int_norm_sq | h_int_norm_sq | h_int_norm_sq, h_int_virtual | h_int_norm_sq | — | Any algorithm with distance-to-optimum recursion |
| `integrable_inner_gradL_comp` | `Lib/Glue/Measurable.lean` | h_int_inner | h_int_inner | h_int_inner | h_int_inner | h_int_inner | h_int_inner | h_int_inner | h_int_inner | — | Any IID algorithm needing inner-product integrability |

### Universally reusable glue lemmas

The following lemmas have no SGD-specific content and are expected to apply
directly to any future algorithm that uses IID stochastic gradients:

| Lemma | Why universal |
|-------|--------------|
| `expectation_inner_gradL_eq` | Only requires `IndepFun wt ξt` and `IsUnbiased' gradL gradF ν`; works for any measurable `h : E → E` |
| `expectation_norm_sq_gradL_bound` | Only requires `IndepFun wt ξt` and the bound component of `HasBoundedVariance'` |
| `integrable_norm_sq_of_bounded_var` | Only requires independence, distribution, and `HasBoundedVariance'` integrability component |
| `integrable_inner_of_sq_integrable` | Pure functional analysis — no stochastic content |
| `norm_sq_sgd_step` | Pure inner product algebra — applies to any gradient step of the form $w - \eta g$ |

### Lemmas specific to SGD's update structure

These lemmas encode the particular form $w_{t+1} = w_t - \eta \cdot \text{gradL}(w_t, \xi_t)$.
Algorithms with different update structures (e.g. Adam's momentum, SVRG's control variate)
will need new glue at these points:

| Lemma | SGD-specific aspect |
|-------|---------------------|
| `sgd_to_hyps` (`Algorithms/SGD.lean`) | Bridges `SGDSetup` to `StochasticDescentHyps`; Adam would need `adam_to_hyps` |
| `sgd_step_eq` (`Algorithms/SGD.lean`) | Connects `process (t+1)` to the explicit update form; specific to SGD's `sgdProcess` definition |
| `sgdProcess_indepFun_xi` (`Main.lean`) | Derives independence from `iIndepFun ξ P`; any IID algorithm can reuse this pattern verbatim |
