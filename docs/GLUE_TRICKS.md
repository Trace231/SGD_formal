# Glue Tricks — Universal Proof Techniques

This document is **algorithm-agnostic**. The patterns here apply to any Lean 4
stochastic optimization proof, regardless of which algorithm you are formalizing.

Read this document when you are stuck on a specific proof obligation and need to
know which Mathlib lemmas to reach for.

For how to structure a new algorithm's file within THIS library, see
[`docs/ALGORITHM_TEMPLATE.md`](ALGORITHM_TEMPLATE.md).

---

## Section 1 — Gap Classification

Before searching for a proof, classify what kind of gap you have. This determines
the search strategy.

```
Does Mathlib have ANY lemma about this topic?
  └─ No  → Level 1: completely missing. Must write from scratch.
  └─ Yes → Does Mathlib compose A and B to give A→B directly?
              └─ No  → Level 2: composition missing. Write a bridge lemma.
              └─ Yes → Is the Mathlib form exactly what you need?
                          └─ No  → Level 3: form mismatch. Write a thin wrapper.
                          └─ Yes → You should be able to close it without a new lemma.
```

**Level 2 is by far the most common case** in stochastic optimization. Mathlib
has `IndepFun`, has `integral_prod` (Fubini), and has `integral_mono`, but has
no single lemma that chains them together for the "expectation under independence"
pattern needed in descent proofs.

**How to search:** For a Level 2 gap, search for the two component names together.
For example: `IndepFun` + `integral` → finds `IndepFun.integral_mul_of_integrable`.

---

## Section 2 — Mathlib Search Strategies

### Tactic-level search (inside a proof)

```lean
-- 1. Try exact? on the current goal
exact?

-- 2. Normalize first, then search
simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right]
exact?

-- 3. Try apply? if you know the rough shape of the conclusion
apply?

-- 4. Use rw? to find applicable rewrite lemmas
rw?
```

### Namespace-level search (for stochastic optimization)

Key namespaces to `#check` in when stuck:

| Topic | Mathlib namespace / file |
|---|---|
| Bochner integral | `MeasureTheory.integral_*` |
| Fubini | `MeasureTheory.integral_prod` |
| Independence | `ProbabilityTheory.IndepFun.*` |
| Pushforward / change of variables | `MeasureTheory.integral_map` |
| Lipschitz functions | `LipschitzWith.*`, `Mathlib.Topology.MetricSpace.Lipschitz` |
| Inner product algebra | `inner_sub_left`, `inner_add_right`, `inner_smul_right` |
| Norm-squared identities | `norm_sub_sq_real`, `norm_add_sq_real` |
| Integrability of compositions | `Integrable.comp_measurable`, `integrable_map_measure` |
| L² space | `MeasureTheory.Memℒp`, `MeasureTheory.snorm` |

### Text-search in Mathlib source

When `exact?` fails, search Mathlib4 source for the key noun + verb combination.
Example: "integral" + "inner" → `integral_inner` in `Mathlib.MeasureTheory.Integral.Bochner.Basic`.

---

## Section 3 — Standard Proof Patterns

## Section 3 — Standard Proof Patterns

No new patterns — GLUE_TRICKS.md unchanged.

**Validation gate answer:** The SVRGOuterLoop.lean file contains only the `svrgOuterProcess` recursive definition and imports — no convergence theorems or bridge lemmas are proved. Therefore no new proof patterns emerged. All required patterns (Archetype B dual integrability from Section 4b, epoch telescoping from Section 4c snapshot freeze) are already documented.

---


No new patterns — GLUE_TRICKS.md unchanged.


Each pattern is a mini-recipe: problem statement → Mathlib lemmas → code template.

---

### Pattern A: Lipschitz Addition

**Problem**: You have `LipschitzWith L f` and `LipschitzWith M g`. You need
`LipschitzWith (L + M) (fun x => f x + g x)`.

**Mathlib lemma**: `LipschitzWith.add`

```lean
-- Template
have h1 : LipschitzWith L f := ...
have h2 : LipschitzWith M g := ...
have h3 : LipschitzWith (L + M) (fun x => f x + g x) := h1.add h2
```

**Constant NNReal form**: if `M = ⟨c, hc⟩` where `c : ℝ` and `hc : 0 ≤ c`:
```lean
have h2 : LipschitzWith ⟨c, hc⟩ (fun x => c • x) := by
  intro u v
  simp only [edist_nndist]
  rw [← smul_sub, nnnorm_smul]
  simp [NNReal.coe_mk]
```

---

### Pattern B: Integral Linearity

**Problem**: You need `∫ f + g = ∫ f + ∫ g` or `∫ c • f = c • ∫ f`.

**Mathlib lemmas**: `integral_add`, `integral_sub`, `integral_smul`, `integral_const`

**Critical precondition**: `integral_add` requires BOTH functions to be `Integrable`.
Always check integrability before applying linearity.

```lean
-- Template: split integral over sum
have hf : Integrable f μ := ...
have hg : Integrable g μ := ...
rw [integral_add hf hg]

-- Template: pull constant out of inner product under integral
-- ∫ ⟪c • u, v⟫ = ∫ c * ⟪u, v⟫ = c * ∫ ⟪u, v⟫
simp only [inner_smul_left, integral_const_mul]

-- Template: integral of a constant on a probability space
-- ∫ c ∂P = c  (when IsProbabilityMeasure P)
simp [integral_const, probReal_univ]
```

---

### Pattern C: Measurability of Composite Oracle

**Problem**: You have `hgL : Measurable (Function.uncurry gradL)` and
`hmeas_wt : Measurable wt`, `hmeas_ξt : Measurable ξt`. You need
`Measurable (fun ω => gradL (wt ω) (ξt ω))`.

**Key step**: pair `wt` and `ξt` into a product, then compose with `gradL`.

```lean
-- Template
have h : Measurable (fun ω => gradL (wt ω) (ξt ω)) :=
  hgL.comp (hmeas_wt.prodMk hmeas_ξt)
```

**For inner product measurability:**
```lean
-- ⟪f(ω), g(ω)⟫ is measurable when both are measurable
have h : Measurable (fun ω => ⟪f ω, g ω⟫_ℝ) :=
  continuous_inner.measurable.comp (hmeas_f.prodMk hmeas_g)
```

**Promotion chain** (from strongest to weakest):
```
Measurable f
  → f.stronglyMeasurable           (via .stronglyMeasurable)
  → f.aestronglyMeasurable         (via .aestronglyMeasurable)

Measurable f
  → f.aemeasurable                 (via .aemeasurable)
```
Use the weakest level that suffices. Bochner integral needs `AEStronglyMeasurable`;
`integral_map` needs `AEMeasurable`; product measure decomposition needs `Measurable`.

---

### Pattern D: Independence Factorization

**Problem**: You have `h_indep : IndepFun wt ξt P` and need to evaluate
`∫ ω, f(wt ω, ξt ω) ∂P` by decoupling the two random variables.

**Standard chain**: `integral_map` → `indepFun_iff_map_prod_eq_prod_map_map` → `integral_prod` (Fubini) → pointwise bound → `integral_map` back.

```lean
-- Step 1: rewrite product measure using independence
have h_prod_eq : P.map (fun ω => (wt ω, ξt ω)) = (P.map wt).prod ν := by
  rw [(indepFun_iff_map_prod_eq_prod_map_map
      h_wt_meas.aemeasurable h_ξt_meas.aemeasurable).mp h_indep, h_dist]

-- Step 2: transfer integrability to the product measure
have h_int_prod : Integrable f ((P.map wt).prod ν) := by
  have h1 := (integrable_map_measure hf_aesm h_joint_meas).mpr h_int
  rwa [h_prod_eq] at h1

-- Step 3: apply Fubini
rw [integral_prod _ h_int_prod]
-- Now the goal is ∫ w, (∫ s, f(w, s) ∂ν) ∂(P.map wt)
```

**Key fact**: `IndepFun.integral_mul_of_integrable` handles the special case where
`f(wt, ξt) = g(wt) * h(ξt)`. Use it instead of the full chain when applicable.

---

### Pattern E: Norm-Squared Expansion

**Problem**: You need to expand `‖u - v‖²` or `‖u + v‖²` algebraically.

**Mathlib lemmas**: `norm_sub_sq_real`, `norm_add_sq_real`

```lean
-- ‖u - v‖² = ‖u‖² - 2 * ⟪u, v⟫ + ‖v‖²
rw [norm_sub_sq_real]
-- now the goal has ‖u‖^2 + ‖v‖^2 - 2 * inner u v

-- ‖u + v‖² = ‖u‖² + 2 * ⟪u, v⟫ + ‖v‖²
rw [norm_add_sq_real]

-- Inner product: sign and scalar
rw [inner_neg_right]      -- ⟪u, -v⟫ = -⟪u, v⟫
rw [inner_smul_right]     -- ⟪u, c • v⟫ = c * ⟪u, v⟫
rw [real_inner_comm u v]  -- ⟪u, v⟫ = ⟪v, u⟫
```

---

### Pattern F: Integrability from Bound

**Problem**: You need `Integrable f P` but only have a pointwise bound `‖f x‖ ≤ g x`
where `g` is integrable.

**Mathlib lemma**: `Integrable.mono`

```lean
-- Template
apply Integrable.mono h_g_integrable h_f_aesm
refine Filter.Eventually.of_forall (fun ω => ?_)
-- goal: ‖f ω‖ ≤ ‖g ω‖
simp [Real.norm_eq_abs, abs_of_nonneg]
calc ‖f ω‖ ≤ ... := ...
  _ ≤ ‖g ω‖ := ...
```

**Young's inequality for norm-squared sums:**
```lean
-- ‖u + v‖² ≤ 2 * ‖u‖² + 2 * ‖v‖²
have h : ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  nlinarith [norm_add_le u v, sq_nonneg (‖u‖ - ‖v‖)]
```

---

### Pattern G: Lifting Non-Expansive Bound to Squared Norm

**Problem**: You have a non-expansive map `proj` and a fixed point `wStar`:
`‖proj x - proj y‖ ≤ ‖x - y‖` and `proj wStar = wStar`. You need
`‖proj x - wStar‖^2 ≤ ‖x - wStar‖^2`.

**Mathlib lemma**: `pow_le_pow_left₀`

```lean
-- Template
have h_nonexp : ∀ x y, ‖proj x - proj y‖ ≤ ‖x - y‖ := ...
have hproj_wStar : proj wStar = wStar := ...

have h_sq : ‖proj x - wStar‖ ^ 2 ≤ ‖x - wStar‖ ^ 2 := by
  calc
    ‖proj x - wStar‖ ^ 2 = ‖proj x - proj wStar‖ ^ 2 := by
      exact congrArg (fun z => ‖proj x - z‖ ^ 2) hproj_wStar.symm
    _ ≤ ‖x - wStar‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (h_nonexp x wStar) 2
```

**CAUTION**: do **not** use `sq_le_sq'` for this goal. The robust route for norm
goals of this form is `pow_le_pow_left₀` with `norm_nonneg`.

**When to use**: projection, truncation, clipping, or any post-update map
`op` that is non-expansive and has the reference point as a fixed point.

---

### Pattern I: Pointwise Bound → Bounded Variance

**Problem**: You have a uniform pointwise bound `‖f s‖ ≤ G` (or
`‖gradL w s‖ ≤ G` for all `w` and `s`) and need to show that
`fun s => ‖f s‖ ^ 2` is integrable under a probability measure `ν`,
and that `∫ s, ‖f s‖ ^ 2 ∂ν ≤ G ^ 2`.

**Two-layer design** (implemented in `Lib/Glue/Probability.lean`):

*Layer 1 — atomic, pure measure theory (use for any normed-valued function):*

```lean
-- Works for any β : Type* with [NormedAddCommGroup β]
theorem integrable_sq_norm_of_pointwise_bound
    {β : Type*} [NormedAddCommGroup β]
    {f : S → β} {G : ℝ} {ν : Measure S} [IsProbabilityMeasure ν]
    (hbounded : ∀ s, ‖f s‖ ≤ G) :
    Integrable (fun s => ‖f s‖ ^ 2) ν ∧ ∫ s, ‖f s‖ ^ 2 ∂ν ≤ G ^ 2
```

*Layer 2 — thin optimization-vocabulary wrapper (use when the caller has `gradL : E → S → E`):*

```lean
theorem hasBoundedVariance_of_pointwise_bound
    {gradL : E → S → E} {G : ℝ} {ν : Measure S} [IsProbabilityMeasure ν]
    (hbounded : ∀ w s, ‖gradL w s‖ ≤ G) :
    ∀ w, Integrable (fun s => ‖gradL w s‖ ^ 2) ν ∧ ∫ s, ‖gradL w s‖ ^ 2 ∂ν ≤ G ^ 2 :=
  fun w => integrable_sq_norm_of_pointwise_bound (fun s => hbounded w s)
```

**Caller pattern** (in an algorithm proof that has `HasBoundedVariance'`):

```lean
have hvar : HasBoundedVariance' setup.gradL setup.sampleDist G :=
  hasBoundedVariance_of_pointwise_bound hbounded
-- Lean unfolds HasBoundedVariance' and unifies with the expanded return type.
```

**Key ingredients**: `Integrable.mono`, `integrable_const`, `integral_mono`,
`integral_const`, `pow_le_pow_left₀`, `probReal_univ`.

**ARCHITECTURAL RULE**: `integrable_sq_norm_of_pointwise_bound` lives in
`Lib/Glue/Probability.lean` and must stay free of any `Lib/Layer1/` imports.
`hasBoundedVariance_of_pointwise_bound` uses the **expanded return type**
(`∀ w, Integrable ... ∧ ∫ ... ≤ G²`) rather than the `HasBoundedVariance'`
predicate, to prevent circular module dependencies.

**When to use**: Any algorithm whose stochastic oracle is uniformly bounded
pointwise (subgradient methods, clipped SGD, gradient clipping variants).

---

## Section 4 — The Effective Oracle Reframe Technique

**Situation**: An algorithm's update looks like:
$$w_{t+1} = w_t - \eta \cdot h(w_t) - \eta \cdot \text{gradL}(w_t, \xi_t)$$
where $h(w_t)$ is a **deterministic** function of the current iterate (e.g. a
regularization gradient, a momentum term, etc.).

**Key insight**: This can be rewritten as:
$$w_{t+1} = w_t - \eta \cdot \underbrace{[\text{gradL}(w_t, \xi_t) + h(w_t)]}_{\text{gradL}_{\text{eff}}(w_t, \xi_t)}$$

which has EXACTLY the form `wt - η • gradL_eff(wt, ξt)` required by the
Layer 1 meta-theorems.

**Lean reframe**: define new oracle and gradient before writing the bridge:

```lean
/-- Effective stochastic gradient oracle: base oracle + deterministic correction. -/
noncomputable def fooGradL (setup : FooSetup E S Ω) : E → S → E :=
  fun w s => setup.gradL w s + h w  -- h : E → E is the deterministic correction

/-- Effective true gradient: base gradient + correction at the true level. -/
noncomputable def fooGradF (setup : FooSetup E S Ω) : E → E :=
  fun w => setup.gradF w + h w
```

**Why this works**: since $h(w)$ is deterministic, $\mathbb{E}[\text{gradL}_{\text{eff}}(w, \xi)] = \mathbb{E}[\text{gradL}(w, \xi)] + h(w) = \text{gradF}(w) + h(w) = \text{gradF}_{\text{eff}}(w)$. Unbiasedness is preserved.

**What changes vs. what stays the same**:

| Property | After reframe | Note |
|---|---|---|
| Independence `wt ⊥ ξt` | Unchanged | `h(wt)` is a function of `wt`, not `ξt` |
| Distribution `map(ξt)P = ν` | Unchanged | `ξt` itself unchanged |
| Iterate measurability | Unchanged | `wt` unchanged |
| Unbiasedness | Need new proof | Use `integral_add` + original unbiasedness |
| L-smoothness | Need new proof | Use `LipschitzWith.add` (Pattern A) |
| Variance bound | **Caution** — see Section 5 | |

---

## Section 4b — Archetype B Virtual-Step Integrability

**Situation**: The algorithm update has the form
$$\text{process}(t+1) = \text{op}(\text{virtualStep}(t))$$
where `op` is not the identity (e.g. projection, truncation, clipping).

In this setting, the actual iterate and the virtual step are different random
variables, so a single integrability assumption is not enough for the
`integral_mono` bridge.

### Archetype distinction

| Archetype | Update form | Integrability pattern |
|---|---|---|
| A | `process(t+1) = virtualStep(t)` | one path often suffices |
| B | `process(t+1) = op(virtualStep(t))` | require both actual and virtual integrability |

### Required dual hypotheses (Archetype B)

```lean
-- Actual (post-op) distance term
h_int_norm_sq : ∀ t, Integrable (fun ω => ‖process (t+1) ω - wStar‖ ^ 2) P

-- Virtual (pre-op) distance term
h_int_virtual : ∀ t, Integrable (fun ω =>
  ‖virtualStep t ω - wStar‖ ^ 2) P
```

### `integral_mono` template

```lean
-- Pointwise operator bound from non-expansiveness/fixed-point structure
have h_pointwise : ∀ ω, ‖process (t+1) ω - wStar‖ ^ 2 ≤ ‖virtualStep t ω - wStar‖ ^ 2 := by
  intro ω
  -- e.g. op_nonexp_sq ...
  sorry

-- Lift pointwise bound to expectation bound
have h_op_bound :
    ∫ ω, ‖process (t+1) ω - wStar‖ ^ 2 ∂P ≤
      ∫ ω, ‖virtualStep t ω - wStar‖ ^ 2 ∂P := by
  exact integral_mono (h_int_norm_sq t) (h_int_virtual t) h_pointwise
```

### Rule of thumb

If your update is `process(t+1) = op(virtualStep(t))`, always include
`h_int_virtual` as a separate theorem hypothesis alongside `h_int_norm_sq`.

**Confirmed**: Projected GD.  
**Likely same pattern**: truncated GD, clipped SGD, and related post-step operators.

---

## Section 4c — Pattern H: Snapshot Freeze = Archetype A Reduction

**Situation**: A control-variate algorithm introduces a snapshot term updated on an
outer loop, e.g. `wTilde` and `gradLTilde = gradF wTilde`. The full algorithm is
two-level (macro Archetype B), but each inner epoch has fixed snapshot values.

**Key insight**: During one epoch, treat snapshot objects as fixed parameters,
not as state fields. This makes the inner update conform to Archetype A:
`process(t+1) = process(t) - η_t • oracle(process(t), ξ_t)`.

### Template

```lean
-- Freeze snapshot objects as parameters to the inner-loop analysis.
variable (wTilde gradLTilde : E)

-- Control-variate oracle at fixed snapshot.
def cvOracle (w : E) (s : S) : E :=
  gradL w s - gradL wTilde s + gradLTilde

-- Inner-loop process with standard SGD-shaped recursion.
noncomputable def cvProcess : ℕ → Ω → E :=
  sgdProcess w0 η cvOracle ξ

-- Package as ordinary SGDSetup for theorem reuse.
noncomputable def effectiveSGDSetup : SGDSetup E S Ω := {
  w₀ := w0
  η := η
  gradL := cvOracle
  gradF := gradF
  ξ := ξ
  P := P
  hP := hP
  hξ_meas := hξ_meas
  hξ_indep := hξ_indep
  hξ_ident := hξ_ident
}
```

### SVRG example (fixed snapshot epoch)

Use
`svrgOracle(w,s) = gradL(w,s) - gradL(wTilde,s) + gradLTilde`
with `gradLTilde = gradF(wTilde)`, then package via `effectiveSGDSetup` and
discharge the epoch theorem by `simpa` into `sgd_convergence_strongly_convex_v2`.

### Archetype note (macro vs micro)

- **Micro (inner epoch):** Archetype A after freezing `(wTilde, gradLTilde)`.
- **Macro (whole SVRG):** Archetype B due to periodic snapshot update every `m` steps.

### Applicability

Any method whose control-variate term is snapshot-anchored and frozen within an
epoch (e.g. SARAH, SPIDER, SCSG).

---

## Section 5 — Iterate-Dependent Variance Pitfall

This is the most common hidden pitfall when applying the effective oracle reframe.

**Problem**: After reframing, the effective oracle is `gradL_eff(w,s) = gradL(w,s) + h(w)`.
The second moment becomes:
$$\mathbb{E}[\|\text{gradL}_{\text{eff}}(w_t, \xi_t)\|^2] = \mathbb{E}[\|\text{gradL}(w_t, \xi_t) + h(w_t)\|^2]$$

This depends on $w_t$ (the current iterate), so it is **not** a uniform constant.
But `HasBoundedVariance'` requires a uniform constant $\sigma^2$ bounding
$\mathbb{E}_\nu[\|\text{gradL}(w, \cdot)\|^2]$ for ALL $w$.

**Young's inequality reduction**: for any $a, b$:
$$\|a + b\|^2 \leq 2\|a\|^2 + 2\|b\|^2$$

So: $\mathbb{E}[\|\text{gradL}_{\text{eff}}(w, \xi)\|^2] \leq 2\sigma^2 + 2\|h(w)\|^2$.

The term $\|h(w)\|^2$ is still iterate-dependent. Two resolutions follow.

---

### Resolution A: Algebraic — treat `h(w)` as a gradient, not variance

**When to use**: $h(w) = \nabla r(w)$ for a known regularizer $r$ (e.g. weight
decay has $h(w) = \lambda w = \nabla(\lambda/2 \cdot \|w\|^2)$).

**Key insight**: in the strongly convex descent inequality, the $h(w_t)$ term appears
in the gradient oracle AND in the strong convexity condition. When $r$ strengthens
the strong convexity constant (from $\mu$ to $\mu + \lambda$), the extra
$2\lambda^2\|w_t\|^2$ in the variance bound is cancelled by the stronger contraction
$(1 - \eta(\mu + \lambda))$. The net effect is a tighter rate, not looser.

**Lean approach**: define `gradF_eff` to include $h$, then prove the effective
objective $f_\lambda = f + r$ is $(\mu + \lambda)$-strongly convex. The
`HasBoundedVariance'` hypothesis can remain over the BASE oracle `gradL` (constant
$\sigma^2$), because the $h(w)$ term is absorbed into the gradient structure.

```lean
-- The variance hypothesis references only the base oracle:
hvar : HasBoundedVariance setup.gradL setup.sampleDist σ

-- The effective oracle is wdGradL = gradL + λ·w, but the Layer 1 call
-- uses hvar on the base oracle because wdGradF accounts for the λ·w term
-- on both sides of the descent inequality.
```

---

### Resolution B: Domain Bound — add a bounded domain hypothesis

**When to use**: $h(w)$ is an arbitrary function with $\|h(w)\|^2 \leq C$ uniformly
on the domain (e.g. gradient clipping), OR you can derive a uniform iterate bound
from the algorithm's contraction property.

**Lean approach**: add `hR : ∀ t, ‖setup.process t ω‖ ≤ R` as a hypothesis.
Then `‖h(wt)‖² ≤ K²·R²` uniformly, and the effective variance is bounded by
$2\sigma^2 + 2K^2R^2$.

```lean
-- New effective variance constant:
def σ_eff := Real.sqrt (2 * σ ^ 2 + 2 * K ^ 2 * R ^ 2)

-- Proof that HasBoundedVariance' holds for the effective oracle:
have hvar_eff : HasBoundedVariance' fooGradL ν σ_eff := by
  intro w
  constructor
  · -- integrability: use integrable_norm_sq_gradL_comp + Young's inequality
    sorry
  · -- bound: Young's + hR w + original hvar
    calc ∫ s, ‖fooGradL w s‖ ^ 2 ∂ν
        ≤ 2 * ∫ s, ‖gradL w s‖ ^ 2 ∂ν + 2 * ‖h w‖ ^ 2 := by ...
      _ ≤ 2 * σ ^ 2 + 2 * K ^ 2 * R ^ 2 := by ...
      _ = σ_eff ^ 2 := by simp [σ_eff, Real.sq_sqrt (by positivity)]
```

---

### Decision rule

| Situation | Resolution |
|---|---|
| $h(w) = \nabla r(w)$ for a known regularizer $r$ | **A** — absorb into gradient structure |
| $h(w)$ is bounded on the domain (e.g. clipping) | **B** — add domain bound |
| $h(w)$ is unbounded and not a gradient | Neither works easily; reconsider the reframe |

**Algorithm impact table** (Reference for `docs/CONVENTIONS.md` Convention 5):

| Algorithm | Oracle addend | Resolution |
|---|---|---|
| Weight Decay SGD | $\lambda w$ (= $\nabla(\lambda/2 \cdot \|w\|^2)$) | A |
| Gradient Clipping SGD | $\text{clip}(g)$ (bounded by clip threshold) | B |
| Proximal SGD | Proximal step (not a gradient of the base objective) | B or restructure |
| Adam | Adaptive scaling (not a simple addend) | Archetype B algorithm |
