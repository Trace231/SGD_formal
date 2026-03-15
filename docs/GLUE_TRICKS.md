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

### Pattern H: Subgradient Inequality to Inner Product Lower Bound

**Problem**: You have a primitive subgradient condition
`hsubgrad : ∀ w s y, f y ≥ f w + ⟪gradL w s, y - w⟫_ℝ`
and need to derive `⟪gradL w s, w - wStar⟫_ℝ ≥ f w - f wStar`
(i.e., flip the direction from `wStar - w` to `w - wStar`).

**Template**:
```lean
have h_sub := hsubgrad w s wStar
-- h_sub : f wStar ≥ f w + ⟪gradL w s, wStar - w⟫_ℝ
rw [show wStar - w = -(w - wStar) from by abel, inner_neg_right] at h_sub
-- h_sub : f wStar ≥ f w - ⟪gradL w s, w - wStar⟫_ℝ
linarith
-- gives: ⟪gradL w s, w - wStar⟫_ℝ ≥ f w - f wStar
```

**Key lemma**: `inner_neg_right : ⟪x, -y⟫_ℝ = -⟪x, y⟫_ℝ`
Verify the exact name with `search_codebase "inner_neg"` — Mathlib versions
differ between `inner_neg_right`, `inner_neg_left`, and `inner_neg`.

**Direction note**: The subgradient condition gives `⟪g, wStar - w⟫` (direction
toward `wStar`). The norm expansion needs `⟪g, w - wStar⟫` (direction away from
`wStar`). The `abel` + `inner_neg_right` combination handles the sign flip exactly.

**When to use**: Any non-smooth convex algorithm (subgradient method, proximal
SGD) where the convergence proof uses the primitive subgradient inequality
`f(y) ≥ f(w) + ⟨g, y - w⟩` directly rather than via a Layer 1 meta-theorem.

---
