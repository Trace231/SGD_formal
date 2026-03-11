# StochOptLib Design Conventions

This document records design rules and common pitfalls discovered during
formalization. Check these conventions **before** designing theorem signatures
for any new algorithm (Adam, SVRG, AdaGrad, etc.).

---

## Convention 1: Moment Conditions Must Include Integrability

**Severity:** Critical — violating this causes circular proofs

### Rule

NEVER define moment / variance / second-moment conditions using only a
Bochner integral bound. ALWAYS pair the bound with an explicit integrability
assertion.

### Bad

```lean
-- DANGEROUS: trivially true when gradL w is not square-integrable,
-- because Bochner integral returns 0 for non-integrable functions.
def HasBoundedVariance (gradL : E → S → E) (ν : Measure S) (σ : ℝ) : Prop :=
  ∀ w : E, ∫ s, ‖gradL w s‖ ^ 2 ∂ν ≤ σ ^ 2
```

### Good (current library choice)

```lean
-- Bochner bound + explicit integrability.
-- Integrability makes the Bochner integral meaningful and breaks the
-- circular dependency when deriving downstream integrability results.
def HasBoundedVariance (gradL : E → S → E) (ν : Measure S) (σ : ℝ) : Prop :=
  ∀ w : E, Integrable (fun s => ‖gradL w s‖ ^ 2) ν ∧
           ∫ s, ‖gradL w s‖ ^ 2 ∂ν ≤ σ ^ 2
```

### Good (ideal Mathlib-idiomatic alternative)

```lean
-- Memℒp bundles AEStronglyMeasurable + finite p-th moment.
-- Memℒp (gradL w) 2 ν  implies both Integrable (gradL w) ν and
-- Integrable (‖gradL w ·‖^2) ν.
def HasBoundedVariance (gradL : E → S → E) (ν : Measure S) (σ : ℝ) : Prop :=
  ∀ w : E, Memℒp (gradL w) 2 ν ∧ snorm (gradL w) 2 ν ≤ ENNReal.ofReal σ
```

### Why

Mathlib's Bochner integral `∫ f ∂μ` is defined to return **0** when `f` is
not integrable (`¬ Integrable f μ`). This means:

```
¬ Integrable f μ  →  ∫ f ∂μ = 0  →  ∫ f ∂μ ≤ C  (for any C ≥ 0)
```

So the "Bad" definition is trivially satisfied by non-square-integrable
gradient oracles — defeating its purpose entirely. When a downstream proof
tries to derive integrability FROM the bounded-variance hypothesis, it
encounters a circular dependency: the Bochner bound is only meaningful if
integrability is already known.

### Impact on algorithms

| Algorithm | Moment condition | Risk if using Bochner-only |
|-----------|-----------------|---------------------------|
| SGD | `E[‖g‖²] ≤ σ²` | Circular proof for `h_int_sq` |
| Adam | `E[‖g‖²] ≤ σ²` (some analyses need `E[‖g‖⁴]`) | Same + deeper nesting |
| AdaGrad | `Σ E[‖g_t‖²] < ∞` | Same + summability issues |
| SVRG | `E[‖g − ∇f‖²] ≤ ...` (variance reduction) | Same pattern |

---

## Convention 2: Measurability Hierarchy

**Severity:** High — wrong choice causes `simp` / `exact?` failures

### Rule

Use the **weakest** measurability level that suffices for the context:

| Context | Required level | Lean type |
|---------|---------------|-----------|
| Bochner integral `∫ f ∂μ` | `AEStronglyMeasurable f μ` | `AEStronglyMeasurable` |
| Lebesgue integral `∫⁻ f ∂μ` | `AEMeasurable f μ` | `AEMeasurable` |
| Product measure decomposition | `Measurable f` | `Measurable` |
| Measure.map / change of variables | `AEMeasurable f μ` | `AEMeasurable` |

### Common mistake

Using `Measurable` (the strongest) when only `AEStronglyMeasurable` is
needed, or vice versa. This causes type mismatches at application sites.

### Promotion chain

```
Measurable f
  → StronglyMeasurable f            (via .stronglyMeasurable)
  → AEStronglyMeasurable f μ        (via .aestronglyMeasurable)

Measurable f
  → AEMeasurable f μ                (via .aemeasurable)
```

Note: `AEStronglyMeasurable` and `AEMeasurable` are NOT directly comparable.
Both weaken `Measurable` but in different directions.

---

## Convention 3: Type Coercion Pitfalls

**Severity:** Medium — causes parsing errors and unification failures

### Rule 1: Use `NNReal` not `ℝ≥0`

The notation `ℝ≥0` can cause parsing failures in theorem signatures.
Always write `NNReal` explicitly.

```lean
-- Bad: may cause "unexpected token" or "failed to synthesize LE Type"
theorem foo {L : ℝ≥0} : ...

-- Good:
theorem foo {L : NNReal} : ...
```

### Rule 2: `ENNReal.ofReal` direction

When converting between Bochner integrals (ℝ-valued) and Lebesgue integrals
(ℝ≥0∞-valued), the standard bridge is:

```lean
-- ℝ → ℝ≥0∞ (for non-negative functions):
ENNReal.ofReal (∫ f ∂μ) = ∫⁻ x, ENNReal.ofReal (f x) ∂μ
-- only when: f ≥ 0 a.e. AND AEMeasurable f μ
-- Mathlib name: ofReal_integral_eq_lintegral_ofReal (or similar)
```

### Rule 3: `NNReal.toReal` vs `(↑· : ℝ)`

Prefer the coercion `(L : ℝ)` over `L.toReal` for cleaner notation.
Both are definitionally equal but the coercion integrates better with `simp`.

---

## Convention 4: Every Lemma Must Carry a `Used in:` Tag

**Severity:** Medium — enables automated reverse-index maintenance in `docs/CATALOG.md`

### Rule

Every lemma added to `Lib/` or `Algorithms/` must include at least one
`Used in:` line in its Lean docstring, listing the algorithm name, file,
and proof step.

### Format

```lean
Used in: `[Algorithm variant]` ([File], Step N — [brief description])
```

Multiple algorithms should each have their own line.

### Examples

```lean
/-- Bounded variance transfer from sample distribution ν to probability space P.
...
Used in: `SGD non-convex convergence` (Algorithms/SGD.lean, Step 5 — variance bound)
Used in: `SGD convex convergence` (Algorithms/SGD.lean, Step 5 — variance bound)
Used in: `SGD strongly convex convergence` (Algorithms/SGD.lean, Step 5 — variance bound) -/
theorem expectation_norm_sq_gradL_bound ...
```

```lean
/-- If ‖u‖² and ‖v‖² are both integrable, then ⟪u, v⟫ is integrable.
...
Used in: `SGD non-convex convergence` (Algorithms/SGD.lean, h_int_inner — integrability)
Used in: `SGD convex convergence` (Algorithms/SGD.lean, h_int_inner — integrability)
Used in: `SGD strongly convex convergence` (Algorithms/SGD.lean, h_int_inner — integrability) -/
theorem integrable_inner_of_sq_integrable ...
```

### Why

The `Roadmap & Dependency Tree` section of `docs/CATALOG.md` is manually
maintained. Having explicit `Used in:` tags in every docstring means the
catalog can be verified (and eventually auto-generated) by scanning the
source files, rather than relying on human memory.

### Exception

Lemmas in `Lib/Glue/` that are genuinely free of optimization content
(e.g. `integral_inner_gradient_segment`) may use:

```lean
Used in: general Hilbert-space calculus (no algorithm-specific usage)
```

until a concrete algorithm proof imports them.

---

## Convention 5: Iterate-Dependent Oracle Terms

**Severity:** High — causes `HasBoundedVariance'` to be unprovable or vacuous

### Rule

If an algorithm's stochastic oracle contains a deterministic term that depends
on the current iterate (e.g. `gradL_eff(w, s) = gradL(w, s) + h(w)`), then
`E_ν[‖gradL_eff(w, ·)‖²]` depends on `w` and is NOT a uniform constant.
`HasBoundedVariance'` requires a uniform bound — do NOT assume it holds
without checking which resolution applies.

### Two resolutions

**Resolution A (preferred)**: If `h(w) = ∇r(w)` for a known regularizer `r`,
absorb `h(w)` into `gradF` rather than into the variance term. The regularizer
strengthens strong convexity and the extra term cancels in the descent inequality.
The `HasBoundedVariance'` hypothesis then applies to the BASE oracle only.

**Resolution B (fallback)**: If `h(w)` is bounded on the domain (`‖h(w)‖ ≤ K·R`),
add a bounded-domain hypothesis and use Young's inequality to derive a uniform
effective variance `σ_eff² = 2σ² + 2K²R²`.

### Reference

See [`docs/GLUE_TRICKS.md`](GLUE_TRICKS.md) Section 5 for the full derivation,
Lean code templates, and the algorithm impact table.

---

## Convention 6: Dot Notation for Namespace-Local Parameterized Functions

**Severity:** Critical — violating this causes `Application type mismatch` that
agents cannot self-repair, because the error message gives no hint about the fix.

### Rule

Any `def` or `noncomputable def` defined inside `namespace FooSetup` under a
`variable (setup : FooSetup ...)` declaration that takes **additional explicit
parameters** (e.g., a step index `m : ℕ`) MUST be called everywhere using dot
notation: `setup.funcName args`.

Writing `funcName args` (without `setup.`) will fail with a misleading error:
```
Application type mismatch: The argument
  m
has type
  ℕ
but is expected to have type
  FooSetup ...
```
This happens because `variable (setup : ...)` with **round brackets** inserts
`setup` as an **explicit** parameter in the definition. Lean will never
auto-insert explicit parameters at a call site, so you must always provide
`setup` explicitly — the most ergonomic way is dot notation.

### Bad

```lean
namespace SVRGSetup
variable (setup : SVRGSetup E S Ω)

noncomputable def outerProcess (m : ℕ) : ℕ → Ω → E := ...

-- WRONG: Lean sees `outerProcess m` as applying `outerProcess` to `m : ℕ`
-- but the first explicit argument is `setup : SVRGSetup`, not `m`.
theorem foo (m k : ℕ) : ... ‖outerProcess m k ω - wStar‖ ... := ...
```

### Good

```lean
-- CORRECT: dot notation provides `setup` explicitly.
theorem foo (m k : ℕ) : ... ‖setup.outerProcess m k ω - wStar‖ ... := ...
```

### Exception: zero-parameter aliases

If the function takes **no additional explicit parameters** (a plain alias),
dot notation is optional because there is no ambiguity:

```lean
noncomputable def process : ℕ → Ω → E :=   -- no extra params
  sgdProcess setup.w₀ setup.η setup.gradL setup.ξ

-- Both forms work:
setup.process t   -- preferred
process t         -- also OK (Lean fills setup from variable context)
```

### Why agents cannot self-repair this

The error message (`m has type ℕ but expected FooSetup`) does not mention the
missing `setup.` prefix. Agents typically respond by changing argument types or
adding explicit type annotations, which never resolves the root cause. This bug
was observed to persist for 15+ agent turns without progress (SVRGOuterLoop,
March 2026).
