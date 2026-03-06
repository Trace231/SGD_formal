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
