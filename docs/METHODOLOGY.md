-- File: docs/METHODOLOGY.md
# StochOptLib Methodology

This document records the theoretical methodology behind this library:
how to diagnose missing infrastructure (gap taxonomy), how to probe for
it systematically (Stub-Probe protocol), and how to decide which algorithms
to use as probes.

**See also:**
- `docs/CONVENTIONS.md` — design rules for theorem signatures
- `docs/CATALOG.md` — index of all proved lemmas and their gaps

---

## 1. Gap Taxonomy

When a Lean 4 / Mathlib formalization gets stuck, there are exactly three
root causes. Correctly diagnosing the cause determines the fix strategy.

| Type | True cause | Common misdiagnosis |
|------|-----------|---------------------|
| **Level 1: Completely absent** | Mathlib has no result in this area at all | "I'm not searching well enough" |
| **Level 2: Composition missing** | Mathlib has A and B, but no A→B bridge lemma | "I need to prove a brand-new theorem" |
| **Level 3: Form mismatch** | Mathlib has the result but wrong dimension / type / curry form | "It's a Level 1 gap" |

### Examples from SGD formalization

| Lemma | Gap level | Reason |
|-------|-----------|--------|
| `hasDerivAt_comp_lineSegment` | Level 3 | Mathlib has scalar FTC, not the Hilbert-space gradient inner-product form |
| `convex_first_order_condition` | Level 1 | Multivariate convex FOC with `HasGradientAt` is absent from Mathlib |
| `expectation_inner_gradL_eq` | Level 2 | Mathlib has `IndepFun` and Fubini separately, not their practical composition |
| `integrable_norm_sq_of_bounded_var` | Level 2 | Mathlib has `integrable_prod_iff` and independence tools, not their composition for bounded variance |

---

## 2. Stub-Probe Protocol

The Stub-Probe method is the core workflow for discovering and classifying gaps.

### Step 1: Write stubs

For each mathematical step in the natural-language proof, write only the
Lean type signature with `sorry` as the body. This validates the types
without committing to a proof strategy.