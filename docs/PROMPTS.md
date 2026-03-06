# StochOptLib Agent Prompt Library

This file collects all reusable agent prompts for the StochOptLib project.
Each prompt is self-contained and can be copied directly into a new Cursor agent session.

**Reading order for context:**
`README.md` → `CONVENTIONS.md` → `CATALOG.md` → `GLUE_TRICKS.md` → `ALGORITHM_TEMPLATE.md`

## How to use this file

**For a NEW algorithm**: use `docs/META_PROMPTS.md` to generate the prompts automatically.
- Meta-Prompt A generates the Prover prompt (given algorithm name + update rule + proof sketch).
- Meta-Prompt B generates the Archivist prompt (given completed proof + new lemma list).

The prompts below are the reference examples that the meta-prompts cite as few-shot anchors.
Do not write new algorithm-specific prompts by hand — use the meta-prompts instead.

---

## Part 1 — Weight Decay SGD

### Prompt 1A: Prover (Weight Decay SGD — Nonconvex + Strongly Convex)

**Files to @mention:** `docs/CONVENTIONS.md`, `docs/GLUE_TRICKS.md`, `docs/ALGORITHM_TEMPLATE.md`, `Algorithms/WeightDecaySGD.lean`, `Algorithms/SGD.lean`, `Lib/Layer1/StochasticDescent.lean`

```
You are a Lean 4 formal verification engineer working on the StochOptLib library.

## Your task
Complete the proofs for non-convex and strongly convex convergence in
`Algorithms/WeightDecaySGD.lean`.

## MANDATORY reading order — read ALL of these before writing any code
1. `docs/CONVENTIONS.md`         — critical design rules, especially Convention 1 and Convention 5
2. `docs/CATALOG.md`             — index of all existing lemmas; check before writing anything new
3. `docs/GLUE_TRICKS.md`         — proof patterns (Lipschitz composition, integral linearity, variance pitfall)
4. `docs/ALGORITHM_TEMPLATE.md`  — the exact bridge pattern used in this library (Section 2 and 5)
5. `Algorithms/WeightDecaySGD.lean` — the existing file; convex convergence is already proved

## What needs to be added
Add two new theorems to `WeightDecaySGDSetup` namespace:
1. `weight_decay_convergence_nonconvex_v2` — call `sgd_convergence_nonconvex_v2` via
   `simpa [WeightDecaySGDSetup.process] using (sgd_convergence_nonconvex_v2 ...)`
2. `weight_decay_convergence_strongly_convex_v2` — same pattern via `sgd_convergence_strongly_convex_v2`

## Key pattern (copy from the existing convex theorem)
The trick is `setup.effectiveSGDSetup` IS a plain `SGDSetup`, so you can pass it
directly to the Layer 2 SGD theorems. Use `simpa [WeightDecaySGDSetup.process]` to unfold
the process alias.

## Signature alignment — CRITICAL differences from the convex theorem

CAUTION: `sgd_convergence_nonconvex_v2` takes `hlower : ∀ w, f_star ≤ f w` instead of
`wStar`/`hconvex`, and its `h_int_inner` is `⟪effGradF(w_t), effGradL(w_t,ξ_t)⟫` —
NOT `⟪w_t - wStar, gradL⟫`. Copy its exact signature from Algorithms/SGD.lean line 114.

For strongly convex: `_hη_L : η ≤ 1 / (L : ℝ)` must be forwarded even though it has
an underscore prefix. There is no `hT` parameter (unlike convex and nonconvex).
The signature has `(T : ℕ)` without positivity.

## Variance hypothesis
`hvar : HasBoundedVariance setup.effGradL setup.sampleDist σ` — the caller provides this.
Do NOT attempt to derive it from `HasBoundedVariance` of the base `gradL`. See
`docs/CONVENTIONS.md` Convention 5 and `docs/GLUE_TRICKS.md` Section 5 for why.

## Integrability and measurability
Use `measurable_effGradL` (already proved in the file) for `hgL`.
Integrability hypotheses should be forwarded from the theorem signature, exactly as in
`sgd_convergence_convex_v2` in `Algorithms/SGD.lean`.

## Success criterion
`lake build Algorithms.WeightDecaySGD` exits 0 with no sorry warnings in the two new
theorems. The existing `weight_decay_convergence_convex_v2` must remain unchanged.
```

---

### Prompt 1B: Archivist (Weight Decay SGD)

**Files to @mention:** `Algorithms/WeightDecaySGD.lean`, `docs/CATALOG.md`, `docs/CONVENTIONS.md`, `docs/METHODOLOGY.md`

```
You are a documentation engineer for the StochOptLib library. The following Lean proofs
have just been completed and need to be catalogued.

## What was proved
In `Algorithms/WeightDecaySGD.lean`:
- `weight_decay_convergence_nonconvex_v2` — non-convex rate via effectiveSGDSetup
- `weight_decay_convergence_strongly_convex_v2` — strongly convex exponential contraction
- `weight_decay_convergence_convex_v2` — convex rate (already existed)

All three reduce Weight Decay SGD to plain SGD on the effective oracle
`effGradL(w,s) = gradL(w,s) + decay • w`, then call the Layer 2 SGD theorems directly.

## Tasks — documentation only, do NOT modify any Lean proof code

### Task 1: Update `docs/CATALOG.md`
Add a new section `## Algorithm Layer (Layer 2) — Algorithms/WeightDecaySGD.lean` following
the same format as the SGD section. Include:
- `WeightDecaySGDSetup` structure description
- `effectiveSGDSetup` — explain the "reframe as plain SGD" trick
- `measurable_effGradL`, `unbiased_effGrad_of_unbiased` — bridge lemmas
- All three convergence theorems with their call chains:
  `weight_decay_* → simpa → sgd_convergence_*_v2 → sgd_to_hyps → stochastic_descent_*`
- Update the `### Roadmap & Dependency Tree` table to include Weight Decay SGD rows.
  Add WD columns to existing rows (not new rows), since Weight Decay reuses the
  same Glue lemma pipeline as SGD via `effectiveSGDSetup`.

### Task 1b: Hit Report — Glue Usage Count
After writing the CATALOG entry, append a short "Hit Report" subsection:

| Component | File | Used by |
|---|---|---|
| (list each reused library component) | ... | ... |

Include leverage score: reused existing / (reused + new), raw ratio.

### Task 2: Add `Used in:` tags to bridge lemmas
Open `Algorithms/WeightDecaySGD.lean` and add `Used in:` docstring lines to:
- `measurable_effGradL`
- `unbiased_effGrad_of_unbiased`
(See `docs/CONVENTIONS.md` Convention 4 for the required format.)

### Task 3: Update `docs/METHODOLOGY.md` Roadmap
Add Phase 0b — Weight Decay SGD (complete) between Phase 0 (SGD) and Phase 1
(Projected GD). Include method note: "effective oracle reframe via effectiveSGDSetup".

### Task 4: Fix unused section variable warnings
In `Algorithms/WeightDecaySGD.lean`, add `omit [SecondCountableTopology E] in`
immediately before each of these three theorems:
- `process_zero`
- `process_succ`
- `unbiased_effGrad_of_unbiased`

IMPORTANT: `omit` must be placed BEFORE the docstring, not between the docstring
and `theorem`. Correct order:
  omit [SecondCountableTopology E] in
  /-- docstring ... -/
  theorem ...

## Style constraints
- All documentation in English
- LaTeX formulas use $...$ or $$...$$
- Do NOT change any Lean proof logic
```

---

## Part 2 — Projected GD

### Prompt 2A: Prover (Projected GD — Convex)

**Files to @mention:** `docs/CONVENTIONS.md`, `docs/GLUE_TRICKS.md`, `docs/ALGORITHM_TEMPLATE.md`, `Main.lean`, `Algorithms/SGD.lean`, `Lib/Layer1/StochasticDescent.lean`, `Lib/Glue/Algebra.lean`

```
You are a Lean 4 formal verification engineer working on the StochOptLib library.

## Your task
Create `Algorithms/ProjectedGD.lean` implementing stochastic projected gradient
descent convergence (convex case). Also add one new Glue lemma to `Lib/Glue/Algebra.lean`.

## MANDATORY reading order — read ALL before writing any code
1. `docs/CONVENTIONS.md`            — design rules (especially Convention 1, 2)
2. `docs/CATALOG.md`                — existing lemmas; check before writing anything new
3. `docs/GLUE_TRICKS.md`            — proof patterns
4. `docs/ALGORITHM_TEMPLATE.md`     — Section 1 (Archetype A vs B); PGD is Archetype B
5. `Main.lean`                      — `sgdProcess`, `sgdProcess_indepFun_xi` definitions
6. `Algorithms/SGD.lean`            — `sgd_to_hyps`, `sgd_convergence_convex_v2` as models
7. `Lib/Layer1/StochasticDescent.lean` — `stochastic_descent_convex'` signature

## Mathematical structure

Update rule: w_{t+1} = proj(w_t - η • gradL(w_t, ξ_t))
This is Archetype B — do NOT use simpa reduction to sgd_convergence_convex_v2.

Proof chain (convex case):
  ‖w_{t+1} − w*‖² = ‖proj(w_t − η•g_t) − proj(w*)‖²
                   ≤ ‖(w_t − η•g_t) − w*‖²       [projection non-expansiveness]
                   ≤ ‖w_t − w*‖² − 2η·gap + η²σ² [stochastic_descent_convex']

## MUST constraints (hard — do not deviate)

MUST 1: proj_nonexp_sq proof uses pow_le_pow_left₀, NOT sq_le_sq':
  calc ‖proj x - wStar‖^2
      = ‖proj x - proj wStar‖^2 := by
          exact congrArg (fun z => ‖proj x - z‖^2) hproj_wStar.symm
    _ ≤ ‖x - wStar‖^2 := pow_le_pow_left₀ (norm_nonneg _) (h x wStar) 2

MUST 2: pgd_convergence_convex_v2 has BOTH of these as SEPARATE hypotheses:
  h_int_norm_sq  : ∀ t, Integrable (fun ω => ‖process (t+1) ω - wStar‖^2) P
  h_int_virtual  : ∀ t, Integrable (fun ω => ‖(process t ω - η•g_t ω) - wStar‖^2) P
  Do NOT merge them. Both are needed for integral_mono.

MUST 3: hproj_meas : Measurable proj is a FIELD in ProjectedGDSetup, not a theorem param.

## Implementation steps

### Step 1: Add proj_nonexp_sq to Lib/Glue/Algebra.lean
Pure lemma: from h : ∀ x y, ‖proj x − proj y‖ ≤ ‖x − y‖ and hproj_wStar : proj wStar = wStar,
prove ‖proj x − wStar‖^2 ≤ ‖x − wStar‖^2. Use proof from MUST 1 above.
Add docstring with Gap classification (Level 2) and Used in: tag.

### Step 2: Define ProjectedGDSetup
Structure fields: toSGDSetup, proj, hproj_nonexp, hproj_meas (see MUST 3).
hproj_wStar goes in theorem signatures, NOT in the structure.

### Step 3: Define pgdProcess (recursive, same shape as sgdProcess but with proj wrapping)

### Step 4: pgdProcess_measurable, pgdProcess_adapted, pgdProcess_indepFun_xi
Copy from Main.lean's sgdProcess versions, replace sgdProcess with pgdProcess,
add hproj_meas argument in the induction step.
sgdFiltration from Main.lean is reused directly — no new filtration needed.

### Step 5: pgd_to_hyps (analogous to sgd_to_hyps)
wt := setup.process t, gradL/gradF from toSGDSetup, h_indep from pgdProcess_indepFun_xi.

### Step 6: pgd_convergence_convex_v2
One-step bound:
  h_proj_bound: integral_mono (h_int_norm_sq (t+1)) (h_int_virtual t) (proj_nonexp_sq ...)
  h_virtual: stochastic_descent_convex' (pgd_to_hyps ...) ...
  linarith [le_trans h_proj_bound h_virtual, hη t]
Then telescope (copy from sgd_convergence_convex_v2 verbatim).

## Variance hypothesis
hvar : HasBoundedVariance setup.toSGDSetup.gradL setup.sampleDist σ
Projection does NOT affect variance. No Convention 5 issue.

## Success criterion
lake env lean Algorithms/ProjectedGD.lean exits 0, no sorry in pgd_convergence_convex_v2.
Nonconvex and strongly convex can remain sorry for now.
```

---

### Prompt 2B: Archivist (Projected GD)

**Files to @mention:** `Algorithms/ProjectedGD.lean`, `Lib/Glue/Algebra.lean`, `docs/CATALOG.md`, `docs/CONVENTIONS.md`, `docs/METHODOLOGY.md`

```
You are a documentation engineer for the StochOptLib library.
The following Lean proofs have just been completed and need to be catalogued.

## What was proved

In `Algorithms/ProjectedGD.lean`:
- `pgd_convergence_convex_v2` — convex convergence via projection non-expansiveness
  + stochastic_descent_convex'

New Glue lemma in `Lib/Glue/Algebra.lean`:
- `proj_nonexp_sq` — if proj is non-expansive and proj(w*)=w*, then
  ‖proj(x) − w*‖² ≤ ‖x − w*‖²

Key design decisions to document:
- hproj_meas : Measurable proj is a FIELD in ProjectedGDSetup
- hproj_wStar : setup.proj wStar = wStar is a per-theorem hypothesis
- h_int_virtual is SEPARATE from h_int_norm_sq (Archetype B pattern)
- sgdFiltration from Main.lean is reused directly

## Tasks — documentation only, do NOT modify any Lean proof code

### Task 1: Add Layer-2 section in docs/CATALOG.md
Add ## Algorithm Layer (Layer 2) — Algorithms/ProjectedGD.lean after Weight Decay section.
Include: ProjectedGDSetup, pgdProcess, process infrastructure, pgd_to_hyps,
pgd_convergence_convex_v2 with call chain:

  pgd_convergence_convex_v2
    → proj_nonexp_sq + integral_mono        [projection bound: actual ≤ virtual step]
    → stochastic_descent_convex' (pgd_to_hyps setup t ...)
        → same Layer 0/Glue chain as SGD convex
    → le_trans h_proj_bound h_virtual
    → telescope (identical to sgd_convergence_convex_v2)

Hit Report: reused = 8, new = 5 (proj_nonexp_sq + pgd process infrastructure),
leverage = 8/13 ≈ 61.5%. Note: lower than WD (77.8%) because Archetype B requires
its own process infrastructure, unlike Archetype A which inherits SGD's process.

Add Archetype B note: h_int_virtual is a new hypothesis type absent in Archetype A.

### Task 2: Add proj_nonexp_sq entry in Glue/Algebra section
Gap: Level 2. Proof: fixed-point rewrite + pow_le_pow_left₀.
Used in: Projected GD (Step 1 — projection bound).

### Task 3: Update Roadmap dependency table
Add "PGD convex" column to existing table.
Add proj_nonexp_sq as a new row (Step 1 for PGD convex, — for all others).

### Task 4: Add Used in: tags in Lean source
In Algorithms/ProjectedGD.lean:
- pgd_to_hyps: "Used in: Projected GD (Algorithms/ProjectedGD.lean, bridge)"
- pgdProcess_indepFun_xi: "Used in: Projected GD (Algorithms/ProjectedGD.lean, pgd_to_hyps — independence)"

### Task 5: Update docs/METHODOLOGY.md
Add Phase 1 — Projected GD (complete). Mark Phase 2 — SVRG as next probe.

## Style constraints
- All documentation in English
- LaTeX formulas use $...$ or $$...$$
- Do NOT change any Lean proof logic
```

---

### Prompt 2C: Glue Tricks Update (Projected GD discoveries)

**Files to @mention:** `docs/GLUE_TRICKS.md`

```
You are a documentation engineer for the StochOptLib library.
Your sole task is to update docs/GLUE_TRICKS.md with two new patterns
discovered during the Projected GD formalization. Do NOT modify any other file.

## Context: what was discovered

During the proof of pgd_convergence_convex_v2 in Algorithms/ProjectedGD.lean,
two reusable proof patterns emerged that are NOT yet recorded in GLUE_TRICKS.md.

### Discovery 1: Lifting non-expansiveness to squared-norm bound

When a function proj is non-expansive (‖proj x − proj y‖ ≤ ‖x − y‖) and
wStar is a fixed point (proj wStar = wStar), the squared-norm bound follows by:

```lean
calc ‖proj x - wStar‖ ^ 2
    = ‖proj x - proj wStar‖ ^ 2 := by
        exact congrArg (fun z => ‖proj x - z‖ ^ 2) hproj_wStar.symm
  _ ≤ ‖x - wStar‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (h x wStar) 2
```

CAUTION: do NOT use sq_le_sq' — that lemma is for real absolute values, not norms.
The correct Mathlib lemma is pow_le_pow_left₀.

### Discovery 2: Virtual step integrability for Archetype B algorithms

Archetype A algorithms (e.g. Weight Decay SGD) reduce to a plain SGD process via
effectiveSGDSetup, so process(t+1) IS the virtual step — only one integrability
condition is needed.

Archetype B algorithms (e.g. Projected GD) have an extra operation wrapping the
gradient step: process(t+1) = op(process t - η•g_t). Because op is NOT the identity,
process(t+1) and (process t − η•g_t) are DIFFERENT objects. To apply integral_mono,
you need TWO separate integrability hypotheses:

  h_int_norm_sq  : ∀ t, Integrable (fun ω => ‖process (t+1) ω - wStar‖^2) P
                   (integrability of the ACTUAL step — after op)
  h_int_virtual  : ∀ t, Integrable (fun ω => ‖(process t ω - η•g_t ω) - wStar‖^2) P
                   (integrability of the VIRTUAL step — before op)

Then:
```lean
have h_op_bound :=
  integral_mono (h_int_norm_sq (t+1)) (h_int_virtual t)
    (fun ω => op_nonexp_sq ...)   -- pointwise bound from op non-expansiveness
```

Rule of thumb: if your algorithm has the form process(t+1) = op(virtual_step t),
always add h_int_virtual as a separate theorem hypothesis alongside h_int_norm_sq.
This pattern applies to any Archetype B algorithm: projection, truncation, clipping, etc.

## Task: update docs/GLUE_TRICKS.md

### Task A: add new proof pattern entry
In Section 3 (Standard Proof Patterns), add a new subsection after the existing
"Norm-Squared Expansion" pattern:

#### Pattern: Lifting Non-Expansive Bound to Squared Norm

with the Lean code template and the CAUTION about sq_le_sq' above.

### Task B: add new Archetype B section
After Section 4 (Effective Oracle Reframe, which describes Archetype A), add a
new parallel section:

#### Section 4b: Archetype B — Virtual Step Integrability

Explain: when the update has the form process(t+1) = op(virtual_step), always
provide h_int_virtual separately from h_int_norm_sq. Give the integral_mono
template. List which algorithms this applies to (Projected GD confirmed;
truncated GD, clipped SGD would follow the same pattern).

## Validation
After editing, confirm:
- Section 3 has the new "Lifting Non-Expansive Bound" subsection
- A new Section 4b exists between Sections 4 and 5
- No other files were modified
```

---

## Appendix: File @ Reference Cheatsheet

| Prompt | Must @ | Optional |
|---|---|---|
| Prover (Archetype A) | `CONVENTIONS.md`, `GLUE_TRICKS.md`, `ALGORITHM_TEMPLATE.md`, target `.lean`, `SGD.lean`, `StochasticDescent.lean` | `CATALOG.md` (long) |
| Prover (Archetype B) | same as above + `Main.lean` | `CATALOG.md` |
| Archivist | target `.lean`, `CATALOG.md`, `CONVENTIONS.md`, `METHODOLOGY.md`, `GLUE_TRICKS.md` | — |
| Glue Tricks Update | `GLUE_TRICKS.md` only | — |
| Meta-Prover Generator | `PROMPTS.md`, `CATALOG.md`, `ALGORITHM_TEMPLATE.md`, `CONVENTIONS.md`, `GLUE_TRICKS.md` | — |
| Meta-Archivist Generator | `PROMPTS.md`, `CATALOG.md`, `CONVENTIONS.md`, `GLUE_TRICKS.md`, completed `.lean` | — |

**Note**: the standalone "Glue Tricks Update" prompt (Prompt 2C) is now subsumed by Task 6
in every Archivist prompt generated by Meta-Prompt B. It is kept here as a standalone
fallback for retroactive updates to older algorithms.
