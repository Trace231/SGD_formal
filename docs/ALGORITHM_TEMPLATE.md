# Algorithm Template — Adding a New Algorithm to StochOptLib

This document is **library-specific**. It describes how to structure a new
algorithm proof within THIS library's Layer 0 / Layer 1 / Layer 2 architecture.

For universal proof techniques (how to discharge individual obligations), see
[`docs/GLUE_TRICKS.md`](GLUE_TRICKS.md).

---

## Section 1 — Two Algorithm Archetypes

Before writing any code, classify your algorithm:

### Archetype A: Oracle Variant

**Definition**: The update has the standard form `w_{t+1} = w_t - η · g(w_t, ξ_t)`,
but the oracle `g` is different from plain SGD.

**Examples**: Weight Decay SGD, L2-regularized SGD, gradient clipping SGD.

**Strategy**: Define the effective oracle and effective true gradient, then wrap
the base `SGDSetup` into a new `SGDSetup` with those effective functions. All
Layer 1 meta-theorems and Layer 2 SGD convergence theorems apply directly.

**Key file to look at**: `Algorithms/WeightDecaySGD.lean` (the worked example).

---

### Archetype B: Novel Update Structure

**Definition**: The update does NOT have the form `w_{t+1} = w_t - η · g(w_t, ξ_t)`.

**Examples**: Adam (adaptive per-coordinate learning rate + momentum), SVRG
(periodic full gradient), Nesterov accelerated SGD (momentum term).

**Strategy**: This archetype requires new work. You may need to:
- Define a new abstract structure analogous to `StochasticDescentHyps`
- Extend `StochasticDescentHyps` with additional fields
- Or prove the meta-theorem from scratch for the specific update form

**Status**: Not yet documented with a worked example. See `docs/METHODOLOGY.md`
Roadmap for planned probes.

---

## Section 2 — Archetype A Playbook

The following is the standard recipe for an oracle-variant algorithm. All steps
correspond directly to code in `Algorithms/WeightDecaySGD.lean`.

### Step 1: Inherit from `SGDSetup`

Define a new structure that CONTAINS (not extends) an `SGDSetup`, plus any
algorithm-specific parameters:

```lean
structure FooSetup
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E]
    (S : Type*) [MeasurableSpace S]
    (Ω : Type*) [MeasurableSpace Ω] where
  toSGDSetup : SGDSetup E S Ω
  -- algorithm-specific parameters:
  param : ℝ
```

Note: use `toSGDSetup : SGDSetup E S Ω` (containment) rather than `extends`,
so that you can override `gradL`/`gradF` without re-proving every SGD field.

### Step 2: Define the Effective Oracle and Gradient

```lean
namespace FooSetup

variable (setup : FooSetup E S Ω)

/-- Effective stochastic oracle: base oracle + deterministic correction. -/
def effGradL (w : E) (s : S) : E :=
  setup.toSGDSetup.gradL w s + setup.param • w  -- example: weight decay

/-- Effective true gradient: base gradient + correction. -/
def effGradF (w : E) : E :=
  setup.toSGDSetup.gradF w + setup.param • w
```

### Step 3: Build the `effectiveSGDSetup`

This is the key step: package the effective oracle into a plain `SGDSetup`.
All fields EXCEPT `gradL` and `gradF` are copied from the base setup.

```lean
/-- Reframe FooAlgorithm as plain SGD on the effective oracle. -/
noncomputable def effectiveSGDSetup : SGDSetup E S Ω where
  w₀      := setup.toSGDSetup.w₀
  η       := setup.toSGDSetup.η
  gradL   := setup.effGradL          -- ← NEW
  gradF   := setup.effGradF          -- ← NEW
  ξ       := setup.toSGDSetup.ξ
  P       := setup.toSGDSetup.P
  hP      := setup.toSGDSetup.hP
  hξ_meas  := setup.toSGDSetup.hξ_meas
  hξ_indep := setup.toSGDSetup.hξ_indep
  hξ_ident := setup.toSGDSetup.hξ_ident

/-- Convenience alias: the algorithm's iterates ARE the effective SGD iterates. -/
noncomputable def process : ℕ → Ω → E :=
  setup.effectiveSGDSetup.process
```

### Step 4: Prove Bridge Lemmas

Three lemmas are required to use the effective oracle. Refer to
`docs/GLUE_TRICKS.md` for the proof patterns.

**Bridge Lemma 1 — Measurability of effective oracle** (Pattern C in GLUE_TRICKS):

```lean
theorem measurable_effGradL
    (hgL : Measurable (Function.uncurry setup.toSGDSetup.gradL)) :
    Measurable (Function.uncurry setup.effGradL) := by
  -- For the additive case gradL + param • w:
  simpa [FooSetup.effGradL, Function.uncurry] using
    hgL.add (measurable_fst.const_smul setup.param)
```

**Bridge Lemma 2 — Unbiasedness of effective oracle** (Pattern B in GLUE_TRICKS):

```lean
theorem unbiased_effGrad_of_unbiased
    (hunb   : IsUnbiased setup.toSGDSetup.gradL setup.toSGDSetup.gradF setup.sampleDist)
    (hprob  : IsProbabilityMeasure setup.sampleDist)
    (h_intL : ∀ w, Integrable (setup.toSGDSetup.gradL w) setup.sampleDist) :
    IsUnbiased setup.effGradL setup.effGradF setup.sampleDist := by
  intro w
  simp [FooSetup.effGradL, integral_add (h_intL w) (integrable_const _),
        hunb w, integral_const, probReal_univ, FooSetup.effGradF]
```

**Bridge Lemma 3 — Variance bound** (see GLUE_TRICKS.md Section 5):

This is the only lemma with nontrivial new content. The correct approach depends
on the nature of the correction term. For weight decay:
- Use Resolution A (absorb the regularizer into the gradient structure)
- The effective oracle satisfies `HasBoundedVariance'` with the SAME constant `σ`
  relative to the base variance, because the `λw` term is absorbed into `gradF`

```lean
-- For weight decay: the convergence theorem takes hvar directly on effGradL
-- as a hypothesis, and the caller must supply it. Document the required form:
-- hvar : HasBoundedVariance setup.effGradL setup.sampleDist σ
-- The caller's responsibility is to ensure σ² accounts for the effective oracle.
```

### Step 5: Call the Layer 2 SGD Theorems Directly

Since `effectiveSGDSetup` IS a `SGDSetup`, you can call the SGD convergence
theorems directly via `simpa`:

```lean
theorem foo_convergence_convex_v2
    (f : E → ℝ) {L : NNReal} {σ η : ℝ} (wStar : E)
    (hgrad : IsGradientOf f setup.effGradF)
    (hsmooth : IsLSmooth setup.effGradF L)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hvar : HasBoundedVariance setup.effGradL setup.sampleDist σ)
    (hunb : IsUnbiased setup.effGradL setup.effGradF setup.sampleDist)
    -- ... remaining integrability hypotheses ... :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T,
        (∫ ω, f (setup.process t ω) ∂setup.effectiveSGDSetup.P - f wStar) ≤
      ‖setup.effectiveSGDSetup.w₀ - wStar‖ ^ 2 / (2 * η * T) + η * σ ^ 2 / 2 := by
  simpa [FooSetup.process] using
    sgd_convergence_convex_v2
      (setup := setup.effectiveSGDSetup) (f := f) (wStar := wStar)
      hgrad hsmooth hconvex hvar hunb hmin hη_pos hη T hT
      hgL h_intL h_int_f h_int_sq h_int_norm_sq h_int_inner h_int_gF_inner
```

The `simpa [FooSetup.process]` unfolds the `process` alias and connects the
algorithm-specific statement to the general SGD statement.

---

## Section 3 — `StochasticDescentHyps` Field Reuse Map

When calling `sgd_to_hyps` (or the Layer 1 meta-theorems directly), here is
which fields come from where. For Archetype A, you call `sgd_to_hyps` on the
`effectiveSGDSetup`, so the mapping is:

| `StochasticDescentHyps` field | Source in Archetype A | Comment |
|---|---|---|
| `P` | `setup.toSGDSetup.P` | Probability space unchanged |
| `hP` | `setup.toSGDSetup.hP` | Unchanged |
| `ν` | `setup.effectiveSGDSetup.sampleDist` | Same IID distribution |
| `wt` | `setup.process t` | Same iterate (effective SGD = same recurrence) |
| `ξt` | `setup.toSGDSetup.ξ t` | Same IID samples |
| `gradL` | `setup.effGradL` | **NEW** — effective oracle |
| `gradF` | `setup.effGradF` | **NEW** — effective true gradient |
| `η` | `setup.toSGDSetup.η t` | Same step size schedule |
| `h_indep` | `sgdProcess_indepFun_xi … hgL_eff t` | Uses `measurable_effGradL` result |
| `h_dist` | `(setup.toSGDSetup.hξ_ident t).map_eq` | Unchanged distribution |
| `h_wt_meas` | `sgdProcess_measurable … hgL_eff t` | Uses `measurable_effGradL` result |
| `h_ξt_meas` | `setup.toSGDSetup.hξ_meas t` | Unchanged |
| `hgL` | `measurable_effGradL hgL` | Bridge Lemma 1 result |
| `hgF_meas` | `measurable_effGradF hgF_meas` | Analogous to Bridge Lemma 1 |
| `hunb` | `unbiased_effGrad_of_unbiased …` | Bridge Lemma 2 result |

**Important**: `h_indep` and `h_wt_meas` use the NEW `hgL_eff := measurable_effGradL hgL`
(not the original `hgL`), because `sgdProcess_indepFun_xi` and `sgdProcess_measurable`
take the joint measurability of the oracle as a parameter.

---

## Section 4 — Weight Decay SGD: Annotated Walkthrough

`Algorithms/WeightDecaySGD.lean` implements exactly the pattern above. Here is
an annotated map of the file:

```
WeightDecaySGDSetup                        -- Step 1: structure with toSGDSetup + decay
  .effGradL                                -- Step 2: effective oracle = gradL + decay • w
  .effGradF                                -- Step 2: effective gradient = gradF + decay • w
  .effectiveSGDSetup                       -- Step 3: plain SGDSetup with effective functions
  .process                                 -- Step 3: alias for effectiveSGDSetup.process
  .measurable_effGradL                     -- Step 4, Bridge Lemma 1
  .measurable_effGradF                     -- Step 4, measurability of gradF
  .unbiased_effGrad_of_unbiased            -- Step 4, Bridge Lemma 2
  .wd_sgd_to_hyps                          -- calls sgd_to_hyps on effectiveSGDSetup
  .weight_decay_one_step_convex            -- one-step result (calls stochastic_descent_convex')
  .weight_decay_convergence_convex_v2      -- Step 5: delegates to sgd_convergence_convex_v2
```

**Variance bridge note**: `WeightDecaySGD.lean` takes `hvar : HasBoundedVariance setup.effGradL …`
as an explicit hypothesis. The caller supplies this. The mathematical justification
(using Resolution A from GLUE_TRICKS.md Section 5) is that the convergence rate
is stated in terms of the effective objective $f_\lambda$, so the $\lambda w$ term
appears on both sides of the descent inequality and does not inflate the variance
constant.

---

## Section 5 — Checklist for Adding a New Archetype A Algorithm

```
[ ] 1. Define FooSetup containing toSGDSetup
[ ] 2. Define effGradL and effGradF (the effective oracle and gradient)
[ ] 3. Build effectiveSGDSetup : SGDSetup from toSGDSetup with effGradL/effGradF
[ ] 4. Prove measurable_effGradL  (Bridge Lemma 1 — Pattern C in GLUE_TRICKS)
[ ] 5. Prove measurable_effGradF
[ ] 6. Prove unbiased_effGrad_of_unbiased  (Bridge Lemma 2 — Pattern B in GLUE_TRICKS)
[ ] 7. Address variance bound:
       - If correction = gradient of regularizer → use Resolution A (GLUE_TRICKS §5)
       - If correction is bounded → use Resolution B
       - Document which resolution you used in the docstring
[ ] 8. Define process alias and process_succ simp lemma
[ ] 9. Call sgd_convergence_* via simpa [FooSetup.process]
[10. ] Update docs/CATALOG.md: add FooSetup and bridge lemmas, update Roadmap table
[11. ] Add Used in: tag to each new lemma's docstring (CONVENTIONS.md §4)
```
