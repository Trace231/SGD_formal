---
name: Layer1 StochasticDescent
overview: Create `Lib/Layer1/StochasticDescent.lean` with the `StochasticDescentHyps` structure and one meta-theorem `stochastic_descent_nonconvex`. `Main.lean` is left with broken imports for now (Step 5 will fix it).
todos:
  - id: create-layer1-file
    content: Create Lib/Layer1/StochasticDescent.lean with StochasticDescentHyps + descent_lemma + stochastic_descent_nonconvex
    status: completed
  - id: build-layer1
    content: Run lake build Lib.Layer1.StochasticDescent and fix any errors
    status: completed
  - id: commit-layer1
    content: "Commit with message: feat: abstract Layer1 stochastic descent meta-theorems"
    status: completed
isProject: false
---

# Layer 1: StochasticDescent (Phase 1 of 3)

## What gets created

One new file: `[Lib/Layer1/StochasticDescent.lean](Lib/Layer1/StochasticDescent.lean)`

- `descent_lemma` (deterministic, Layer 0 by nature but placed here as a local stepping stone)
- `StochasticDescentHyps` structure
- `stochastic_descent_nonconvex` meta-theorem

`Main.lean` is intentionally left with stale `stochastic_descent_nonconvex` (SGDSetup version) for now — it still compiles since we are only **adding** a file.

## `StochasticDescentHyps` design

Captures the **one-step probabilistic setup** independent of any specific algorithm:

```lean
structure StochasticDescentHyps (E S Ω) [...] where
  P    : Measure Ω
  hP   : IsProbabilityMeasure P
  ν    : Measure S             -- sample distribution (= sampleDist in SGD)
  wt   : Ω → E                 -- current iterate as random variable
  ξt   : Ω → S                 -- current sample
  gradL : E → S → E            -- stochastic gradient oracle
  gradF : E → E                -- true gradient
  η    : ℝ                     -- step size (scalar, this step only)
  -- Probabilistic structure
  h_indep  : IndepFun wt ξt P
  h_dist   : Measure.map ξt P = ν
  -- Measurability
  h_wt_meas  : Measurable wt
  h_ξt_meas  : Measurable ξt
  hgL        : Measurable (Function.uncurry gradL)
  -- Oracle property (fixed for the algorithm)
  hunb : IsUnbiased gradL gradF ν
```

**Not** in the struct (remain as theorem params):

- `L : NNReal`, `σ : ℝ` — problem constants
- `hgrad`, `hsmooth`, `hvar` — function-space properties
- All `Integrable` hypotheses

## `stochastic_descent_nonconvex` signature

```lean
theorem stochastic_descent_nonconvex
    (hyps : StochasticDescentHyps E S Ω) (f : E → ℝ) {L : NNReal} {σ : ℝ}
    (hgrad : IsGradientOf f hyps.gradF)
    (hsmooth : IsLSmooth hyps.gradF L)
    (hvar : HasBoundedVariance hyps.gradL hyps.ν σ)
    (h_intL : ∀ w, Integrable (hyps.gradL w) hyps.ν)
    (h_int_ft  : Integrable (fun ω => f (hyps.wt ω)) hyps.P)
    (h_int_ft1 : Integrable (fun ω => f (hyps.wt ω - hyps.η • hyps.gradL (hyps.wt ω) (hyps.ξt ω))) hyps.P)
    (h_int_inner : Integrable (fun ω => ⟪hyps.gradF (hyps.wt ω), hyps.gradL (hyps.wt ω) (hyps.ξt ω)⟫_ℝ) hyps.P)
    (h_int_sq : Integrable (fun ω => ‖hyps.gradL (hyps.wt ω) (hyps.ξt ω)‖ ^ 2) hyps.P) :
    ∫ ω, f (hyps.wt ω - hyps.η • hyps.gradL (hyps.wt ω) (hyps.ξt ω)) ∂hyps.P ≤
      ∫ ω, f (hyps.wt ω) ∂hyps.P
      - hyps.η * ∫ ω, ‖hyps.gradF (hyps.wt ω)‖ ^ 2 ∂hyps.P
      + hyps.η ^ 2 * (L : ℝ) * σ ^ 2 / 2
```

**Key simplifications vs. SGD version**:

- No `SGDSetup`, no `t : ℕ`, no `hη : setup.η t = η`
- No `sgdProcess_indepFun_xi` call — independence is `hyps.h_indep` directly
- No `h_step_eq` rewriting — statement uses `hyps.wt ω - hyps.η • ...` directly
- `sgdProcess_measurable ... t` → `hyps.h_wt_meas` (one field)
- `setup.hξ_meas t` → `hyps.h_ξt_meas` (one field)
- Drops the unused `h_int_gF_sq` parameter

## Proof adaptation

The proof body is essentially the same 5-step structure from `Main.lean` (lines 351–426), with:

- `set wt := hyps.wt`, `set gt := fun ω => hyps.gradL (hyps.wt ω) (hyps.ξt ω)`
- `haveI := hyps.hP`
- `h_dist_t` and `h_indep_t` are `hyps.h_dist` / `hyps.h_indep` directly
- `h_step_eq` disappears (statement is already in the right form)
- `sgdProcess_measurable setup.hξ_meas hgL t` → `hyps.h_wt_meas`

## Verification

```bash
lake build Lib.Layer1.StochasticDescent
```

`Main.lean` continues to compile (we are not modifying it this step).

## Docstring labels

```
Layer: 1 | Gap: Level 2 (composition of Layer 0 lemmas + independence structure)
```

