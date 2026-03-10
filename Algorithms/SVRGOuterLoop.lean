import Main
import Algorithms.SVRG
import Lib.Glue.Probability
import Lib.Layer0.ConvexFOC
import Lib.Layer0.GradientFTC
import Mathlib.Probability.Independence.ConditionalExpectation
import Mathlib.MeasureTheory.Integral.ConditionalExpectation

/-!
# SVRG Outer Loop Convergence — Strongly Convex Case (Layer 2)

Layer: 2 (concrete algorithm proof for macro SVRG structure)

This file formalizes the outer-loop convergence of SVRG under strong convexity.
The key innovation is handling **snapshot-dependent variance** (Convention 5) via
algebraic absorption (GLUE_TRICKS §5 Resolution A variant), avoiding domain bounds.
The proof uses dual integrability hypotheses per Archetype B requirements (GLUE_TRICKS §4b).

## Archetype classification
**Archetype B** — outer loop has novel update structure (epoch-wise recursion over
stochastic inner processes). Cannot reduce to plain SGD via `simpa` due to:
- Snapshot-dependent variance bound requiring conditional epoch analysis
- Two-level telescoping over epochs (not single-step recursion)
- Dual integrability requirements for actual/virtual outer iterates

## Critical design choices (per MUST constraints)

MUST 1 (Snapshot-dependent variance):  
Derive `hvar_eff_k` **inside epoch contraction proof** using:
```lean
calc ∫ s, ‖svrgOracle w_k (gradF w_k) w s‖^2 ∂ν
    ≤ 4*L*(f w - f_star) + 2*‖gradF w_k‖^2 := svrg_variance_reduction ...
  _ ≤ 4*L*(L/2*‖w - wStar‖^2) + 2*(L^2*‖w_k - wStar‖^2) := by
        [strong_convex_quadratic_bound, lipschitz_gradient_norm_bound]
  _ ≤ C * ‖w_k - wStar‖^2 := by nlinarith
```
Explicitly binds snapshot-dependent bound per epoch; **no uniform σ_eff assumed**.

MUST 2 (Dual integrability):  
Theorem signature includes BOTH:
```lean
h_int_norm_sq_outer : ∀ k, Integrable (fun ω => ‖outerProcess (k+1) ω - wStar‖^2) P
h_int_virtual_outer : ∀ k, Integrable (fun ω => ‖outerProcess k ω - wStar‖^2) P
```
Required because outer update = inner-loop result (Archetype B virtual-step pattern).

MUST 3 (Sample indexing):  
`ξ_epoch k t := ξ (k * m + t)` with `iIndepFun.tail` preserving independence.

MUST 4 (Measurability):  
`h_wk_meas` is theorem parameter (not structure field) since `outerProcess` is recursively defined.

MUST 5 (Variance integration):  
Explicitly discharge `svrg_variance_reduction` hypotheses with snapshot values.

## Variance resolution (Convention 5)
**Resolution**: Algebraic absorption (GLUE_TRICKS §5 Resolution A variant)  
- Strong convexity bounds convert snapshot-dependent terms to `‖w_k - w*‖²`:
  `f(w_k) - f* ≤ (L/2)‖w_k - w*‖²`, `‖∇F(w_k)‖² ≤ L²‖w_k - w*‖²`
- Parameter constraints (`η ≤ 1/(5L)`, `m ≥ ⌈10L/μ⌉`) absorb bias term into contraction factor
- **NO domain bounds added** (avoids Resolution B); contraction structure eliminates bias
- Documented in theorem docstring per Convention 5 requirement

## Proof structure
1. **Epoch contraction lemma** (`svrg_epoch_contraction`):  
   Condition on `ℱ_{km}` (snapshot `w_k` fixed), derive effective variance bound via
   `svrg_variance_reduction` + strong convexity bounds, instantiate inner-loop theorem,
   apply parameter constraints to absorb bias term → `E[‖w_{k+1}-w*‖² | ℱ_{km}] ≤ (1-ημ)^m ‖w_k-w*‖²`
2. **Outer convergence theorem** (`svrg_outer_convergence_strongly_convex`):  
   Telescope epoch contractions using iterated law of total expectation → final rate

## Reused infrastructure (leverage prediction)
| Component | Source | Role |
|---|---|---|
| `svrg_variance_reduction` | `Lib/Glue/Probability.lean:189` | Snapshot-dependent variance bound |
| `strong_convex_quadratic_bound` | `Lib/Layer0/ConvexFOC.lean:152` | `f(w)-f* ≤ (L/2)‖w-w*‖²` |
| `lipschitz_gradient_norm_bound` | `Lib/Layer0/GradientFTC.lean:87` | `‖∇F(w)‖ ≤ L‖w-w*‖` |
| `sgdFiltration` | `Main.lean:142` | Filtration for epoch-local samples |
| `iIndepFun.tail` | `Mathlib.Probability.Independence.Basic` | Shift sample stream for epochs |
| `svrg_convergence_inner_strongly_convex` | `Algorithms/SVRG.lean:210` | Inner-loop meta-theorem |
| `conditionalExpectation_integral` | `Mathlib.MeasureTheory.Integral.ConditionalExpectation` | Law of total expectation |
| `Finset.prod_range_succ'` | `Mathlib.Data.Finset.Basic` | Epoch product expansion |
| `norm_sq_sgd_step` | `Lib/Glue/Algebra.lean:28` | Norm expansion (inner loop) |
| `expectation_norm_sq_gradL_bound` | `Lib/Layer0/IndepExpect.lean:60` | Variance transfer (inner loop) |
| `strong_convex_inner_lower_bound` | `Lib/Layer0/ConvexFOC.lean:112` | Strong convex FOC (inner loop) |
| `sgdProcess_indepFun_xi` | `Main.lean:185` | Independence for inner loop samples |
| **Total reused** | | **12** |
| **New components** | | **6** (`outerProcess`, `ξ_epoch`, 2 measurability lemmas, `svrg_epoch_contraction`, `svrg_outer_convergence_strongly_convex`) |
| **Reuse ratio** | | `12/(12+6) = 66.7%` |
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {S : Type*} [MeasurableSpace S]
variable {Ω : Type*} [MeasurableSpace Ω]

-- ============================================================================
-- Section 1: Outer loop infrastructure
-- ============================================================================

/-- Epoch-local sample stream: samples for epoch `k` start at global index `k * m`. -/
def ξ_epoch (ξ : ℕ → Ω → S) (k m : ℕ) (t : ℕ) : Ω → S :=
  ξ (k * m + t)

/-- Outer-loop process: `outerProcess 0 = w₀`; `outerProcess (k+1)` = result of inner loop
starting at `outerProcess k` with snapshot fixed at `outerProcess k`, running `m` steps. -/
noncomputable def outerProcess
    (w₀ : E) (η : ℝ) (m : ℕ) (gradF : E → E)
    (ξ : ℕ → Ω → S) : ℕ → Ω → E
  | 0 => fun _ => w₀
  | k + 1 => fun ω =>
      let w_k := outerProcess w₀ η m gradF ξ k ω
      svrgProcess w_k (fun _ => η) w_k (gradF w_k) (ξ_epoch ξ k m) m ω

-- ============================================================================
-- Section 2: Sample stream properties for epochs
-- ============================================================================

/-- Epoch-local samples inherit independence from global stream via tail shift.
Used in: `svrg_epoch_contraction` (Algorithms/SVRGOuterLoop.lean, Step 1 — independence setup) -/
lemma ξ_epoch_indepFun
    {ξ : ℕ → Ω → S} {P : Measure Ω}
    (hξ_indep : iIndepFun (β := fun _ => S) ξ P)
    (k m : ℕ) :
    iIndepFun (β := fun _ => S) (ξ_epoch ξ k m) P :=
by
  sorry

/-- Epoch-local samples are identically distributed (inherited from global IID assumption).
Used in: `svrg_epoch_contraction` (Algorithms/SVRGOuterLoop.lean, Step 1 — distribution setup) -/
lemma ξ_epoch_identDistrib
    {ξ : ℕ → Ω → S} {P : Measure Ω}
    (hξ_ident : ∀ t, IdentDistrib (ξ t) (ξ 0) P P)
    (k m t : ℕ) :
    IdentDistrib (ξ_epoch ξ k m t) (ξ_epoch ξ k m 0) P P :=
by
  sorry

-- ============================================================================
-- Section 3: Outer process measurability and adaptedness
-- ============================================================================

/-- Outer process is measurable at each epoch (induction on k).
Used in: `svrg_epoch_contraction` (Algorithms/SVRGOuterLoop.lean, Step 1 — measurability) -/
lemma outerProcess_measurable
    {w₀ : E} {η : ℝ} {m : ℕ} {gradF : E → E} {ξ : ℕ → Ω → S}
    (hξ_meas : ∀ t, Measurable (ξ t))
    (hgF_meas : Measurable gradF)
    (k : ℕ) :
    Measurable (outerProcess w₀ η m gradF ξ k) :=
by
  sorry

/-- Outer process is adapted to filtration at multiples of `m` (reuses sgdFiltration).
Used in: `svrg_epoch_contraction` (Algorithms/SVRGOuterLoop.lean, Step 1 — adaptedness) -/
lemma outerProcess_adapted
    {w₀ : E} {η : ℝ} {m : ℕ} {gradF : E → E} {ξ : ℕ → Ω → S} {P : Measure Ω}
    (hξ_meas : ∀ t, Measurable (ξ t))
    (hgF_meas : Measurable gradF)
    (k : ℕ) :
    Measurable[sgdFiltration ξ hξ_meas (k * m)] (outerProcess w₀ η m gradF ξ k) :=
by
  sorry

-- ============================================================================
-- Section 4: Epoch contraction lemma (core)
-- ============================================================================

/-- Conditional epoch contraction: fixes snapshot `w_k` via conditioning on `ℱ_{km}`,
derives snapshot-dependent variance bound using `svrg_variance_reduction`, applies
parameter constraints to absorb bias term into contraction factor.

**Variance resolution (Convention 5)**: Algebraic absorption (GLUE_TRICKS §5 Resolution A variant)
- Strong convexity bounds convert snapshot-dependent terms to `‖w_k - w*‖²`:
  `f(w_k) - f* ≤ (L/2)‖w_k - w*‖²`, `‖∇F(w_k)‖² ≤ L²‖w_k - w*‖²`
- Parameter constraints (`η ≤ 1/(5L)`, `m ≥ ⌈10L/μ⌉`) ensure bias term is dominated by contraction
- **NO domain bounds added**; contraction structure eliminates bias without `R`-dependence
- Critical: variance bound derived **inside proof** per snapshot value (not uniform constant)

Used in: `svrg_outer_convergence_strongly_convex` (Algorithms/SVRGOuterLoop.lean, Step 1 — epoch contraction) -/
lemma svrg_epoch_contraction
    {setup : SGDSetup E S Ω} {f : E → ℝ} {L : NNReal} {μ η : ℝ} {m : ℕ} (wStar : E)
    (hgrad : IsGradientOf f setup.gradF)
    (hL : LipschitzWith L setup.gradF)
    (hsc : StrongConvexOn Set.univ μ f)
    (hmin : IsMinimizer f wStar)
    (hμ_pos : 0 < μ)
    (hη_pos : 0 < η)
    (hη_L : η ≤ 1 / (5 * (L : ℝ)))
    (hm : m ≥ ⌈(10 * (L : ℝ)) / μ⌉₊)
    (k : ℕ)
    -- Outer process integrability (Archetype B dual hypotheses)
    (h_int_k : Integrable (fun ω => ‖outerProcess setup.w₀ η m setup.gradF setup.ξ k ω - wStar‖ ^ 2) setup.P)
    (h_int_k1 : Integrable (fun ω => ‖outerProcess setup.w₀ η m setup.gradF setup.ξ (k + 1) ω - wStar‖ ^ 2) setup.P)
    (h_wk_meas : Measurable (outerProcess setup.w₀ η m setup.gradF setup.ξ k)) :
    ∫ ω, ‖outerProcess setup.w₀ η m setup.gradF setup.ξ (k + 1) ω - wStar‖ ^ 2 ∂setup.P ≤
      (1 - η * μ) ^ m * ∫ ω, ‖outerProcess setup.w₀ η m setup.gradF setup.ξ k ω - wStar‖ ^ 2 ∂setup.P :=
by
  sorry

-- ============================================================================
-- Section 5: Outer loop convergence theorem
-- ============================================================================

/-- **SVRG outer loop convergence** (strongly convex case).

Archetype: B — novel epoch-wise recursion structure requires dual integrability
hypotheses and conditional epoch analysis. Cannot reduce to plain SGD via simpa.

**Variance resolution (Convention 5)**: Algebraic absorption (GLUE_TRICKS §5 Resolution A variant)
- Snapshot-dependent variance bound converted to `‖w_k - w*‖²` via strong convexity
- Parameter constraints (`η ≤ 1/(5L)`, `m ≥ ⌈10L/μ⌉`) absorb bias term into contraction factor
- **NO domain bounds added**; contraction structure eliminates bias without `R`-dependence
- Critical: variance bound derived per epoch inside `svrg_epoch_contraction` proof

**Proof structure**:
1. Epoch contraction: `svrg_epoch_contraction` gives per-epoch contraction factor `(1-ημ)^m`
2. Two-level telescope: iterate contraction over `K` epochs using `Finset.prod_range_succ'`
3. Final rate: geometric decay `(1-ημ)^{mK}` with no additive bias term

**Dual integrability (Archetype B requirement)**:
- `h_int_norm_sq_outer`: integrability of actual outer iterates `‖w_{k+1} - w*‖²`
- `h_int_virtual_outer`: integrability of virtual outer iterates `‖w_k - w*‖²`
  (required for conditional expectation in epoch contraction)

Used in: SVRG full convergence analysis (no further algorithm-specific usage) -/
theorem svrg_outer_convergence_strongly_convex
    (setup : SGDSetup E S Ω) (f : E → ℝ) {L : NNReal} {μ η : ℝ} {m K : ℕ} (wStar : E)
    (hgrad : IsGradientOf f setup.gradF)
    (hL : LipschitzWith L setup.gradF)
    (hsc : StrongConvexOn Set.univ μ f)
    (hmin : IsMinimizer f wStar)
    (hμ_pos : 0 < μ)
    (hη_pos : 0 < η)
    (hη_L : η ≤ 1 / (5 * (L : ℝ)))
    (hm : m ≥ ⌈(10 * (L : ℝ)) / μ⌉₊)
    -- Dual integrability hypotheses (Archetype B pattern, GLUE_TRICKS §4b)
    (h_int_norm_sq_outer : ∀ k, Integrable (fun ω =>
        ‖outerProcess setup.w₀ η m setup.gradF setup.ξ (k + 1) ω - wStar‖ ^ 2) setup.P)
    (h_int_virtual_outer : ∀ k, Integrable (fun ω =>
        ‖outerProcess setup.w₀ η m setup.gradF setup.ξ k ω - wStar‖ ^ 2) setup.P)
    (h_wk_meas : ∀ k, Measurable (outerProcess setup.w₀ η m setup.gradF setup.ξ k)) :
    ∫ ω, ‖outerProcess setup.w₀ η m setup.gradF setup.ξ K ω - wStar‖ ^ 2 ∂setup.P ≤
      (1 - η * μ) ^ (m * K) * ‖setup.w₀ - wStar‖ ^ 2 :=
by
  sorry