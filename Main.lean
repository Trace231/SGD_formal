import Mathlib.Analysis.InnerProductSpace.Basic
import Lib.Layer0.GradientFTC
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Data.NNReal.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Strong
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lib.Layer0.IndepExpect
import Lib.Layer0.ConvexFOC


open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

/-!
# Stochastic Gradient Descent — Algorithm Formalization

We formalize SGD as a discrete-time stochastic process on a real Hilbert space `E`,
with IID sampling from a sample space `S`. Convergence analysis is not addressed here.

## Main definitions

* `sgdProcess` — The SGD iteration as a random process `ℕ → Ω → E`
* `SGDSetup` — Packages all data and IID assumptions
* `sgdFiltration` — The natural filtration `ℱ_t = σ(ξ₀, …, ξ_{t−1})`
* `IsUnbiased`, `HasBoundedVariance`, `IsLSmooth` — Standard assumptions
-/

-- ============================================================================
-- Section 1 : Space Setup
-- ============================================================================

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

variable {S : Type*} [MeasurableSpace S]

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

-- ============================================================================
-- Section 2 : SGD Process Definition
-- ============================================================================

/-- The SGD iteration as a stochastic process.

* `w₀`    : initial parameter
* `η t`   : learning rate at step `t`
* `gradL` : stochastic gradient (deterministic in `(w, s)`)
* `ξ t`   : random sample drawn at step `t`

Returns `ℕ → Ω → E` where each `sgdProcess … t` is a random variable. -/
noncomputable def sgdProcess (w₀ : E) (η : ℕ → ℝ)
    (gradL : E → S → E) (ξ : ℕ → Ω → S) : ℕ → Ω → E
  | 0 => fun _ => w₀
  | t + 1 => fun ω =>
      let w_t := sgdProcess w₀ η gradL ξ t ω
      w_t - (η t) • gradL w_t (ξ t ω)

-- ============================================================================
-- Section 3 : SGD Setup (data + IID assumptions)
-- ============================================================================

/-- Complete SGD setup: initial point, learning rate schedule,
stochastic gradient oracle, true gradient, and IID random samples. -/
structure SGDSetup
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E]
    (S : Type*) [MeasurableSpace S]
    (Ω : Type*) [MeasurableSpace Ω] where
  w₀ : E
  η : ℕ → ℝ
  gradL : E → S → E
  gradF : E → E
  ξ : ℕ → Ω → S
  P : Measure Ω
  hP : IsProbabilityMeasure P
  hξ_meas : ∀ t, Measurable (ξ t)
  hξ_indep : iIndepFun (β := fun _ => S) ξ P
  hξ_ident : ∀ t, IdentDistrib (ξ t) (ξ 0) P P

namespace SGDSetup

variable (setup : SGDSetup E S Ω)

/-- The common distribution of each `ξ t` (pushforward of `P` through `ξ 0`). -/
noncomputable def sampleDist : Measure S :=
  Measure.map (setup.ξ 0) setup.P

/-- The SGD random process derived from the setup. -/
noncomputable def process : ℕ → Ω → E :=
  sgdProcess setup.w₀ setup.η setup.gradL setup.ξ

omit [SecondCountableTopology E] in
@[simp]
theorem process_zero : setup.process 0 = fun _ => setup.w₀ := rfl

omit [SecondCountableTopology E] in
@[simp]
theorem process_succ (t : ℕ) :
    setup.process (t + 1) = fun ω =>
      setup.process t ω - (setup.η t) • setup.gradL (setup.process t ω) (setup.ξ t ω) :=
  rfl

end SGDSetup

-- ============================================================================
-- Section 4 : Measurability
-- ============================================================================

omit [CompleteSpace E] in
/-- Each `sgdProcess … t` is a measurable function (i.e. a random variable).
Requires `gradL` to be jointly measurable and each `ξ t` to be measurable. -/
theorem sgdProcess_measurable {w₀ : E} {η : ℕ → ℝ}
    {gradL : E → S → E} {ξ : ℕ → Ω → S}
    (hξ : ∀ t, Measurable (ξ t))
    (hg : Measurable (Function.uncurry gradL))
    (t : ℕ) : Measurable (sgdProcess w₀ η gradL ξ t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      simp only [sgdProcess]
      exact ih.sub ((hg.comp (ih.prodMk (hξ t))).const_smul _)

-- ============================================================================
-- Section 5 : Natural Filtration and Adaptedness
-- ============================================================================

/-- The natural filtration for SGD:  `ℱ_t = σ(ξ₀, …, ξ_{t−1})`.

Uses strict inequality so that `ℱ₀` is trivial (w₀ is deterministic)
and `ξ_t` is independent of `ℱ_t`. -/
noncomputable def sgdFiltration
    (ξ : ℕ → Ω → S) (hξ : ∀ t, Measurable (ξ t)) : Filtration ℕ mΩ where
  seq t := ⨆ (j : ℕ) (_ : j < t), MeasurableSpace.comap (ξ j) ‹MeasurableSpace S›
  mono' _ _ hij := iSup₂_mono' fun k hk => ⟨k, lt_of_lt_of_le hk hij, le_rfl⟩
  le' t := iSup₂_le fun j _ => (hξ j).comap_le

omit [CompleteSpace E] in
/-- The SGD process is adapted to its natural filtration. -/
theorem sgdProcess_adapted {w₀ : E} {η : ℕ → ℝ}
    {gradL : E → S → E} {ξ : ℕ → Ω → S}
    (hξ : ∀ t, Measurable (ξ t))
    (hg : Measurable (Function.uncurry gradL)) :
    Adapted (sgdFiltration ξ hξ) (fun t => sgdProcess w₀ η gradL ξ t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    simp only [sgdProcess]
    have h_wt : Measurable[sgdFiltration ξ hξ (t + 1)] (sgdProcess w₀ η gradL ξ t) :=
      ih.mono ((sgdFiltration ξ hξ).mono (Nat.le_succ t)) le_rfl
    have h_ξt : Measurable[sgdFiltration ξ hξ (t + 1)] (ξ t) := by
      rw [measurable_iff_comap_le]
      exact le_iSup₂_of_le t (Nat.lt_succ_self t) le_rfl
    exact h_wt.sub ((hg.comp (h_wt.prodMk h_ξt)).const_smul _)

-- ============================================================================
-- Section 5b : Independence of process t from ξ t
-- ============================================================================

omit [CompleteSpace E] in
/-- The SGD process at step `t` is independent of the random sample `ξ t`.

**Proof**: `process t` depends only on `ξ 0, …, ξ (t−1)`, so it is measurable w.r.t.
`ℱ_t = σ(ξ₀, …, ξ_{t−1})`. By `iIndepFun`, `ℱ_t ⊥ σ(ξ_t)`, hence
`process t ⊥ ξ t` by sigma-algebra monotonicity. -/
lemma sgdProcess_indepFun_xi
    {w₀ : E} {η : ℕ → ℝ} {gradL : E → S → E} {ξ : ℕ → Ω → S}
    {P : Measure Ω}
    (hξ_meas : ∀ t, Measurable (ξ t))
    (hξ_indep : iIndepFun (β := fun _ => S) ξ P)
    (hgL : Measurable (Function.uncurry gradL))
    (t : ℕ) :
    IndepFun (sgdProcess w₀ η gradL ξ t) (ξ t) P := by
  -- The natural filtration
  set F := sgdFiltration ξ hξ_meas with hF_def
  -- process t is F t -measurable (adaptedness)
  have h_adapted : Measurable[F t] (sgdProcess w₀ η gradL ξ t) :=
    sgdProcess_adapted hξ_meas hgL t
  -- comap(process t) ≤ F t
  have h_comap_le :
      (inferInstance : MeasurableSpace E).comap (sgdProcess w₀ η gradL ξ t) ≤ F t :=
    measurable_iff_comap_le.mp h_adapted
  -- iIndepFun gives iIndep on comap sigma-algebras (definitionally)
  have h_iIndep : iIndep (fun i => (inferInstance : MeasurableSpace S).comap (ξ i)) P :=
    hξ_indep
  -- F t and comap(ξ t) are independent: from iIndep + disjoint index sets
  have h_filt_indep : Indep (F t) ((inferInstance : MeasurableSpace S).comap (ξ t)) P := by
    have h_le : ∀ i, (inferInstance : MeasurableSpace S).comap (ξ i) ≤ mΩ :=
      fun i => (hξ_meas i).comap_le
    have h_disj : Disjoint ({j : ℕ | j < t}) ({t} : Set ℕ) :=
      Set.disjoint_left.mpr fun j hj ht => absurd (ht ▸ hj) (Nat.lt_irrefl t)
    -- F t = ⨆ j ∈ {j | j < t}, comap(ξ j)  (matches filtration definition)
    have h_F_eq : F t = ⨆ j ∈ {j : ℕ | j < t},
        (inferInstance : MeasurableSpace S).comap (ξ j) := by
      simp [hF_def, sgdFiltration, Set.mem_setOf_eq]
    -- ⨆ i ∈ {t}, comap(ξ i) = comap(ξ t)
    have h_sing : ⨆ i ∈ ({t} : Set ℕ),
        (inferInstance : MeasurableSpace S).comap (ξ i) =
        (inferInstance : MeasurableSpace S).comap (ξ t) := by
      simp
    rw [h_F_eq, ← h_sing]
    exact indep_iSup_of_disjoint h_le h_iIndep h_disj
  -- Conclude by monotonicity: comap(process t) ≤ F t
  exact indep_of_indep_of_le_left h_filt_indep h_comap_le

-- ============================================================================
-- Section 6 : Assumptions on Stochastic Gradient
-- ============================================================================

/-- Unbiasedness: `E_s[∇L(w, s)] = ∇f(w)` for all `w`. -/
def IsUnbiased (gradL : E → S → E) (gradF : E → E) (ν : Measure S) : Prop :=
  ∀ w : E, ∫ s, gradL w s ∂ν = gradF w

/-- Bounded second moment: `E_s[‖∇L(w, s)‖²] ≤ σ²` for all `w`,
with explicit integrability (see docs/CONVENTIONS.md §1). -/
def HasBoundedVariance (gradL : E → S → E) (ν : Measure S) (σ : ℝ) : Prop :=
  ∀ w : E, Integrable (fun s => ‖gradL w s‖ ^ 2) ν ∧ ∫ s, ‖gradL w s‖ ^ 2 ∂ν ≤ σ ^ 2

/-- L-smoothness: the true gradient `∇f` is `L`-Lipschitz. -/
def IsLSmooth (gradF : E → E) (L : NNReal) : Prop :=
  LipschitzWith L gradF

/-- Stochastic gradient noise: `e(w, s) = ∇L(w, s) − ∇f(w)`. -/
noncomputable def sgdNoise (gradL : E → S → E) (gradF : E → E) (w : E) (s : S) : E :=
  gradL w s - gradF w

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Under unbiasedness, the noise has zero mean. -/
theorem noise_mean_zero {gradL : E → S → E} {gradF : E → E} {ν : Measure S}
    [IsProbabilityMeasure ν]
    (h_unbiased : IsUnbiased gradL gradF ν)
    (h_int : ∀ w, Integrable (gradL w) ν)
    (w : E) :
    ∫ s, sgdNoise gradL gradF w s ∂ν = 0 := by
  simp only [sgdNoise]
  rw [integral_sub (h_int w) (integrable_const _)]
  simp [h_unbiased w, integral_const]

-- ============================================================================
-- Section 7 : Extended Infrastructure for Convergence Analysis
-- ============================================================================

/-- The stochastic gradient noise has bounded variance:
`E_s[‖∇L(w, s) − ∇f(w)‖²] ≤ σ²` for all `w`.
This is a standard assumption in SGD convergence proofs. -/
def HasBoundedNoiseVariance (gradL : E → S → E) (gradF : E → E)
    (ν : Measure S) (σ : ℝ) : Prop :=
  ∀ w : E, ∫ s, ‖sgdNoise gradL gradF w s‖ ^ 2 ∂ν ≤ σ ^ 2

/-- `gradF` is the gradient of `f` at every point. -/
def IsGradientOf (f : E → ℝ) (gradF : E → E) : Prop :=
  ∀ w : E, HasGradientAt f (gradF w) w

/-- `w*` is a global minimizer of `f`. -/
def IsMinimizer (f : E → ℝ) (wStar : E) : Prop :=
  ∀ w : E, f wStar ≤ f w

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Under unbiasedness, the noise is uncorrelated with every direction `v`:
`E_s[⟪∇L(w, s) − ∇f(w), v⟫] = 0`. -/
theorem noise_inner_product_zero {gradL : E → S → E} {gradF : E → E} {ν : Measure S}
    [IsProbabilityMeasure ν]
    (h_unbiased : IsUnbiased gradL gradF ν)
    (h_int : ∀ w, Integrable (gradL w) ν)
    (w v : E) :
    ∫ s, ⟪sgdNoise gradL gradF w s, v⟫_ℝ ∂ν = 0 := by
  have h_noise_int : Integrable (fun s => sgdNoise gradL gradF w s) ν :=
    (h_int w).sub (integrable_const _)
  -- Swap ⟪noise, v⟫ → ⟪v, noise⟫, then pull v outside the integral
  simp_rw [real_inner_comm v]
  rw [integral_inner h_noise_int v, noise_mean_zero h_unbiased h_int w, inner_zero_right]

