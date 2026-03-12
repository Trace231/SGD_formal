import Algorithms.SVRG
import Lib.Layer0.ConvexFOC
import Lib.Glue.Staging.SVRGOuterLoop

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {S : Type*} [MeasurableSpace S]
variable {Ω : Type*} [MeasurableSpace Ω]

/-!
# SVRG Outer Loop Convergence — Algorithm Layer (Layer 2)

Layer: 2 (concrete algorithm proof with two-level telescoping)

Archetype: B — novel two-level structure:
- Inner epoch: Archetype A (reduces to SGD via `effectiveSGDSetup`)
- Outer loop: Archetype B (explicit telescoping with snapshot-dependent variance)

## Main definitions

* `SVRGOuterSetup` — extends `SVRGSetup` with epoch length `m` and iteration count `K`
* `svrgOuterProcess` — outer-loop iterate (snapshot refreshed every `m` steps)

## Proof strategy

1. Inner epoch contraction via `svrg_convergence_inner_strongly_convex`
2. Primitive variance bound (pointwise inequality, no lemma dependency)
3. Gradient norm bound via `strongly_convex_gradient_norm_bound`
4. Telescope over K outer epochs

## Conventions compliance

* Convention 1: `HasBoundedVariance` includes `Integrable`
* Convention 4: All lemmas have `Used in:` tags
* Convention 5: Resolution B (primitive inequality form for variance)
* Convention 6: Dot notation `setup.svrgOuterProcess k` throughout
-/

-- ============================================================================
-- Section 1: SVRG Outer Setup Structure
-- ============================================================================

/-- SVRG outer-loop setup: extends inner-loop setup with epoch parameters.

The snapshot is refreshed every `m` inner steps, and the outer loop runs for `K`
epochs. The snapshot and its gradient are NOT structure fields — they are
computed from the outer iterate at each epoch boundary.

Used in: `SVRG outer-loop strongly-convex convergence`
  (`Algorithms/SVRGOuterLoop.lean`, structure definition) -/
structure SVRGOuterSetup
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E]
    (S : Type*) [MeasurableSpace S]
    (Ω : Type*) [MeasurableSpace Ω] where
  toSVRGSetup : SVRGSetup E S Ω
  m : ℕ  -- inner epoch length
  h_m_pos : 0 < m
  K : ℕ  -- number of outer epochs

namespace SVRGOuterSetup

variable (setup : SVRGOuterSetup E S Ω)

/-- SVRG outer-loop process: snapshot refreshed every `m` steps.

Definition:
- `svrgOuterProcess setup 0 = w₀` (initial point)
- `svrgOuterProcess setup (k+1) ω = svrgProcess (svrgOuterProcess setup k ω) (gradF (svrgOuterProcess setup k ω)) m ω`

For each ω, the snapshot w̃_k(ω) is a fixed vector, so we apply the inner process
with that fixed snapshot to ω.

Used in: `SVRG outer-loop strongly-convex convergence`
  (`Algorithms/SVRGOuterLoop.lean`, main theorem statement) -/
noncomputable def svrgOuterProcess (setup : SVRGOuterSetup E S Ω) : ℕ → Ω → E
  | 0 => fun _ => setup.toSVRGSetup.toSGDSetup.w₀
  | k + 1 => fun ω =>
      let wTilde := svrgOuterProcess setup k ω
      let gradLTilde := setup.toSVRGSetup.toSGDSetup.gradF wTilde
      setup.toSVRGSetup.svrgProcess wTilde gradLTilde setup.m ω

omit [SecondCountableTopology E] in
@[simp] theorem process_zero (setup : SVRGOuterSetup E S Ω) :
    svrgOuterProcess setup 0 = fun _ => setup.toSVRGSetup.toSGDSetup.w₀ := rfl

omit [SecondCountableTopology E] in
@[simp] theorem process_succ (setup : SVRGOuterSetup E S Ω) (k : ℕ) (ω : Ω) :
    svrgOuterProcess setup (k + 1) ω =
      let wTilde := svrgOuterProcess setup k ω
      let gradLTilde := setup.toSVRGSetup.toSGDSetup.gradF wTilde
      setup.toSVRGSetup.svrgProcess wTilde gradLTilde setup.m ω := rfl

-- ============================================================================
-- Section 2: Process Infrastructure Lemmas
-- ============================================================================

/-- Measurability of each outer-loop iterate.

Proof: Induction on k. Base case is constant (measurable). Step case uses
`svrgProcess_measurable_random_snapshot` with snapshot-dependent oracle.

Used in: `SVRG outer-loop strongly-convex convergence`
  (`Algorithms/SVRGOuterLoop.lean`, bridge construction — iterate measurability) -/
theorem svrgOuterProcess_measurable
    (hgL : Measurable (Function.uncurry setup.toSVRGSetup.toSGDSetup.gradL))
    (hgF_meas : Measurable setup.toSVRGSetup.toSGDSetup.gradF)
    (k : ℕ) :
    Measurable (svrgOuterProcess setup k) := by
  induction k with
  | zero =>
      -- Base case: constant function w₀
      simpa [svrgOuterProcess] using measurable_const
  | succ k ih =>
      -- Inductive step: apply joint measurability lemma
      -- ω ↦ svrgProcess (wTilde(ω)) (gradLTilde(ω)) m ω
      -- where wTilde = svrgOuterProcess k (measurable by ih)
      -- and gradLTilde = gradF ∘ wTilde (measurable by hgF_meas.comp ih)
      have h_gradLTilde_meas : Measurable (fun ω =>
          setup.toSVRGSetup.toSGDSetup.gradF (svrgOuterProcess setup k ω)) :=
        hgF_meas.comp ih
      -- Apply staging lemma for snapshot-dependent process
      have h_step_meas : Measurable (fun ω =>
          setup.toSVRGSetup.svrgProcess (svrgOuterProcess setup k ω)
            (setup.toSVRGSetup.toSGDSetup.gradF (svrgOuterProcess setup k ω))
            setup.m ω) :=
          svrgProcess_measurable_random_snapshot setup.toSVRGSetup
            (svrgOuterProcess setup k) (fun ω => setup.toSVRGSetup.toSGDSetup.gradF (svrgOuterProcess setup k ω))
            ih h_gradLTilde_meas hgL setup.m
      -- svrgOuterProcess (k+1) equals this by definition
      simpa [svrgOuterProcess] using h_step_meas

-- Adaptedness of outer process to `sgdFiltration` at epoch boundaries.
-- Note: `svrgOuterProcess k` is adapted to `F_{k*m}`, not `F_k`.
-- This lemma is omitted as it is not required for the main convergence proof.
-- Used in: future extensions (`Algorithms/SVRGOuterLoop.lean`)
-- theorem svrgOuterProcess_adapted ... := by sorry

-- Independence of `svrgOuterProcess k` from epoch k samples.
-- Note: This lemma is not required for the main convergence proof.
-- Used in: future extensions (`Algorithms/SVRGOuterLoop.lean`)
-- lemma svrgOuterProcess_indepFun_xi_epoch ... := by sorry

-- ============================================================================
-- Section 3: Epoch Contraction Lemma
-- ============================================================================

/-- One-epoch contraction bound: applies inner-loop convergence with fixed snapshot.

For a FIXED snapshot wTilde, running m steps of inner loop gives:
E[‖svrgProcess wTilde gradLTilde m − w*‖²] ≤ (1 − ημ)^m · ‖w₀ − w*‖² + η·σ_eff²/μ

This is a simplified version for fixed snapshot; the outer loop applies this
conditionally on the random snapshot from the previous epoch.

Used in: `svrg_outer_convergence_strongly_convex` (Algorithms/SVRGOuterLoop.lean, Step 1) -/
theorem svrg_epoch_contraction_fixed
    (f : E → ℝ) {L μ : NNReal} {η σeff : ℝ} (wStar wTilde gradLTilde : E) (fStar : ℝ)
    (hgradLTilde : gradLTilde = setup.toSVRGSetup.toSGDSetup.gradF wTilde)
    (hgrad : IsGradientOf f setup.toSVRGSetup.toSGDSetup.gradF)
    (hsmooth : IsLSmooth setup.toSVRGSetup.toSGDSetup.gradF L)
    (hsc : StrongConvexOn Set.univ μ f)
    (hμ_pos : 0 < μ)
    (hη_pos : 0 < η) (hημ : η * μ < 1) (hη_L : η ≤ 1 / (L : ℝ))
    (hfStar : ∀ w, fStar ≤ f w)
    (hmin : ∀ w, f wStar ≤ f w)
    (hvar_eff : HasBoundedVariance
        (setup.toSVRGSetup.svrgOracle wTilde gradLTilde)
        setup.toSVRGSetup.sampleDist σeff)
    (hunb : IsUnbiased setup.toSVRGSetup.toSGDSetup.gradL setup.toSVRGSetup.toSGDSetup.gradF
      setup.toSVRGSetup.sampleDist)
    (h_sample_prob : IsProbabilityMeasure setup.toSVRGSetup.sampleDist)
    (hη : ∀ t, setup.toSVRGSetup.toSGDSetup.η t = η)
    (hgL : Measurable (Function.uncurry setup.toSVRGSetup.toSGDSetup.gradL))
    (h_intL_base : ∀ w, Integrable (setup.toSVRGSetup.toSGDSetup.gradL w)
      setup.toSVRGSetup.sampleDist)
    (h_intL_eff : ∀ w, Integrable (setup.toSVRGSetup.svrgOracle wTilde gradLTilde w)
      setup.toSVRGSetup.sampleDist)
    (h_int_sq : ∀ t, Integrable (fun ω =>
        ‖setup.toSVRGSetup.svrgOracle wTilde gradLTilde
            (setup.toSVRGSetup.svrgProcess wTilde gradLTilde t ω)
          (setup.toSVRGSetup.toSGDSetup.ξ t ω)‖ ^ 2) setup.toSVRGSetup.toSGDSetup.P)
    (h_int_norm_sq : ∀ t, Integrable (fun ω =>
        ‖setup.toSVRGSetup.svrgProcess wTilde gradLTilde t ω - wStar‖ ^ 2)
      setup.toSVRGSetup.toSGDSetup.P)
    (h_int_inner : ∀ t, Integrable (fun ω =>
        ⟪setup.toSVRGSetup.svrgProcess wTilde gradLTilde t ω - wStar,
          setup.toSVRGSetup.svrgOracle wTilde gradLTilde
            (setup.toSVRGSetup.svrgProcess wTilde gradLTilde t ω)
            (setup.toSVRGSetup.toSGDSetup.ξ t ω)⟫_ℝ) setup.toSVRGSetup.toSGDSetup.P)
    (h_int_gF_inner : ∀ t, Integrable (fun ω =>
        ⟪setup.toSVRGSetup.svrgProcess wTilde gradLTilde t ω - wStar,
          setup.toSVRGSetup.toSGDSetup.gradF (setup.toSVRGSetup.svrgProcess wTilde gradLTilde t ω)
        ⟫_ℝ) setup.toSVRGSetup.toSGDSetup.P) :
    ∫ ω, ‖setup.toSVRGSetup.svrgProcess wTilde gradLTilde setup.m ω - wStar‖ ^ 2
        ∂setup.toSVRGSetup.toSGDSetup.P ≤
      (1 - η * μ) ^ setup.m * ‖setup.toSVRGSetup.toSGDSetup.w₀ - wStar‖ ^ 2
      + η * σeff ^ 2 / μ := by
  -- Direct application of inner-loop convergence
  have h_inner := setup.toSVRGSetup.svrg_convergence_inner_strongly_convex
    (f := f) (L := L) (μ := μ) (σeff := σeff) (η := η)
    (wStar := wStar) (wTilde := wTilde) (gradLTilde := gradLTilde)
    hgradLTilde hgrad hsmooth hsc hvar_eff hunb hmin h_sample_prob
    hμ_pos hη_pos hη_L hημ hη setup.m
    hgL h_intL_base h_intL_eff h_int_sq h_int_norm_sq h_int_inner h_int_gF_inner
  exact h_inner

-- ============================================================================
-- Section 3b: Epoch Contraction with Random Snapshot (Archetype B Bridge)
-- ============================================================================

/-- Epoch contraction bound with random snapshot: integrates inner-loop contraction
over the distribution of the snapshot from the previous epoch.

This is the key Archetype B bridge lemma: it applies `svrg_epoch_contraction_fixed`
conditionally on the random snapshot w̃_K, then integrates using the primitive
variance bound and gradient norm bound.

Used in: `svrg_outer_convergence_strongly_convex` (Algorithms/SVRGOuterLoop.lean, Step 2) -/
theorem svrg_epoch_contraction_random_snapshot
    (f : E → ℝ) {L μ : NNReal} {η σeff : ℝ} (wStar : E) (fStar : ℝ)
    (hgrad : IsGradientOf f setup.toSVRGSetup.toSGDSetup.gradF)
    (hsmooth : IsLSmooth setup.toSVRGSetup.toSGDSetup.gradF L)
    (hsc : StrongConvexOn Set.univ μ f)
    (hμ_pos : 0 < μ)
    (hη_pos : 0 < η) (hημ : η * μ < 1) (hη_L : η ≤ 1 / (L : ℝ))
    (hfStar : ∀ w, fStar ≤ f w)
    (hmin : ∀ w, f wStar ≤ f w)
    -- Measurability and integrability for the random snapshot:
    (wTilde_fun : Ω → E)
    (hwTilde_meas : Measurable wTilde_fun)
    (h_int_wTilde : Integrable (fun ω => ‖wTilde_fun ω - wStar‖ ^ 2)
      setup.toSVRGSetup.toSGDSetup.P)
    -- Variance bound for effective oracle:
    (hvar_eff : HasBoundedVariance
        (setup.toSVRGSetup.svrgOracle (wTilde_fun ω) (setup.toSVRGSetup.toSGDSetup.gradF (wTilde_fun ω)))
        setup.toSVRGSetup.sampleDist σeff)
    -- Base integrability:
    (hgL : Measurable (Function.uncurry setup.toSVRGSetup.toSGDSetup.gradL))
    (h_intL_base : ∀ w, Integrable (setup.toSVRGSetup.toSGDSetup.gradL w)
      setup.toSVRGSetup.sampleDist)
    (h_intL_eff : ∀ w, Integrable (setup.toSVRGSetup.svrgOracle (wTilde_fun ω) (setup.toSVRGSetup.toSGDSetup.gradF (wTilde_fun ω)) w)
      setup.toSVRGSetup.sampleDist)
    (h_int_sq : ∀ t, Integrable (fun ω =>
        ‖setup.toSVRGSetup.svrgOracle (wTilde_fun ω)
            (setup.toSVRGSetup.toSGDSetup.gradF (wTilde_fun ω))
            (setup.toSVRGSetup.svrgProcess (wTilde_fun ω)
              (setup.toSVRGSetup.toSGDSetup.gradF (wTilde_fun ω)) t ω)
          (setup.toSVRGSetup.toSGDSetup.ξ t ω)‖ ^ 2) setup.toSVRGSetup.toSGDSetup.P)
    (h_int_norm_sq : ∀ t, Integrable (fun ω =>
        ‖setup.toSVRGSetup.svrgProcess (wTilde_fun ω)
            (setup.toSVRGSetup.toSGDSetup.gradF (wTilde_fun ω)) t ω - wStar‖ ^ 2)
      setup.toSVRGSetup.toSGDSetup.P)
    (h_int_inner : ∀ t, Integrable (fun ω =>
        ⟪setup.toSVRGSetup.svrgProcess (wTilde_fun ω)
            (setup.toSVRGSetup.toSGDSetup.gradF (wTilde_fun ω)) t ω - wStar,
          setup.toSVRGSetup.svrgOracle (wTilde_fun ω)
            (setup.toSVRGSetup.toSGDSetup.gradF (wTilde_fun ω))
            (setup.toSVRGSetup.svrgProcess (wTilde_fun ω)
              (setup.toSVRGSetup.toSGDSetup.gradF (wTilde_fun ω)) t ω)
            (setup.toSVRGSetup.toSGDSetup.ξ t ω)⟫_ℝ) setup.toSVRGSetup.toSGDSetup.P)
    (h_int_gF_inner : ∀ t, Integrable (fun ω =>
        ⟪setup.toSVRGSetup.svrgProcess (wTilde_fun ω)
            (setup.toSVRGSetup.toSGDSetup.gradF (wTilde_fun ω)) t ω - wStar,
          setup.toSVRGSetup.toSGDSetup.gradF (setup.toSVRGSetup.svrgProcess
            (wTilde_fun ω) (setup.toSVRGSetup.toSGDSetup.gradF (wTilde_fun ω))
            t ω)⟫_ℝ) setup.toSVRGSetup.toSGDSetup.P)
    (hunb : IsUnbiased setup.toSVRGSetup.toSGDSetup.gradL setup.toSVRGSetup.toSGDSetup.gradF
      setup.toSVRGSetup.sampleDist)
    (h_sample_prob : IsProbabilityMeasure setup.toSVRGSetup.sampleDist)
    (hη : ∀ t, setup.toSVRGSetup.toSGDSetup.η t = η) :
    ∫ ω, ‖setup.toSVRGSetup.svrgProcess (wTilde_fun ω)
        (setup.toSVRGSetup.toSGDSetup.gradF (wTilde_fun ω))
        setup.m ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.toSGDSetup.P ≤
      (1 - η * μ) ^ setup.m * ∫ ω, ‖wTilde_fun ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.toSGDSetup.P +
      η * σeff ^ 2 / μ := by
  -- This lemma is an intermediate bridge; the main theorem uses a direct approach.
  -- Proof requires careful handling of conditional expectations (Archetype B).
  sorry

-- ============================================================================
-- Section 4: Main Convergence Theorem
-- ============================================================================

/-- Outer-loop SVRG convergence under strong convexity.

Archetype: B — two-level telescoping (inner epochs + outer iterations)

Proof chain:
1. Inner epoch contraction via `svrg_convergence_inner_strongly_convex`
2. Primitive variance bound (pointwise inequality, scoping-corrected)
3. Gradient norm bound via `strongly_convex_gradient_norm_bound`
4. Telescope over K outer epochs

Used in: `SVRG outer-loop strongly-convex convergence`
  (`Algorithms/SVRGOuterLoop.lean`, main theorem) -/
theorem svrg_outer_convergence_strongly_convex
    (f : E → ℝ) {L μ : NNReal} {η : ℝ} (wStar : E) (fStar : ℝ)
    (hgrad : IsGradientOf f setup.toSVRGSetup.toSGDSetup.gradF)
    (hsmooth : IsLSmooth setup.toSVRGSetup.toSGDSetup.gradF L)
    (hsc : StrongConvexOn Set.univ μ f)
    (hμ_pos : 0 < μ)
    (hη_pos : 0 < η) (hημ : η * μ < 1)
    (hfStar : ∀ w, fStar ≤ f w)
    (hmin : f wStar = fStar)
    -- PRIMITIVE variance bound (scoping corrected — no free ω in hypothesis):
    (hvar_eff : ∀ k : ℕ, ∀ w_tilde : E, ∀ w : E,
      ∫ s, ‖setup.toSVRGSetup.toSGDSetup.gradL w s
          - setup.toSVRGSetup.toSGDSetup.gradL w_tilde s
          + setup.toSVRGSetup.toSGDSetup.gradF w_tilde‖ ^ 2
        ∂setup.toSVRGSetup.sampleDist
      ≤ 4 * (L : ℝ) * (f w - fStar) + 2 * ‖setup.toSVRGSetup.toSGDSetup.gradF w_tilde‖ ^ 2)
    -- Archetype B dual integrability (GLUE_TRICKS.md §4b):
    (h_int_outer : ∀ k, Integrable (fun ω => ‖svrgOuterProcess setup (k+1) ω - wStar‖ ^ 2)
      setup.toSVRGSetup.toSGDSetup.P)
    (h_int_inner : ∀ k, Integrable (fun ω =>
      ‖setup.toSVRGSetup.svrgProcess (svrgOuterProcess setup k ω)
        (setup.toSVRGSetup.toSGDSetup.gradF (svrgOuterProcess setup k ω))
        setup.m ω - wStar‖ ^ 2) setup.toSVRGSetup.toSGDSetup.P)
    (hgL : Measurable (Function.uncurry setup.toSVRGSetup.toSGDSetup.gradL))
    (hgF_meas : Measurable setup.toSVRGSetup.toSGDSetup.gradF)
    (hunb : IsUnbiased setup.toSVRGSetup.toSGDSetup.gradL setup.toSVRGSetup.toSGDSetup.gradF
      setup.toSVRGSetup.sampleDist)
    (h_sample_prob : IsProbabilityMeasure setup.toSVRGSetup.sampleDist)
    (h_intL_base : ∀ w, Integrable (setup.toSVRGSetup.toSGDSetup.gradL w)
      setup.toSVRGSetup.sampleDist) :
    ∫ ω, ‖svrgOuterProcess setup setup.K ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.toSGDSetup.P ≤
      (1 - η * μ) ^ (setup.m * setup.K) * ‖setup.toSVRGSetup.toSGDSetup.w₀ - wStar‖ ^ 2 +
      (4 * (L : ℝ) / μ + 2 * (L : ℝ) ^ 2 / μ ^ 2) * (1 - (1 - η * μ) ^ (setup.m * setup.K)) *
        (f (setup.toSVRGSetup.toSGDSetup.w₀) - fStar) := by
  -- Archetype B: two-level telescoping (inner epochs + outer iterations)
  -- Proof by induction on K (number of outer epochs)
  induction setup.K with
  | zero =>
      -- Base case: K = 0, outer process is w₀
      have h_process_zero : svrgOuterProcess setup 0 = fun _ => setup.toSVRGSetup.toSGDSetup.w₀ := process_zero setup
      simp only [h_process_zero]
      -- The integral becomes ∫ ω, ‖w₀ - wStar‖² ∂P = ‖w₀ - wStar‖² (constant function)
      -- RHS: (1 - ημ)^0 * ‖w₀ - wStar‖² + (...) * (1 - 1) * (...) = ‖w₀ - wStar‖²
      simp only [pow_zero, mul_zero, sub_self, integral_const, probReal_univ]
      <;> ring_nf
      <;> norm_num
  | succ K ih =>
      -- Inductive step: assume for K, prove for K+1
      -- svrgOuterProcess (K+1) = svrgProcess (svrgOuterProcess K) (gradF (svrgOuterProcess K)) m
      -- Apply inner epoch contraction with random snapshot
      -- This requires the primitive variance bound and gradient norm bound
      -- The proof telescopes using the contraction factor and variance accumulation
      -- For staging, we use a simplified approach with sorry for the detailed variance handling
      have h_inner_contract : ∀ (wTilde_fun : Ω → E) (hwTilde_meas : Measurable wTilde_fun),
        ∫ ω, ‖setup.toSVRGSetup.svrgProcess (wTilde_fun ω)
            (setup.toSVRGSetup.toSGDSetup.gradF (wTilde_fun ω))
            setup.m ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.toSGDSetup.P ≤
          (1 - η * μ) ^ setup.m * ∫ ω, ‖wTilde_fun ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.toSGDSetup.P +
          η * (4 * (L : ℝ) / μ + 2 * (L : ℝ) ^ 2 / μ ^ 2) *
            (∫ ω, f (wTilde_fun ω) ∂setup.toSVRGSetup.toSGDSetup.P - fStar) := by
        -- This is the key epoch contraction with random snapshot
        -- It applies svrg_convergence_inner_strongly_convex pointwise and integrates
        -- The variance bound comes from hvar_eff and strongly_convex_gradient_norm_bound
        sorry
      -- Apply the contraction to wTilde_fun = svrgOuterProcess K
      have h_step := h_inner_contract (svrgOuterProcess setup K) (svrgOuterProcess_measurable setup hgL hgF_meas K)
      -- Combine with induction hypothesis and telescope
      sorry

end SVRGOuterSetup
