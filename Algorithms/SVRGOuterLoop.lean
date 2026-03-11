import Algorithms.SVRG
import Lib.Layer0.ConvexFOC

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
`svrgProcess_measurable` with snapshot-dependent oracle.

Used in: `SVRG outer-loop strongly-convex convergence`
  (`Algorithms/SVRGOuterLoop.lean`, bridge construction — iterate measurability) -/
theorem svrgOuterProcess_measurable
    (hgL : Measurable (Function.uncurry setup.toSVRGSetup.toSGDSetup.gradL))
    (hgF_meas : Measurable setup.toSVRGSetup.toSGDSetup.gradF)
    (k : ℕ) :
    Measurable (svrgOuterProcess setup k) := by
  -- Measurability proof requires induction on both outer epoch k and inner step t
  -- The key insight: svrgOuterProcess (k+1) is built from measurable operations
  -- on svrgOuterProcess k, ξ, gradL, and gradF
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
      -- svrgOuterProcess (k+1) ω = svrgProcess wTilde gradLTilde m ω
      -- where wTilde = svrgOuterProcess k ω (measurable by IH)
      -- and gradLTilde = gradF (svrgOuterProcess k ω) (measurable by composition)
      -- The inner process svrgProcess is measurable for fixed wTilde, gradLTilde
      -- by svrgProcess_measurable (SVRG.lean:72-81)
      -- For snapshot-dependent case, we need joint measurability in (wTilde, gradLTilde, ω)
      -- This is a Level 2 gap - the proof requires extending svrgProcess_measurable
      -- to handle measurable functions wTilde, gradLTilde : Ω → E
      -- For now, we note that the main theorem takes measurability as hypotheses
      sorry -- MEASURABILITY_TODO: requires joint measurability lemma for svrgProcess with snapshot-dependent parameters

/-- Adaptedness of outer process to `sgdFiltration`.

Used in: `SVRG outer-loop strongly-convex convergence`
  (`Algorithms/SVRGOuterLoop.lean`, filtration argument) -/
theorem svrgOuterProcess_adapted
    (hgL : Measurable (Function.uncurry setup.toSVRGSetup.toSGDSetup.gradL))
    (hgF_meas : Measurable setup.toSVRGSetup.toSGDSetup.gradF) :
    Adapted (sgdFiltration setup.toSVRGSetup.toSGDSetup.ξ setup.toSVRGSetup.toSGDSetup.hξ_meas)
      (fun k => svrgOuterProcess setup k) := by
  intro k
  induction k with
  | zero =>
      simp [svrgOuterProcess]
  | succ k ih =>
      simp [svrgOuterProcess]
      sorry -- ADAPTED_TODO

/-- Independence of `svrgOuterProcess k` from epoch k samples.

Used in: `SVRG outer-loop strongly-convex convergence`
  (`Algorithms/SVRGOuterLoop.lean`, independence field) -/
lemma svrgOuterProcess_indepFun_xi_epoch
    (hgL : Measurable (Function.uncurry setup.toSVRGSetup.toSGDSetup.gradL))
    (hgF_meas : Measurable setup.toSVRGSetup.toSGDSetup.gradF)
    (k : ℕ) :
    IndepFun (svrgOuterProcess setup k)
      (setup.toSVRGSetup.toSGDSetup.ξ (k * setup.m))
      setup.toSVRGSetup.toSGDSetup.P := by
  -- Key insight: svrgOuterProcess k depends only on samples ξ₀, ..., ξ_{k·m-1}
  -- while ξ_{k·m} is independent of all previous samples by iIndepFun
  -- Proof deferred - requires careful handling of iIndepFun sample sequence
  sorry -- INDEP_TODO: requires induction on k with iIndepFun argument

-- ============================================================================
-- Section 3: Main Convergence Theorem
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
  -- Proof by induction on K (number of outer epochs)
  -- Define contraction factor ρ = (1 - ημ)^m
  set ρ := (1 - η * μ) ^ setup.m with hρ_def
  -- Define steady-state constant C = (4L/μ + 2L²/μ²) · (f(w₀) - f*)
  set C := (4 * (L : ℝ) / μ + 2 * (L : ℝ) ^ 2 / μ ^ 2) * (f (setup.toSVRGSetup.toSGDSetup.w₀) - fStar) with hC_def
  have hρ_nonneg : 0 ≤ ρ := by
    rw [hρ_def]
    exact pow_nonneg (by linarith) _
  -- Induction on K
  induction setup.K with
  | zero =>
      -- Base case: K = 0, svrgOuterProcess 0 = w₀
      simp [svrgOuterProcess, hρ_def, hC_def, pow_zero, mul_zero, zero_add]
  | succ K ih =>
      -- Inductive step: assume bound holds for K, prove for K+1
      -- Epoch contraction: E[‖w_{K+1} - w*‖²] ≤ ρ · E[‖w_K - w*‖²] + C
      have h_epoch_contract : ∫ ω, ‖svrgOuterProcess setup (K + 1) ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.toSGDSetup.P ≤
          ρ * ∫ ω, ‖svrgOuterProcess setup K ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.toSGDSetup.P + C := by
        -- EPOCH_CONTRACTION: Level 2 structural gap
        -- Requires applying svrg_convergence_inner_strongly_convex with snapshot-dependent variance
        sorry -- EPOCH_CONTRACTION_TODO: Level 2 gap
      -- Combine with induction hypothesis
      calc ∫ ω, ‖svrgOuterProcess setup (K + 1) ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.toSGDSetup.P
          ≤ ρ * ∫ ω, ‖svrgOuterProcess setup K ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.toSGDSetup.P + C := h_epoch_contract
        _ ≤ ρ * (ρ ^ K * ‖setup.toSVRGSetup.toSGDSetup.w₀ - wStar‖ ^ 2 + C * (1 - ρ ^ K)) + C := by
            gcongr
        _ = ρ ^ (K + 1) * ‖setup.toSVRGSetup.toSGDSetup.w₀ - wStar‖ ^ 2 + C * (1 - ρ ^ (K + 1)) := by
            ring
        _ = (1 - η * μ) ^ (setup.m * (K + 1)) * ‖setup.toSVRGSetup.toSGDSetup.w₀ - wStar‖ ^ 2 +
            (4 * (L : ℝ) / μ + 2 * (L : ℝ) ^ 2 / μ ^ 2) * (1 - (1 - η * μ) ^ (setup.m * (K + 1))) *
              (f (setup.toSVRGSetup.toSGDSetup.w₀) - fStar) := by
            rw [hρ_def, hC_def]
            simp [pow_mul, pow_succ]
            <;> ring_nf

end SVRGOuterSetup
