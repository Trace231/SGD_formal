import Algorithms.SVRG
import Lib.Layer0.ConvexFOC

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {S : Type*} [MeasurableSpace S]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- SVRG outer-loop setup: inherits inner-loop infrastructure, adds epoch-level sampling.

Used in: `SVRG outer loop` (Algorithms/SVRGOuterLoop.lean, all outer-loop theorems) -/
structure SVRGOuterSetup
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E]
    (S : Type*) [MeasurableSpace S]
    (Ω : Type*) [MeasurableSpace Ω] where
  toSVRGSetup : SVRGSetup E S Ω
  m : ℕ
  hm_pos : 0 < m
  ξ_epoch : ℕ → ℕ → Ω → S
  hξ_epoch_meas : ∀ k t, Measurable (ξ_epoch k t)
  hξ_epoch_indep : iIndepFun (fun kt : ℕ × ℕ => ξ_epoch kt.1 kt.2) toSVRGSetup.P
  hξ_epoch_ident : ∀ k t, IdentDistrib (ξ_epoch k t) (ξ_epoch 0 0) toSVRGSetup.P toSVRGSetup.P

namespace SVRGOuterSetup

variable (setup : SVRGOuterSetup E S Ω) (w₀ : E)

/-- Outer-loop iterate: epoch k endpoint after running m inner steps from epoch-start snapshot.

Used in: `SVRG outer loop` (Algorithms/SVRGOuterLoop.lean, all outer-loop theorems) -/
noncomputable def outerProcess : ℕ → Ω → E
  | 0 => fun _ => w₀
  | k + 1 => fun ω =>
      setup.toSVRGSetup.svrgProcess (outerProcess w₀ k ω) (setup.toSVRGSetup.gradF (outerProcess w₀ k ω))
        (fun t => setup.ξ_epoch k t) setup.m ω

omit [SecondCountableTopology E] in
@[simp] theorem outerProcess_zero : outerProcess w₀ 0 = fun _ => w₀ := rfl

omit [SecondCountableTopology E] in
@[simp] theorem outerProcess_succ (k : ℕ) :
    outerProcess w₀ (k + 1) = fun ω =>
      setup.toSVRGSetup.svrgProcess (outerProcess w₀ k ω) (setup.toSVRGSetup.gradF (outerProcess w₀ k ω))
        (fun t => setup.ξ_epoch k t) setup.m ω := rfl

/-- Measurability of outer-loop iterates.

Used in: `SVRG outer loop` (Algorithms/SVRGOuterLoop.lean, bridge construction) -/
theorem outerProcess_measurable (k : ℕ) : Measurable (outerProcess w₀ k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
      simp only [outerProcess]
      -- svrgProcess_measurable requires:
      -- 1. wTilde := outerProcess k (measurable by IH)
      -- 2. gradLTilde := gradF (outerProcess k) (measurable by hsmooth.continuous.measurable.comp ih)
      -- 3. ξ_epoch k (measurable by setup.hξ_epoch_meas k)
      exact setup.toSVRGSetup.svrgProcess_measurable
        (wTilde := outerProcess w₀ k)
        (gradLTilde := setup.toSVRGSetup.gradF ∘ outerProcess w₀ k)
        (hgL := setup.toSVRGSetup.toSGDSetup.hgL)
        (t := setup.m)

/-- Adaptedness of outer-loop iterates to natural filtration.

Used in: `SVRG outer loop` (Algorithms/SVRGOuterLoop.lean, independence argument) -/
theorem outerProcess_adapted :
    Adapted (sgdFiltration setup.toSVRGSetup.toSGDSetup.ξ setup.toSVRGSetup.toSGDSetup.hξ_meas)
      (fun k => outerProcess w₀ k) := by
  intro k
  induction k with
  | zero => exact measurable_const.adapted
  | succ k ih =>
      -- outerProcess (k+1) depends on ξ_epoch k 0, …, ξ_epoch k (m-1)
      -- These are independent of the base filtration, but outerProcess k is adapted
      -- Use svrgProcess_adapted pattern with epoch-k samples
      have h_adapted_inner : Adapted (sgdFiltration (fun t => setup.ξ_epoch k t) (setup.hξ_epoch_meas k))
          (fun t => setup.toSVRGSetup.svrgProcess (outerProcess w₀ k) (setup.toSVRGSetup.gradF (outerProcess w₀ k))
            (fun t => setup.ξ_epoch k t) t) := by
        simpa [SVRGSetup.svrgProcess] using
          sgdProcess_adapted (hξ := setup.hξ_epoch_meas k)
            (hg := setup.toSVRGSetup.measurable_svrgOracle
              (wTilde := outerProcess w₀ k)
              (gradLTilde := setup.toSVRGSetup.gradF (outerProcess w₀ k))
              setup.toSVRGSetup.toSGDSetup.hgL)
      -- outerProcess (k+1) = inner process at step m
      exact h_adapted_inner setup.m

/-- Independence: outerProcess k is independent of fresh epoch-k samples.

Used in: `SVRG outer loop` (Algorithms/SVRGOuterLoop.lean, variance bound step) -/
lemma outerProcess_indepFun_xi_epoch (k : ℕ) :
    IndepFun (outerProcess w₀ k) (fun t => setup.ξ_epoch k t) setup.toSVRGSetup.P := by
  -- outerProcess k depends only on ξ_epoch 0, …, ξ_epoch (k-1)
  -- iIndepFun gives independence across disjoint epoch indices
  have h_adapted : Measurable (outerProcess w₀ k) := outerProcess_measurable w₀ k
  have h_xi_meas : Measurable (fun t => setup.ξ_epoch k t) := setup.hξ_epoch_meas k
  -- Use iIndepFun with disjoint index sets
  have h_disj : Disjoint ({kt : ℕ × ℕ | kt.1 < k}) ({kt : ℕ × ℕ | kt.1 = k}) := by
    simp [Set.disjoint_left]
    intro ⟨i, j⟩ hij hki
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq] at hij hki
    linarith
  -- outerProcess k is measurable w.r.t. σ(ξ_epoch i t | i < k)
  -- ξ_epoch k is measurable w.r.t. σ(ξ_epoch k t | t)
  -- iIndepFun + disjoint indices → independence
  sorry  -- Requires detailed filtration argument analogous to sgdProcess_indepFun_xi

/-- One-epoch contraction bound for SVRG outer loop.

Used in: `SVRG outer loop` (Algorithms/SVRGOuterLoop.lean, telescoping proof) -/
theorem svrg_outer_one_epoch_contraction
    (f : E → ℝ) {L μ η : ℝ} (wStar : E)
    (hgrad : IsGradientOf f setup.toSVRGSetup.toSGDSetup.gradF)
    (hsmooth : IsLSmooth setup.toSVRGSetup.toSGDSetup.gradF L)
    (hsc : StrongConvexOn Set.univ μ f)
    (hmin : IsMinimizer f wStar)
    (hη_pos : 0 < η) (hημ : η * μ < 1)
    (hη : ∀ t, setup.toSVRGSetup.toSGDSetup.η t = η)
    (k : ℕ)
    (h_int_epoch_start : Integrable (fun ω => ‖outerProcess w₀ k ω - wStar‖ ^ 2) setup.toSVRGSetup.P)
    (h_int_epoch_end : Integrable (fun ω => ‖outerProcess w₀ (k + 1) ω - wStar‖ ^ 2) setup.toSVRGSetup.P)
    (h_int_inner : ∀ t < setup.m, Integrable (fun ω =>
        ‖setup.toSVRGSetup.svrgOracle (outerProcess w₀ k ω) (setup.toSVRGSetup.gradF (outerProcess w₀ k ω))
          (outerProcess w₀ k ω) (setup.ξ_epoch k t ω)‖ ^ 2) setup.toSVRGSetup.P)
    (h_int_inner_norm_sq : ∀ t < setup.m, Integrable (fun ω =>
        ‖setup.toSVRGSetup.svrgProcess (outerProcess w₀ k ω) (setup.toSVRGSetup.gradF (outerProcess w₀ k ω))
          (fun t => setup.ξ_epoch k t) t ω - wStar‖ ^ 2) setup.toSVRGSetup.P)
    (h_int_inner_inner : ∀ t < setup.m, Integrable (fun ω =>
        ⟪setup.toSVRGSetup.svrgProcess (outerProcess w₀ k ω) (setup.toSVRGSetup.gradF (outerProcess w₀ k ω))
          (fun t => setup.ξ_epoch k t) t ω - wStar,
          setup.toSVRGSetup.svrgOracle (outerProcess w₀ k ω) (setup.toSVRGSetup.gradF (outerProcess w₀ k ω))
            (setup.toSVRGSetup.svrgProcess (outerProcess w₀ k ω) (setup.toSVRGSetup.gradF (outerProcess w₀ k ω))
              (fun t => setup.ξ_epoch k t) t ω) (setup.ξ_epoch k t ω)⟫_ℝ) setup.toSVRGSetup.P)
    (h_int_inner_gF : ∀ t < setup.m, Integrable (fun ω =>
        ⟪setup.toSVRGSetup.svrgProcess (outerProcess w₀ k ω) (setup.toSVRGSetup.gradF (outerProcess w₀ k ω))
          (fun t => setup.ξ_epoch k t) t ω - wStar,
          setup.toSVRGSetup.gradF (setup.toSVRGSetup.svrgProcess (outerProcess w₀ k ω)
            (setup.toSVRGSetup.gradF (outerProcess w₀ k ω)) (fun t => setup.ξ_epoch k t) t ω)⟫_ℝ)
      setup.toSVRGSetup.P) :
    ∫ ω, ‖outerProcess w₀ (k + 1) ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.P ≤
      ((1 - η * μ) ^ setup.m + η * (L : ℝ) ^ 2 / μ) *
        ∫ ω, ‖outerProcess w₀ k ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.P := by
  -- Step 1: Apply inner-loop contraction (svrg_convergence_inner_strongly_convex)
  -- The inner-loop theorem applies for fixed snapshots; we use it with the epoch-k start point
  -- Note: outerProcess k ω is random, but the theorem applies pointwise for each ω
  have h_inner_contract : ∫ ω, ‖outerProcess w₀ (k + 1) ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.P ≤
      (1 - η * μ) ^ setup.m * ∫ ω, ‖outerProcess w₀ k ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.P +
        η / μ * ∫ ω, ‖setup.toSVRGSetup.gradF (outerProcess w₀ k ω) - setup.toSVRGSetup.gradF wStar‖ ^ 2 ∂setup.toSVRGSetup.P := by
    -- Apply svrg_convergence_inner_strongly_convex with wTilde := outerProcess k ω (pointwise)
    -- This requires lifting the theorem to handle random snapshots
    -- For now, use the theorem structure directly
    sorry
  -- Step 2: Lipschitz gradient norm bound
  have h_lip_bound : ∀ ω, ‖setup.toSVRGSetup.gradF (outerProcess w₀ k ω) - setup.toSVRGSetup.gradF wStar‖ ^ 2 ≤
      (L : ℝ) ^ 2 * ‖outerProcess w₀ k ω - wStar‖ ^ 2 := by
    intro ω
    have h := hsmooth.dist_le_mul (outerProcess w₀ k ω) wStar
    calc ‖setup.toSVRGSetup.gradF (outerProcess w₀ k ω) - setup.toSVRGSetup.gradF wStar‖ ^ 2
        ≤ ((L : ℝ) * ‖outerProcess w₀ k ω - wStar‖) ^ 2 := by gcongr; rwa [dist_eq_norm, dist_eq_norm] at h
      _ = (L : ℝ) ^ 2 * ‖outerProcess w₀ k ω - wStar‖ ^ 2 := by ring
  -- Step 3: Integrate the Lipschitz bound
  have h_lip_int : ∫ ω, ‖setup.toSVRGSetup.gradF (outerProcess w₀ k ω) - setup.toSVRGSetup.gradF wStar‖ ^ 2 ∂setup.toSVRGSetup.P ≤
      (L : ℝ) ^ 2 * ∫ ω, ‖outerProcess w₀ k ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.P := by
    calc ∫ ω, ‖setup.toSVRGSetup.gradF (outerProcess w₀ k ω) - setup.toSVRGSetup.gradF wStar‖ ^ 2 ∂setup.toSVRGSetup.P
        ≤ ∫ ω, (L : ℝ) ^ 2 * ‖outerProcess w₀ k ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.P := by
          apply integral_mono _ _ h_lip_bound
          · exact integrable_const _
          · exact h_int_epoch_start.const_mul ((L : ℝ) ^ 2)
      _ = (L : ℝ) ^ 2 * ∫ ω, ‖outerProcess w₀ k ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.P := by
          rw [integral_const_mul]
  -- Step 4: Combine
  calc ∫ ω, ‖outerProcess w₀ (k + 1) ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.P
      ≤ (1 - η * μ) ^ setup.m * ∫ ω, ‖outerProcess w₀ k ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.P +
          η / μ * ∫ ω, ‖setup.toSVRGSetup.gradF (outerProcess w₀ k ω) - setup.toSVRGSetup.gradF wStar‖ ^ 2 ∂setup.toSVRGSetup.P := h_inner_contract
    _ ≤ (1 - η * μ) ^ setup.m * ∫ ω, ‖outerProcess w₀ k ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.P +
          η / μ * ((L : ℝ) ^ 2 * ∫ ω, ‖outerProcess w₀ k ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.P) := by
          gcongr
    _ = ((1 - η * μ) ^ setup.m + η * (L : ℝ) ^ 2 / μ) *
          ∫ ω, ‖outerProcess w₀ k ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.P := by
          ring

/-- Outer-loop linear convergence for SVRG under strong convexity.

Used in: `SVRG outer loop` (Algorithms/SVRGOuterLoop.lean, final theorem) -/
theorem svrg_outer_convergence_strongly_convex
    (f : E → ℝ) {L μ η : ℝ} (wStar : E)
    (hgrad : IsGradientOf f setup.toSVRGSetup.toSGDSetup.gradF)
    (hsmooth : IsLSmooth setup.toSVRGSetup.toSGDSetup.gradF L)
    (hsc : StrongConvexOn Set.univ μ f)
    (hmin : IsMinimizer f wStar)
    (hη_pos : 0 < η) (hημ : η * μ < 1)
    (hρ : (1 - η * μ) ^ setup.m + η * (L : ℝ) ^ 2 / μ < 1)
    (hη : ∀ t, setup.toSVRGSetup.toSGDSetup.η t = η)
    (K : ℕ)
    (h_int_all : ∀ k ≤ K, Integrable (fun ω => ‖outerProcess w₀ k ω - wStar‖ ^ 2) setup.toSVRGSetup.P)
    (h_int_inner_all : ∀ k < K, ∀ t < setup.m, Integrable (fun ω =>
        ‖setup.toSVRGSetup.svrgOracle (outerProcess w₀ k ω) (setup.toSVRGSetup.gradF (outerProcess w₀ k ω))
          (outerProcess w₀ k ω) (setup.ξ_epoch k t ω)‖ ^ 2) setup.toSVRGSetup.P)
    (h_int_inner_norm_sq_all : ∀ k < K, ∀ t < setup.m, Integrable (fun ω =>
        ‖setup.toSVRGSetup.svrgProcess (outerProcess w₀ k ω) (setup.toSVRGSetup.gradF (outerProcess w₀ k ω))
          (fun t => setup.ξ_epoch k t) t ω - wStar‖ ^ 2) setup.toSVRGSetup.P)
    (h_int_inner_inner_all : ∀ k < K, ∀ t < setup.m, Integrable (fun ω =>
        ⟪setup.toSVRGSetup.svrgProcess (outerProcess w₀ k ω) (setup.toSVRGSetup.gradF (outerProcess w₀ k ω))
          (fun t => setup.ξ_epoch k t) t ω - wStar,
          setup.toSVRGSetup.svrgOracle (outerProcess w₀ k ω) (setup.toSVRGSetup.gradF (outerProcess w₀ k ω))
            (setup.toSVRGSetup.svrgProcess (outerProcess w₀ k ω) (setup.toSVRGSetup.gradF (outerProcess w₀ k ω))
              (fun t => setup.ξ_epoch k t) t ω) (setup.ξ_epoch k t ω)⟫_ℝ) setup.toSVRGSetup.P)
    (h_int_inner_gF_all : ∀ k < K, ∀ t < setup.m, Integrable (fun ω =>
        ⟪setup.toSVRGSetup.svrgProcess (outerProcess w₀ k ω) (setup.toSVRGSetup.gradF (outerProcess w₀ k ω))
          (fun t => setup.ξ_epoch k t) t ω - wStar,
          setup.toSVRGSetup.gradF (setup.toSVRGSetup.svrgProcess (outerProcess w₀ k ω)
            (setup.toSVRGSetup.gradF (outerProcess w₀ k ω)) (fun t => setup.ξ_epoch k t) t ω)⟫_ℝ)
      setup.toSVRGSetup.P) :
    ∫ ω, ‖outerProcess w₀ K ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.P ≤
      ((1 - η * μ) ^ setup.m + η * (L : ℝ) ^ 2 / μ) ^ K * ‖w₀ - wStar‖ ^ 2 := by
  set ρ := (1 - η * μ) ^ setup.m + η * (L : ℝ) ^ 2 / μ
  induction K with
  | zero =>
      simp only [outerProcess_zero, integral_const, pow_zero, one_mul]
      rw [integral_const, smul_eq_mul, setup.toSVRGSetup.toSGDSetup.probReal_univ, one_mul]
  | succ K ih =>
      have h_contract := svrg_outer_one_epoch_contraction w₀ f L μ η wStar
        hgrad hsmooth hsc hmin hη_pos hημ hη K
        (h_int_all K (Nat.le_succ K)) (h_int_all (K + 1) (Nat.le_succ K))
        (fun t ht => h_int_inner_all K (Nat.lt_succ_iff.mp ht) t ht)
        (fun t ht => h_int_inner_norm_sq_all K (Nat.lt_succ_iff.mp ht) t ht)
        (fun t ht => h_int_inner_inner_all K (Nat.lt_succ_iff.mp ht) t ht)
        (fun t ht => h_int_inner_gF_all K (Nat.lt_succ_iff.mp ht) t ht)
      calc ∫ ω, ‖outerProcess w₀ (K + 1) ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.P
          ≤ ρ * ∫ ω, ‖outerProcess w₀ K ω - wStar‖ ^ 2 ∂setup.toSVRGSetup.P := h_contract
        _ ≤ ρ * (ρ ^ K * ‖w₀ - wStar‖ ^ 2) := by gcongr
        _ = ρ ^ (K + 1) * ‖w₀ - wStar‖ ^ 2 := by rw [pow_succ]; ring

end SVRGOuterSetup
