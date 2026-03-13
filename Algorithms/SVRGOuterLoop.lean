import Algorithms.SVRG
import Lib.Glue.Staging.SVRGOuterLoop

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {S : Type*} [MeasurableSpace S]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- SVRG outer-loop setup: manages epoch-to-epoch snapshot updates.

The outer loop runs for `numEpochs` epochs. Each epoch:
1. Computes the full gradient at the snapshot point `wTilde_k`
2. Runs the inner SVRG loop for `innerIters` iterations
3. Sets the next snapshot to the final inner iterate

Used in: `svrg_outer_convergence_strongly_convex` (Algorithms/SVRGOuterLoop.lean, main theorem) -/
structure SVRGOuterSetup
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E]
    (S : Type*) [MeasurableSpace S]
    (Ω : Type*) [MeasurableSpace Ω] where
  innerSetup : SVRGSetup E S Ω
  numEpochs : ℕ
  innerIters : ℕ

namespace SVRGOuterSetup

/-- Snapshot sequence: `outerSnapshot setup k` is the snapshot at epoch `k`.

Defined recursively:
- `outerSnapshot setup 0 = w₀` (initial point)
- `outerSnapshot setup (k+1) = innerLoopResult k (innerIters - 1)` (final inner iterate)

Used in: `svrg_outer_convergence_strongly_convex` (Algorithms/SVRGOuterLoop.lean, main theorem) -/
noncomputable def outerSnapshot (setup : SVRGOuterSetup E S Ω) : ℕ → Ω → E
  | 0 => fun _ => setup.innerSetup.toSGDSetup.w₀
  | k + 1 => fun ω =>
      let wTilde := outerSnapshot setup k ω
      let gradLTilde := setup.innerSetup.toSGDSetup.gradF wTilde
      setup.innerSetup.svrgProcess wTilde gradLTilde setup.innerIters ω

/-- Precomputed full gradient at snapshot for epoch `k`.

`outerGradLTilde setup k ω = gradF (outerSnapshot setup k ω)`

Used in: `svrg_outer_convergence_strongly_convex` (Algorithms/SVRGOuterLoop.lean, main theorem) -/
noncomputable def outerGradLTilde (setup : SVRGOuterSetup E S Ω) : ℕ → Ω → E
  | k => fun ω => setup.innerSetup.toSGDSetup.gradF (outerSnapshot setup k ω)

/-- Outer-loop process: `outerProcess setup k t ω` is the iterate at epoch `k`, inner step `t`.

For epoch `k`, we run the inner SVRG loop with snapshot `outerSnapshot setup k` and
precomputed gradient `outerGradLTilde setup k`.

Used in: `svrg_outer_convergence_strongly_convex` (Algorithms/SVRGOuterLoop.lean, main theorem) -/
noncomputable def outerProcess (setup : SVRGOuterSetup E S Ω) : ℕ → ℕ → Ω → E
  | k, t => fun ω =>
      let wTilde := outerSnapshot setup k ω
      let gradLTilde := outerGradLTilde setup k ω
      setup.innerSetup.svrgProcess wTilde gradLTilde t ω

/-- Measurability of SVRG process with random snapshot.

When the snapshot `wTilde` and precomputed gradient `gradLTilde` are random variables
(measurable functions of `ω`), the inner process remains measurable.

Used in: `outerSnapshot_measurable` (Algorithms/SVRGOuterLoop.lean, line 82) -/
theorem svrgProcess_measurable_random_snapshot
    (setup : SVRGSetup E S Ω)
    (wTildeFun gradLTildeFun : Ω → E)
    (hwTilde : Measurable wTildeFun)
    (hgradLTilde : Measurable gradLTildeFun)
    (hgL : Measurable (Function.uncurry setup.toSGDSetup.gradL))
    (t : ℕ) :
    Measurable (fun ω => setup.svrgProcess (wTildeFun ω) (gradLTildeFun ω) t ω) := by
  induction t with
  | zero =>
      simp [SVRGSetup.svrgProcess]
      exact measurable_const
  | succ t ih =>
      simp [SVRGSetup.svrgProcess, SVRGSetup.svrgOracle, SGDSetup.process_succ]
      -- The update: svrgProcess t ω - η t • (gradL (svrgProcess t ω) (ξ t ω) - gradL wTilde (ξ t ω) + gradLTilde)
      -- Each component is measurable by composition
      have hξ_meas : Measurable (setup.toSGDSetup.ξ t) := setup.toSGDSetup.hξ_meas t
      have h_step_measurable : Measurable (fun ω => setup.svrgProcess (wTildeFun ω) (gradLTildeFun ω) t ω) := ih
      have h_gradL_at_step : Measurable (fun ω => setup.toSGDSetup.gradL (setup.svrgProcess (wTildeFun ω) (gradLTildeFun ω) t ω) (setup.toSGDSetup.ξ t ω)) :=
        hgL.comp (h_step_measurable.prodMk hξ_meas)
      have h_gradL_at_wTilde : Measurable (fun ω => setup.toSGDSetup.gradL (wTildeFun ω) (setup.toSGDSetup.ξ t ω)) :=
        hgL.comp (hwTilde.prodMk hξ_meas)
      have h_oracle : Measurable (fun ω => setup.toSGDSetup.gradL (setup.svrgProcess (wTildeFun ω) (gradLTildeFun ω) t ω) (setup.toSGDSetup.ξ t ω) -
          setup.toSGDSetup.gradL (wTildeFun ω) (setup.toSGDSetup.ξ t ω) + gradLTildeFun ω) :=
        h_gradL_at_step.sub h_gradL_at_wTilde |>.add hgradLTilde
      exact h_step_measurable.sub (h_oracle.const_smul (setup.toSGDSetup.η t))

/-- Measurability of outer snapshot sequence.

Used in: `svrg_outer_convergence_strongly_convex` (Algorithms/SVRGOuterLoop.lean, measurability argument) -/
theorem outerSnapshot_measurable
    (setup : SVRGOuterSetup E S Ω)
    (hgL : Measurable (Function.uncurry setup.innerSetup.toSGDSetup.gradL))
    (hgF : Measurable setup.innerSetup.toSGDSetup.gradF)
    (k : ℕ) :
    Measurable (outerSnapshot setup k) := by
  induction k with
  | zero =>
    simp [outerSnapshot]
  | succ k ih =>
    simp [outerSnapshot, outerGradLTilde]
    exact svrgProcess_measurable_random_snapshot setup.innerSetup (outerSnapshot setup k)
      (setup.innerSetup.toSGDSetup.gradF ∘ outerSnapshot setup k) ih
      (hgF.comp ih) hgL setup.innerIters

/-- Outer-loop strongly-convex convergence theorem.

This theorem bounds the expected squared distance to optimum after `numEpochs` epochs,
where each epoch runs `innerIters` inner iterations.

Used in: `SVRG outer-loop convergence analysis` (Algorithms/SVRGOuterLoop.lean, main result) -/
theorem svrg_outer_convergence_strongly_convex
    (setup : SVRGOuterSetup E S Ω) (f : E → ℝ) {L : NNReal} {μ σeff η : ℝ}
    (wStar : E)
    (hgrad : IsGradientOf f setup.innerSetup.toSGDSetup.gradF)
    (hsmooth : IsLSmooth setup.innerSetup.toSGDSetup.gradF L)
    (hsc : StrongConvexOn Set.univ μ f)
    (hunb : IsUnbiased setup.innerSetup.toSGDSetup.gradL setup.innerSetup.toSGDSetup.gradF
      setup.innerSetup.sampleDist)
    (hmin : IsMinimizer f wStar)
    (h_sample_prob : IsProbabilityMeasure setup.innerSetup.sampleDist)
    (hμ_pos : 0 < μ) (hη_pos : 0 < η) (_hη_L : η ≤ 1 / (L : ℝ))
    (hημ : η * μ < 1) (hη : ∀ t, setup.innerSetup.toSGDSetup.η t = η)
    (h_inner_iters : setup.innerIters > 0)
    (hgL : Measurable (Function.uncurry setup.innerSetup.toSGDSetup.gradL))
    (hgF : Measurable setup.innerSetup.toSGDSetup.gradF)
    (h_intL_base : ∀ w, Integrable (setup.innerSetup.toSGDSetup.gradL w)
      setup.innerSetup.sampleDist)
    (hvar_eff : ∀ k ω, HasBoundedVariance
      (setup.innerSetup.svrgOracle (outerSnapshot setup k ω) (outerGradLTilde setup k ω))
      setup.innerSetup.sampleDist σeff)
    (h_int_sq : ∀ k t, Integrable (fun ω =>
        ‖setup.innerSetup.svrgOracle (outerSnapshot setup k ω) (outerGradLTilde setup k ω)
          (outerProcess setup k t ω) (setup.innerSetup.toSGDSetup.ξ t ω)‖ ^ 2)
      setup.innerSetup.toSGDSetup.P)
    (h_int_norm_sq : ∀ k t, Integrable (fun ω =>
        ‖outerProcess setup k t ω - wStar‖ ^ 2) setup.innerSetup.toSGDSetup.P)
    (h_int_inner : ∀ k t, Integrable (fun ω =>
        ⟪outerProcess setup k t ω - wStar,
          setup.innerSetup.svrgOracle (outerSnapshot setup k ω) (outerGradLTilde setup k ω)
            (outerProcess setup k t ω) (setup.innerSetup.toSGDSetup.ξ t ω)⟫_ℝ)
      setup.innerSetup.toSGDSetup.P)
    (h_int_gF_inner : ∀ k t, Integrable (fun ω =>
        ⟪outerProcess setup k t ω - wStar,
          setup.innerSetup.toSGDSetup.gradF (outerProcess setup k t ω)⟫_ℝ)
      setup.innerSetup.toSGDSetup.P) :
    ∫ ω, ‖outerProcess setup setup.numEpochs 0 ω - wStar‖ ^ 2 ∂setup.innerSetup.toSGDSetup.P ≤
      (1 - η * μ) ^ (setup.numEpochs * setup.innerIters) * ‖setup.innerSetup.toSGDSetup.w₀ - wStar‖ ^ 2
        + (η * σeff ^ 2 / μ) * (1 - (1 - η * μ) ^ setup.numEpochs) / (η * μ) := by
  haveI := setup.innerSetup.toSGDSetup.hP
  -- Key observation: epoch boundary equality
  have h_epoch_boundary : ∀ k, outerProcess setup (k + 1) 0 = outerProcess setup k setup.innerIters := by
    intro k
    ext ω
    simp [outerProcess, outerSnapshot, outerGradLTilde]
  -- Induction on numEpochs
  induction setup.numEpochs with
  | zero =>
      -- Base case: numEpochs = 0
      simp [outerProcess, outerSnapshot]
      -- LHS = ‖w₀ - w*‖²
      -- RHS = (1-ημ)^0 * ‖w₀-w*‖² + (η*σeff²/μ) * (1-1)/(η*μ) = ‖w₀-w*‖²
      have hημ_ne : η * μ ≠ 0 := mul_ne_zero hη_pos.ne' hμ_pos.ne'
      field_simp [hημ_ne]
  | succ numEpochs ih =>
      set k := numEpochs with hk
      -- Epoch boundary rewrite
      have h_boundary : outerProcess setup (k + 1) 0 = outerProcess setup k setup.innerIters :=
        h_epoch_boundary k
      -- Apply inner loop convergence at epoch k
      have h_inner : ∀ ω,
          ∫ ω', ‖setup.innerSetup.svrgProcess (outerSnapshot setup k ω) (outerGradLTilde setup k ω)
              setup.innerIters ω' - wStar‖ ^ 2 ∂setup.innerSetup.toSGDSetup.P ≤
          (1 - η * μ) ^ setup.innerIters * ‖outerSnapshot setup k ω - wStar‖ ^ 2 +
            η * σeff ^ 2 / μ := by
        intro ω
        have h_inner_conv := SVRGSetup.svrg_convergence_inner_strongly_convex
          (setup := setup.innerSetup) (f := f) (wStar := wStar)
          (wTilde := outerSnapshot setup k ω) (gradLTilde := outerGradLTilde setup k ω)
          (hgradLTilde := by simp [outerGradLTilde])
          hgrad hsmooth hsc
          (hvar_eff := hvar_eff k ω)
          hunb hmin h_sample_prob hμ_pos hη_pos _hη_L hημ hη setup.innerIters
          hgL h_intL_base
          (h_intL_eff := fun w => by
            have h1 : Integrable (setup.innerSetup.toSGDSetup.gradL w) setup.innerSetup.sampleDist := h_intL_base w
            have h2 : Integrable (setup.innerSetup.toSGDSetup.gradL (outerSnapshot setup k ω)) setup.innerSetup.sampleDist := h_intL_base _
            have h3 : Integrable (fun s : S => outerGradLTilde setup k ω) setup.innerSetup.sampleDist := integrable_const _
            have h4 : Integrable (fun s : S => setup.innerSetup.toSGDSetup.gradL w s - setup.innerSetup.toSGDSetup.gradL (outerSnapshot setup k ω) s) setup.innerSetup.sampleDist := h1.sub h2
            simpa [SVRGSetup.svrgOracle] using h4.add h3)
          (h_int_sq := fun t => h_int_sq k t)
          (h_int_norm_sq := fun t => h_int_norm_sq k t)
          (h_int_inner := fun t => h_int_inner k t)
          (h_int_gF_inner := fun t => h_int_gF_inner k t)
        simpa [SVRGSetup.svrgProcess] using h_inner_conv
      -- Integrate over ω and chain with induction hypothesis
      calc ∫ ω, ‖outerProcess setup (k + 1) 0 ω - wStar‖ ^ 2 ∂setup.innerSetup.toSGDSetup.P
          = ∫ ω, ‖outerProcess setup k setup.innerIters ω - wStar‖ ^ 2 ∂setup.innerSetup.toSGDSetup.P := by
            rw [h_boundary]
        _ = ∫ ω, ‖setup.innerSetup.svrgProcess (outerSnapshot setup k ω) (outerGradLTilde setup k ω)
              setup.innerIters ω - wStar‖ ^ 2 ∂setup.innerSetup.toSGDSetup.P := by
            simp [outerProcess]
        _ ≤ ∫ ω, ((1 - η * μ) ^ setup.innerIters * ‖outerSnapshot setup k ω - wStar‖ ^ 2 + η * σeff ^ 2 / μ)
              ∂setup.innerSetup.toSGDSetup.P := by
            -- Integrate the pointwise bound from h_inner
            apply integral_mono
            · -- Integrability of LHS
              exact h_int_norm_sq k setup.innerIters
            · -- Integrability of RHS
              apply Integrable.add
              · exact (h_int_norm_sq k 0).const_mul _
              · exact integrable_const _
            · -- Pointwise bound
              exact h_inner
        _ = (1 - η * μ) ^ setup.innerIters * ∫ ω, ‖outerSnapshot setup k ω - wStar‖ ^ 2 ∂setup.innerSetup.toSGDSetup.P
              + η * σeff ^ 2 / μ := by
            rw [integral_add, integral_const_mul]
            <;> simp [integral_const, h_sample_prob]
        _ = (1 - η * μ) ^ setup.innerIters * ∫ ω, ‖outerProcess setup k 0 ω - wStar‖ ^ 2 ∂setup.innerSetup.toSGDSetup.P
              + η * σeff ^ 2 / μ := by
            simp [outerProcess]
        _ ≤ (1 - η * μ) ^ setup.innerIters *
              ((1 - η * μ) ^ (k * setup.innerIters) * ‖setup.innerSetup.toSGDSetup.w₀ - wStar‖ ^ 2 +
                (η * σeff ^ 2 / μ) * (1 - (1 - η * μ) ^ k) / (η * μ)) +
              η * σeff ^ 2 / μ := by
            gcongr
            simpa [hk] using ih
        _ = (1 - η * μ) ^ ((k + 1) * setup.innerIters) * ‖setup.innerSetup.toSGDSetup.w₀ - wStar‖ ^ 2 +
              (η * σeff ^ 2 / μ) * (1 - (1 - η * μ) ^ (k + 1)) / (η * μ) := by
            -- Geometric series algebra
            have hημ_ne : η * μ ≠ 0 := mul_ne_zero hη_pos.ne' hμ_pos.ne'
            simp only [pow_add, pow_mul, mul_add, mul_comm, mul_left_comm]
            field_simp [hημ_ne]
            <;> ring

end SVRGOuterSetup
