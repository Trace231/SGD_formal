import Algorithms.SVRG
import Lib.Glue.Probability
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Basic

/-!
# SVRG Outer Loop Convergence (Archetype B — Macro Structure)

Layer: 2 | Archetype: B (novel multi-epoch structure; no Layer 1 meta-theorem)
Verification target: Full SVRG convergence over K epochs with m steps/epoch.

## Critical design notes
* **Dual integrability hypotheses** (`h_int_norm_sq_outer`, `h_int_norm_sq_inner`) required per GLUE_TRICKS §4b (Archetype B pattern)
* **Resolution A** applied to variance reduction (Convention 5): `svrg_variance_reduction` uses smoothness/convexity bounds, no domain constraint
* **Epoch independence**: `ξ_epoch_indep_blocks` leverages `iIndepFun.of_disjoint_finset` (Pattern H in GLUE_TRICKS §3)
* **Law of total expectation**: Core technique for chaining inner-loop contraction to outer-loop recursion (Pattern I in GLUE_TRICKS §3)

## Documentation updates required after proof completion
* `docs/CATALOG.md`: Add SVRG outer section, update Roadmap table with "SVRG outer" column
* `docs/GLUE_TRICKS.md`: Add Patterns H (epoch independence) and I (nested expectation)
* `docs/METHODOLOGY.md`: Mark Phase 4 complete
* All new lemmas include `Used in:` tags per Convention 4
-/

open MeasureTheory ProbabilityTheory SVRGSetup
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {S : Type*} [MeasurableSpace S]
variable {Ω : Type*} [MeasurableSpace Ω]

-- ============================================================================
-- Epoch infrastructure (Pattern H: Nested Independence)
-- ============================================================================

/-- Epoch-block sample stream: ξ_epoch ξ k m t = ξ (k * m + t).
Used in: `SVRG outer loop convergence` (Algorithms/SVRGOuterLoop.lean, epoch slicing) -/
def ξ_epoch (ξ : ℕ → Ω → S) (k m : ℕ) : ℕ → Ω → S :=
  fun t ω => ξ (k * m + t) ω

/-- Disjoint epoch blocks are independent under iIndepFun.
Used in: `SVRG outer loop convergence` (Algorithms/SVRGOuterLoop.lean, epoch independence) -/
lemma ξ_epoch_indep_blocks
    {ξ : ℕ → Ω → S} {P : Measure Ω}
    (hξ_indep : iIndepFun (β := fun _ => S) ξ P)
    (k₁ k₂ m : ℕ) (h_disj : k₁ ≠ k₂) :
    IndepFun (ξ_epoch ξ k₁ m) (ξ_epoch ξ k₂ m) P := by
  sorry -- LOCAL_ERROR: build failed ℹ [2645/2747] Replayed Lib.Glue.Calculus info: Lib/Glue/Calculus.lean:100:11: Try this: [apply] abel_nf ⚠ [

-- ============================================================================
-- Outer-loop process definition
-- ============================================================================

/-- Outer-loop SVRG process: w_{k+1} = svrgProcess w_k η (ξ_epoch ξ k m) (gradF w_k) m.
Used in: `SVRG outer loop convergence` (Algorithms/SVRGOuterLoop.lean, main recursion) -/
noncomputable def svrgOuterProcess
    (setup : SVRGSetup E S Ω) (k m : ℕ) : Ω → E :=
  Nat.recOn k
    setup.w₀
    (fun k_prev w_k =>
      svrgProcess w_k setup.η setup.gradL (ξ_epoch setup.ξ k_prev m)
        (setup.gradF w_k) m)

/-- Measurability of outer-loop process.
Used in: `SVRG outer loop convergence` (Algorithms/SVRGOuterLoop.lean, process measurability) -/
lemma svrgOuterProcess_measurable
    (setup : SVRGSetup E S Ω) (hgL : Measurable (Function.uncurry setup.gradL))
    (k m : ℕ) : Measurable (svrgOuterProcess setup k m) := by
  sorry

-- ============================================================================
-- Full SVRG convergence theorem (Archetype B macro)
-- ============================================================================

/-- Full SVRG convergence over K epochs (m steps/epoch).
Used in: full SVRG convergence analysis (no downstream usage yet)

Conclusion:
E[‖w_K − w*‖²] ≤ (1−ημ)^{mK} ‖w₀−w*‖² + (ησ²/μ) · (1 − (1−ημ)^{mK}) / (1 − (1−ημ)^m)

Critical hypotheses:
* Dual integrability (GLUE_TRICKS §4b): 
  - h_int_norm_sq_outer : integrability of outer iterate distance
  - h_int_norm_sq_inner : integrability of inner epoch output distance
* hm_pos : 0 < m (avoids division by zero in geometric series denominator)
* Resolution A applied to variance reduction (Convention 5): no domain constraint needed -/
theorem svrg_convergence_outer
    (setup : SVRGSetup E S Ω) (f : E → ℝ) {L μ σ η : ℝ} (wStar : E)
    (hgrad : IsGradientOf f setup.gradF)
    (hsmooth : IsLSmooth setup.gradF ⟨L, by positivity⟩)
    (hsc : StrongConvexOn Set.univ μ f)
    (hvar : HasBoundedVariance setup.gradL setup.sampleDist σ)
    (hunb : IsUnbiased setup.gradL setup.gradF setup.sampleDist)
    (hmin : IsMinimizer f wStar)
    (hμ_pos : 0 < μ) (hη_pos : 0 < η) (hημ : η * μ < 1)
    (hη_L : η ≤ 1 / L) (hm_pos : 0 < m)
    (K m : ℕ)
    (hgL : Measurable (Function.uncurry setup.gradL))
    (h_intL : ∀ w, Integrable (setup.gradL w) setup.sampleDist)
    (h_int_sq : ∀ t, Integrable (fun ω => ‖setup.gradL (setup.process t ω) (setup.ξ t ω)‖ ^ 2) setup.P)
    (h_int_norm_sq_outer : ∀ k, Integrable (fun ω => ‖svrgOuterProcess setup k m ω - wStar‖ ^ 2) setup.P)
    (h_int_norm_sq_inner : ∀ k, Integrable (fun ω =>
        ‖svrgProcess (svrgOuterProcess setup k m ω) setup.η setup.gradL
          (ξ_epoch setup.ξ k m) (setup.gradF (svrgOuterProcess setup k m ω)) m ω - wStar‖ ^ 2)
      setup.P) :
    ∫ ω, ‖svrgOuterProcess setup K m ω - wStar‖ ^ 2 ∂setup.P ≤
      (1 - η * μ) ^ (m * K) * ‖setup.w₀ - wStar‖ ^ 2 +
        (η * σ ^ 2 / μ) * (1 - (1 - η * μ) ^ (m * K)) / (1 - (1 - η * μ) ^ m) := by
  sorry