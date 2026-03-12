-- Staging lemmas for SVRGOuterLoop formalization.
-- Add new helper lemmas here. Do NOT modify existing Lib/Glue files.
import Lib.Glue.Probability
import Lib.Glue.Algebra
import Lib.Glue.Measurable
import Lib.Glue.Calculus
import Algorithms.SVRG

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {S : Type*} [MeasurableSpace S]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Joint measurability of svrgProcess with random snapshot.

If wTilde(ω) and gradLTilde(ω) are measurable functions of ω, then
ω ↦ svrgProcess wTilde(ω) gradLTilde(ω) m ω is measurable.

Used in: `SVRG outer-loop convergence` (Algorithms/SVRGOuterLoop.lean, measurability bridge) -/
theorem svrgProcess_measurable_random_snapshot
    (setup : SVRGSetup E S Ω)
    (w_fun g_fun : Ω → E)
    (hw : Measurable w_fun) (hg : Measurable g_fun)
    (hgL : Measurable (Function.uncurry setup.toSGDSetup.gradL))
    (m : ℕ) :
    Measurable (fun ω => setup.svrgProcess (w_fun ω) (g_fun ω) m ω) := by
  -- Proof: induction on m, using svrgProcess_succ and measurability of arithmetic operations
  -- For m=0, svrgProcess returns w₀ (constant, hence measurable)
  -- For m+1, use the recursive definition and measurability of vector operations
  induction m with
  | zero =>
      -- Base case: svrgProcess wTilde gradLTilde 0 = w₀ (constant)
      simp [SVRGSetup.svrgProcess, SVRGSetup.process_zero]
      exact measurable_const
  | succ m ih =>
      -- Inductive step: use process_succ recursion
      have hξ_meas : Measurable (setup.toSGDSetup.ξ m) := setup.toSGDSetup.hξ_meas m
      -- Composition: ω ↦ (svrgProcess ... m ω, ξ m ω) is measurable
      have h_pair1 : Measurable (fun ω => (setup.svrgProcess (w_fun ω) (g_fun ω) m ω, setup.toSGDSetup.ξ m ω)) :=
        Measurable.prodMk ih hξ_meas
      -- gradL ∘ (pair1) is measurable
      have h_gradL1 : Measurable (fun ω => setup.toSGDSetup.gradL (setup.svrgProcess (w_fun ω) (g_fun ω) m ω) (setup.toSGDSetup.ξ m ω)) :=
        hgL.comp h_pair1
      -- Composition: ω ↦ (w_fun ω, ξ m ω) is measurable
      have h_pair2 : Measurable (fun ω => (w_fun ω, setup.toSGDSetup.ξ m ω)) :=
        Measurable.prodMk hw hξ_meas
      -- gradL ∘ (pair2) is measurable
      have h_gradL2 : Measurable (fun ω => setup.toSGDSetup.gradL (w_fun ω) (setup.toSGDSetup.ξ m ω)) :=
        hgL.comp h_pair2
      -- All components are measurable, so the combination is measurable
      have h_body : Measurable (fun ω =>
          setup.toSGDSetup.gradL (setup.svrgProcess (w_fun ω) (g_fun ω) m ω) (setup.toSGDSetup.ξ m ω)
            - setup.toSGDSetup.gradL (w_fun ω) (setup.toSGDSetup.ξ m ω) + g_fun ω) :=
        h_gradL1.sub h_gradL2 |>.add hg
      -- Scalar multiplication and subtraction preserve measurability
      have h_step : Measurable (fun ω =>
          setup.svrgProcess (w_fun ω) (g_fun ω) m ω
            - setup.toSGDSetup.η m •
              (setup.toSGDSetup.gradL (setup.svrgProcess (w_fun ω) (g_fun ω) m ω) (setup.toSGDSetup.ξ m ω)
                - setup.toSGDSetup.gradL (w_fun ω) (setup.toSGDSetup.ξ m ω) + g_fun ω)) :=
        ih.sub (measurable_const.smul h_body)
      -- Rewrite using process_succ
      have h_eq : (fun ω => setup.svrgProcess (w_fun ω) (g_fun ω) (m + 1) ω) =
          fun ω => setup.svrgProcess (w_fun ω) (g_fun ω) m ω
            - setup.toSGDSetup.η m •
              (setup.toSGDSetup.gradL (setup.svrgProcess (w_fun ω) (g_fun ω) m ω) (setup.toSGDSetup.ξ m ω)
                - setup.toSGDSetup.gradL (w_fun ω) (setup.toSGDSetup.ξ m ω) + g_fun ω) := by
        funext ω
        have h_succ := SVRGSetup.process_succ (wTilde := w_fun ω) (gradLTilde := g_fun ω) (setup := setup) m
        -- h_succ : setup.svrgProcess (w_fun ω) (g_fun ω) (m + 1) = fun ω' => ...
        -- Apply congr_fun to get pointwise equality at ω
        have h_pointwise := congr_fun h_succ ω
        simp only [h_pointwise]
      rw [h_eq]
      exact h_step
