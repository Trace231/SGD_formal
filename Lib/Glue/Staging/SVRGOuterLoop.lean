-- Staging lemmas for SVRGOuterLoop formalization.
-- Add new helper lemmas here. Do NOT modify existing Lib/Glue files.
import Lib.Glue.Probability
import Lib.Glue.Algebra
import Lib.Glue.Measurable
import Lib.Glue.Calculus
import Algorithms.SVRG

/-- Measurability of SVRG process with ω-dependent snapshot parameters.

Used in: `outerSnapshot_measurable` (Algorithms/SVRGOuterLoop.lean, successor case) -/
theorem svrgProcess_measurable_random_snapshot
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {S : Type*} [MeasurableSpace S]
    {Ω : Type*} [MeasurableSpace Ω]
    (setup : SVRGSetup E S Ω)
    (wTilde : Ω → E) (gradLTilde : Ω → E)
    (hwTilde_meas : Measurable wTilde)
    (hgradLTilde_meas : Measurable gradLTilde)
    (hgL : Measurable (Function.uncurry setup.toSGDSetup.gradL))
    (t : ℕ) :
    Measurable (fun ω => setup.svrgProcess (wTilde ω) (gradLTilde ω) t ω) := by
  -- This requires establishing joint measurability in (wTilde, gradLTilde, ω)
  -- For now, we use sorry as this is an infrastructure lemma
  sorry
