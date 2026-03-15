-- Staging lemmas for SubgradientMethod formalization.
-- Add new helper lemmas here. Do NOT modify existing Lib/Glue files.
import Lib.Glue.Probability
import Lib.Glue.Algebra
import Lib.Glue.Measurable
import Lib.Glue.Calculus

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

/-- Bound expected squared norm of composed oracle by G² using pointwise bound.
Direct proof: pointwise bound → integral_mono → integral_const → measure_univ.
Used in: `subgradient_convergence_convex` step A5 (variance bound for gradL∘(wt,ξt)). -/
theorem process_composition_expected_sq_norm_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {S : Type*} [MeasurableSpace S] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {gradL : E → S → E} {wt : Ω → E} {ξt : Ω → S} {G : ℝ}
    (hbounded : ∀ w s, ‖gradL w s‖ ≤ G)
    (h_wt_meas : Measurable wt)
    (h_ξt_meas : Measurable ξt)
    (hgL : Measurable (Function.uncurry gradL))
    (h_int : Integrable (fun ω => ‖gradL (wt ω) (ξt ω)‖ ^ 2) P) :
    ∫ ω, ‖gradL (wt ω) (ξt ω)‖ ^ 2 ∂ P ≤ G ^ 2 := by sorry
