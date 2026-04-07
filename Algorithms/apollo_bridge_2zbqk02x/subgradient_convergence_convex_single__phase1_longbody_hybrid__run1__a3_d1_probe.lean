import Main
import Lib.Glue.Algebra
import Lib.Glue.Probability
import Lib.Layer0.IndepExpect
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {S : Type*} [MeasurableSpace S]
variable {Ω : Type*} [MeasurableSpace Ω]
structure SubgradientSetup
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E]
    (S : Type*) [MeasurableSpace S]
    (Ω : Type*) [MeasurableSpace Ω] where
  w₀ : E
  η : ℕ → ℝ
  gradL : E → S → E
  ξ : ℕ → Ω → S
  P : Measure Ω
  hP : IsProbabilityMeasure P
  hξ_meas : ∀ t, Measurable (ξ t)
  hξ_indep : iIndepFun (β := fun _ => S) ξ P
  hξ_ident : ∀ t, IdentDistrib (ξ t) (ξ 0) P P
  hgL : Measurable (Function.uncurry gradL)
noncomputable def SubgradientSetup.process (setup : SubgradientSetup E S Ω) : ℕ → Ω → E
  | 0 => fun _ => setup.w₀
  | t + 1 => fun ω =>
      let w_t := process setup t ω
      w_t - setup.η t • setup.gradL w_t (setup.ξ t ω)
namespace SubgradientSetup
variable (setup : SubgradientSetup E S Ω)
@[simp]
theorem process_zero : process setup 0 = fun _ => setup.w₀ := by
  try norm_cast ; try norm_num ; try simp_all ; try ring_nf at * ; try native_decide ; try linarith ; try nlinarith
  try norm_cast; try norm_num; try simp_all; try ring_nf at *; try native_decide; try linarith; try nlinarith