import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Independence and Expectation Infrastructure for SGD

Key measure-theoretic lemmas connecting independence structure of SGD
with expectation calculations needed for convergence proofs.

## Main results

* `expectation_inner_gradL_eq` — The "unbiased cross-term" identity
* `expectation_norm_sq_gradL_bound` — Bounded variance transfer from ν to P

These formalize the "take expectation" step in textbook SGD proofs.
The proofs require Fubini's theorem and conditional expectation arguments
from Mathlib's probability theory library.
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {S : Type*} [MeasurableSpace S]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Unbiased cross-term identity**.

For `wₜ` independent of `ξₜ` with `E_ν[∇L(w,·)] = ∇f(w)`:
`E[⟪h(wₜ), ∇L(wₜ, ξₜ)⟫] = E[⟪h(wₜ), ∇f(wₜ)⟫]`

Proof sketch: By independence of wₜ and ξₜ,
`E[⟪h(wₜ), ∇L(wₜ, ξₜ)⟫] = E_w[⟪h(w), E_ξ[∇L(w, ξ)]⟫] = E_w[⟪h(w), ∇f(w)⟫]`
using Fubini + unbiasedness. -/
theorem expectation_inner_gradL_eq
    {gradL : E → S → E} {gradF : E → E}
    {P : Measure Ω} {ν : Measure S} [IsProbabilityMeasure P]
    {wt : Ω → E} {ξt : Ω → S}
    (hunb : ∀ w, ∫ s, gradL w s ∂ν = gradF w)
    (h_indep : IndepFun wt ξt P)
    (h_dist : Measure.map ξt P = ν)
    (h : E → E)
    (h_wt_meas : Measurable wt)
    (h_ξt_meas : Measurable ξt) :
    ∫ ω, ⟪h (wt ω), gradL (wt ω) (ξt ω)⟫_ℝ ∂P =
      ∫ ω, ⟪h (wt ω), gradF (wt ω)⟫_ℝ ∂P := by
  sorry

/-- **Bounded variance transfer**: E_P[‖∇L(wₜ, ξₜ)‖²] ≤ σ².

If `E_ν[‖∇L(w, s)‖²] ≤ σ²` for all `w`, then by Fubini and
the pushforward distribution, `E_P[‖∇L(wₜ, ξₜ)‖²] ≤ σ²`. -/
theorem expectation_norm_sq_gradL_bound
    {gradL : E → S → E} {σ : ℝ}
    {P : Measure Ω} {ν : Measure S} [IsProbabilityMeasure P]
    {wt : Ω → E} {ξt : Ω → S}
    (hvar : ∀ w, ∫ s, ‖gradL w s‖ ^ 2 ∂ν ≤ σ ^ 2)
    (h_indep : IndepFun wt ξt P)
    (h_dist : Measure.map ξt P = ν)
    (h_wt_meas : Measurable wt)
    (h_ξt_meas : Measurable ξt) :
    ∫ ω, ‖gradL (wt ω) (ξt ω)‖ ^ 2 ∂P ≤ σ ^ 2 := by
  sorry
