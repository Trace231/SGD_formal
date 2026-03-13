-- File: Algorithms/AveragedSGD.lean
import Algorithms.SubgradientMethod
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Integral

/-!
# Averaged SGD — Algorithm Layer (Archetype A)

Layer: 2 (concrete algorithm built on SubgradientMethod)

This file formalizes stochastic subgradient descent with ergodic averaging (Archetype A).
The update structure matches SubgradientMethod exactly, but the convergence statement
concerns the averaged iterate `average T = (1/T) * ∑_{t=0}^{T-1} process t` rather than
the final iterate.

## Reduction strategy

The proof reduces to `subgradient_convergence_convex_v2` via Jensen's inequality:
1. Pointwise: `f(average_T ω) ≤ (1/T) ∑_t f(process t ω)` by convexity.
2. Integrate: `E[f(average_T)] ≤ (1/T) ∑_t E[f(w_t)]`.
3. Apply SubgradientMethod theorem to bound RHS.

No new stochastic infrastructure needed — pure convex analysis.
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {S : Type*} [MeasurableSpace S]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Setup for stochastic subgradient descent with ergodic averaging. -/
structure AveragedSGDSetup
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (S : Type*) [MeasurableSpace S]
    (Ω : Type*) [MeasurableSpace Ω] where
  toSubgradientSetup : SubgradientSetup E S Ω

namespace AveragedSGDSetup

variable (setup : AveragedSGDSetup E S Ω)

/-- The underlying stochastic process (same as SubgradientMethod).
Used in: `averaged_sgd_convergence_convex_v2` (Algorithms/AveragedSGD.lean, iterate sequence) -/
noncomputable def process : ℕ → Ω → E :=
  setup.toSubgradientSetup.process

/-- Ergodic average of the first T iterates: `(1/T) * ∑_{t=0}^{T-1} process t`.
Used in: `averaged_sgd_convergence_convex_v2` (Algorithms/AveragedSGD.lean, convergence target) -/
noncomputable def average (T : ℕ) (ω : Ω) : E :=
  (1 / (T : ℝ)) • ∑ t in Finset.range T, setup.process t ω

end AveragedSGDSetup

/-- **Averaged SGD convex convergence** via Jensen's inequality + base theorem.

Layer: 2 | Archetype: A (oracle variant — same update as SubgradientMethod)
Used in: Averaged SGD convex convergence (Algorithms/AveragedSGD.lean, ergodic average bound)

Conclusion:
`E[f(average_T)] - f(w*) ≤ ‖w₀ - w*‖² / (2ηT) + ηG²/2`

where `average_T = (1/T) * ∑_{t=0}^{T-1} w_t` and `w_t` follows stochastic subgradient descent.

Proof outline:
1. Pointwise Jensen: `f(average_T ω) ≤ (1/T) ∑_t f(w_t ω)` (convexity).
2. Subtract optimum: `f(average_T ω) - f(w*) ≤ (1/T) ∑_t (f(w_t ω) - f(w*))`.
3. Integrate: LHS expectation ≤ RHS expectation = (1/T) ∑_t (E[f(w_t)] - f(w*)).
4. Apply `subgradient_convergence_convex_v2` to bound RHS.
-/
theorem averaged_sgd_convergence_convex_v2
    (setup : AveragedSGDSetup E S Ω) (f : E → ℝ) {G η : ℝ} (wStar : E)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hmin : IsMinimizer f wStar)
    (hsubgrad_ineq : ∀ w v, f v ≥ f w + ⟪setup.toSubgradientSetup.subgradF w, v - w⟫_ℝ)
    (hvar : HasBoundedVariance setup.toSubgradientSetup.subgradL setup.toSubgradientSetup.sampleDist G)
    (hunb : IsUnbiased setup.toSubgradientSetup.subgradL setup.toSubgradientSetup.subgradF
              setup.toSubgradientSetup.sampleDist)
    (hη_pos : 0 < η) (hη : ∀ t, setup.toSubgradientSetup.η t = η)
    (T : ℕ) (hT : 0 < T)
    (hsubgrad_meas : Measurable (Function.uncurry setup.toSubgradientSetup.subgradL))
    (h_int_f : ∀ t, Integrable (fun ω => f (setup.process t ω)) setup.toSubgradientSetup.P)
    (h_int_sq : ∀ t, Integrable (fun ω =>
        ‖setup.toSubgradientSetup.subgradL (setup.process t ω) (setup.toSubgradientSetup.ξ t ω)‖ ^ 2)
        setup.toSubgradientSetup.P)
    (h_int_norm_sq : ∀ t, Integrable (fun ω => ‖setup.process t ω - wStar‖ ^ 2) setup.toSubgradientSetup.P)
    (h_int_inner : ∀ t, Integrable (fun ω =>
        ⟪setup.process t ω - wStar, setup.toSubgradientSetup.subgradL (setup.process t ω)
          (setup.toSubgradientSetup.ξ t ω)⟫_ℝ) setup.toSubgradientSetup.P)
    (h_int_gF_inner : ∀ t, Integrable (fun ω =>
        ⟪setup.process t ω - wStar, setup.toSubgradientSetup.subgradF (setup.process t ω)⟫_ℝ)
        setup.toSubgradientSetup.P) :
    ∫ ω, f (setup.average T ω) ∂setup.toSubgradientSetup.P - f wStar ≤
      ‖setup.toSubgradientSetup.w₀ - wStar‖ ^ 2 / (2 * η * T) + η * G ^ 2 / 2 := by
  haveI := setup.toSubgradientSetup.hP
  let P := setup.toSubgradientSetup.P
  -- Step 1: Pointwise Jensen inequality (convex combination weights verified)
  have h_jensen : ∀ ω,
      f (setup.average T ω) ≤ (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, f (setup.process t ω) := by
    intro ω
    apply (convexOn_univ_iff.1 hconvex) (Finset.range T) (fun _ => 1 / (T : ℝ)) (fun t => setup.process t ω)
    · intro t _; exact div_nonneg zero_le_one (by positivity : (0 : ℝ) ≤ (T : ℝ))
    · rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
      field_simp [show (T : ℝ) ≠ 0 from by exact_mod_cast hT.ne.symm]
    · intro t _; exact Set.mem_univ _
  -- Step 2: Subtract optimum & rearrange
  have h_pointwise : ∀ ω,
      f (setup.average T ω) - f wStar ≤
        (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, (f (setup.process t ω) - f wStar) := by
    intro ω
    calc
      f (setup.average T ω) - f wStar
        ≤ (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, f (setup.process t ω) - f wStar := by
          gcongr
          exact h_jensen ω
      _ = (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, (f (setup.process t ω) - f wStar) := by
          rw [Finset.mul_sum]
          congr
          ext t
          ring
  -- Step 3: Integrability of RHS (finite linear combination of integrable terms)
  have h_int_rhs : Integrable (fun ω =>
      (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, (f (setup.process t ω) - f wStar)) P := by
    apply Integrable.const_mul
    apply Finset.integrable_sum
    intro t _; exact (h_int_f t).sub (integrable_const _)
  -- Step 4: Nonnegativity of LHS (minimizer property)
  have h_nonneg : ∀ ω, 0 ≤ f (setup.average T ω) - f wStar :=
    fun ω => sub_nonneg.mpr (hmin (setup.average T ω))
  -- Step 5: Measurability of average (finite sum of measurable iterates)
  have h_meas_avg : Measurable (setup.average T) := by
    unfold AveragedSGDSetup.average
    refine (measurable_const_smul ?_).comp measurable_const
    exact Finset.measurable_sum fun t _ => setup.toSubgradientSetup.process_measurable t hsubgrad_meas
  -- Step 6: Integrability of LHS via domination
  have h_meas_f : Measurable f :=
    hconvex.measurable isOpen_univ
  have h_int_lhs : Integrable (fun ω => f (setup.average T ω) - f wStar) P := by
    refine Integrable.mono h_int_rhs ((h_meas_f.comp h_meas_avg).sub measurable_const) h_pointwise
  -- Step 7: Integrate pointwise bound and apply linearity
  calc
    ∫ ω, f (setup.average T ω) ∂P - f wStar
      = ∫ ω, (f (setup.average T ω) - f wStar) ∂P := by
          rw [integral_sub h_int_lhs (integrable_const _)]
      _ ≤ ∫ ω, ((1 / (T : ℝ)) * ∑ t ∈ Finset.range T, (f (setup.process t ω) - f wStar)) ∂P :=
          integral_mono h_int_lhs h_int_rhs h_pointwise
      _ = (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, ∫ ω, (f (setup.process t ω) - f wStar) ∂P := by
          rw [integral_const_mul, integral_sum fun t _ => (h_int_f t).sub (integrable_const _)]
      _ = (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, (∫ ω, f (setup.process t ω) ∂P - f wStar) := by
          simp [integral_sub, integral_const, probReal_univ]
      _ ≤ ‖setup.toSubgradientSetup.w₀ - wStar‖ ^ 2 / (2 * η * T) + η * G ^ 2 / 2 :=
          subgradient_convergence_convex_v2 setup.toSubgradientSetup f wStar
            hconvex hsubgrad_ineq hvar hunb hη_pos hη T hT
            hsubgrad_meas h_int_f h_int_sq h_int_norm_sq h_int_inner h_int_gF_inner