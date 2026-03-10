import Main
import Algorithms.SVRG
import Lib.Glue.Measurable
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {S : Type*} [MeasurableSpace S]
variable {Ω : Type*} [MeasurableSpace Ω]

/-! SVRG Outer-Loop Convergence (Archetype B) -/

-- MINIMAL SCAFFOLD: Safe JSON creation
-- Next: Apply PATCH 1 to inject full theorem scaffold
def shift_xi (ξ : ℕ → Ω → S) (offset : ℕ) : ℕ → Ω → S :=
  fun t ω => ξ (offset + t) ω

def ξ_epoch (ξ : ℕ → Ω → S) (k m : ℕ) : ℕ → Ω → S :=
  shift_xi ξ (k * m)

noncomputable def svrgOuterProcess
    (w₀ : E) (η : ℝ) (gradL : E → S → E) (gradF : E → E)
    (ξ : ℕ → Ω → S) (m : ℕ) : ℕ → Ω → E
  | 0, _ => w₀
  | k + 1, ω => svrgProcess
      (svrgOuterProcess w₀ η gradL gradF ξ m k ω)
      η
      (svrgOuterProcess w₀ η gradL gradF ξ m k ω)
      (gradF (svrgOuterProcess w₀ η gradL gradF ξ m k ω))
      (ξ_epoch ξ k m)
      m
      ω

@[simp]
theorem svrgOuterProcess_zero
    (w₀ : E) (η : ℝ) (gradL : E → S → E) (gradF : E → E)
    (ξ : ℕ → Ω → S) (m : ℕ) :
    svrgOuterProcess w₀ η gradL gradF ξ m 0 = fun _ => w₀ := rfl

/-- Shift sample stream by offset for epoch blocking.
Used in: ξ_epoch (Algorithms/SVRGOuterLoop.lean, sample stream blocking for epoch isolation) -/
def shift_xi (ξ : ℕ → Ω → S) (offset : ℕ) : ℕ → Ω → S :=
  fun t ω => ξ (offset + t) ω

/-- Sample stream for inner epoch starting at outer index k with length m.
Used in: svrgOuterProcess, svrg_outer_to_inner_hyps (Algorithms/SVRGOuterLoop.lean, epoch sample stream construction) -/
def ξ_epoch (ξ : ℕ → Ω → S) (k m : ℕ) : ℕ → Ω → S :=
  shift_xi ξ (k * m)

/-- Outer-loop SVRG process: w_{k+1} = result of inner epoch starting at w_k with snapshot w_k.
MUST 2: Explicitly reuses svrgProcess for inner epochs.
Used in: SVRG outer-loop convergence analysis (Algorithms/SVRGOuterLoop.lean, macro recursion definition) -/
noncomputable def svrgOuterProcess
    (w₀ : E) (η : ℝ) (gradL : E → S → E) (gradF : E → E)
    (ξ : ℕ → Ω → S) (m : ℕ) : ℕ → Ω → E
  | 0, _ => w₀
  | k + 1, ω => svrgProcess
      (svrgOuterProcess w₀ η gradL gradF ξ m k ω)
      η
      (svrgOuterProcess w₀ η gradL gradF ξ m k ω)
      (gradF (svrgOuterProcess w₀ η gradL gradF ξ m k ω))
      (ξ_epoch ξ k m)
      m
      ω

/-- Initial condition for outer-loop process.
Used in: svrg_convergence_outer base case (Algorithms/SVRGOuterLoop.lean, initial condition) -/
@[simp]
theorem svrgOuterProcess_zero
    (w₀ : E) (η : ℝ) (gradL : E → S → E) (gradF : E → E)
    (ξ : ℕ → Ω → S) (m : ℕ) :
    svrgOuterProcess w₀ η gradL gradF ξ m 0 = fun _ => w₀ := rfl

/-- Measurability of outer-loop process (induction using svrgProcess_measurable).
Used in: svrg_convergence_outer bridge (Algorithms/SVRGOuterLoop.lean, measurability chain for outer process) -/
theorem svrgOuterProcess_measurable
    {w₀ : E} {η : ℝ} {gradL : E → S → E} {gradF : E → E}
    {ξ : ℕ → Ω → S} {m : ℕ}
    (hξ_meas : ∀ t, Measurable (ξ t))
    (hgL : Measurable (Function.uncurry gradL))
    (hgF_meas : Measurable gradF)
    (k : ℕ) :
    Measurable (svrgOuterProcess w₀ η gradL gradF ξ m k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
      simp only [svrgOuterProcess]
      have h_svrg_meas : Measurable (fun p : E × E × (ℕ → Ω → S) × ℕ × Ω =>
        svrgProcess p.1 p.2.1 p.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
        exact measurable_svrgProcess
      have h_args_meas : Measurable (fun ω =>
        (svrgOuterProcess w₀ η gradL gradF ξ m k ω,
         η,
         svrgOuterProcess w₀ η gradL gradF ξ m k ω,
         gradF (svrgOuterProcess w₀ η gradL gradF ξ m k ω),
         ξ_epoch ξ k m,
         m,
         ω)) := by
        refine ih.prodMk ?_ |>.prodMk ?_ |>.prodMk ?_ |>.prodMk ?_ |>.prodMk ?_ |>.prodMk measurable_const
        · exact measurable_const
        · exact ih
        · exact hgF_meas.comp ih
        · exact measurable_ξ_epoch hξ_meas k m
      exact h_svrg_meas.comp h_args_meas

private theorem measurable_ξ_epoch
    {ξ : ℕ → Ω → S} (hξ_meas : ∀ t, Measurable (ξ t)) (k m : ℕ) :
    ∀ t, Measurable ((ξ_epoch ξ k m) t) := by
  intro t; simp [ξ_epoch, shift_xi]; exact hξ_meas (k * m + t)

/-- Outer-loop process is adapted to natural filtration (reuses sgdFiltration).
Used in: svrgOuterProcess_indepFun_xi_epoch (Algorithms/SVRGOuterLoop.lean, filtration argument foundation) -/
theorem svrgOuterProcess_adapted
    {w₀ : E} {η : ℝ} {gradL : E → S → E} {gradF : E → E}
    {ξ : ℕ → Ω → S} {m : ℕ} {P : Measure Ω}
    (hξ_meas : ∀ t, Measurable (ξ t))
    (hgL : Measurable (Function.uncurry gradL))
    (hgF_meas : Measurable gradF) :
    Adapted (sgdFiltration ξ hξ_meas) (fun k => svrgOuterProcess w₀ η gradL gradF ξ m k) := by
  intro k
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
      simp only [svrgOuterProcess]
      have h_wk : Measurable[sgdFiltration ξ hξ_meas (k + 1)] (svrgOuterProcess w₀ η gradL gradF ξ m k) :=
        ih.mono ((sgdFiltration ξ hξ_meas).mono (Nat.le_succ k)) le_rfl
      have h_gradF_wk : Measurable[sgdFiltration ξ hξ_meas (k + 1)] (fun ω => gradF (svrgOuterProcess w₀ η gradL gradF ξ m k ω)) :=
        hgF_meas.comp h_wk
      have h_xi_epoch_meas : ∀ t, Measurable[sgdFiltration ξ hξ_meas (k + 1)] ((ξ_epoch ξ k m) t) := by
        intro t
        rw [measurable_iff_comap_le]
        exact le_iSup₂_of_le (k * m + t) (by linarith) le_rfl
      have h_svrg_adapted : Adapted (sgdFiltration (ξ_epoch ξ k m) (measurable_ξ_epoch hξ_meas k m))
          (fun t => svrgProcess
            (svrgOuterProcess w₀ η gradL gradF ξ m k ω)
            η
            (svrgOuterProcess w₀ η gradL gradF ξ m k ω)
            (gradF (svrgOuterProcess w₀ η gradL gradF ξ m k ω))
            (ξ_epoch ξ k m)
            m) := by
        exact svrgProcess_adapted hgL hgF_meas (ξ_epoch ξ k m) (fun t _ => h_xi_epoch_meas t)
      exact (h_svrg_adapted 0).comp (h_wk.prodMk (h_gradF_wk.prodMk measurable_prod))

/-- Independence: snapshot at epoch start is independent of entire inner sample block.
Critical for tower property argument in svrg_epoch_contraction.
Used in: svrg_epoch_contraction (Algorithms/SVRGOuterLoop.lean, tower property via snapshot-epoch independence) -/
lemma svrgOuterProcess_indepFun_xi_epoch_strong
    {w₀ : E} {η : ℝ} {gradL : E → S → E} {gradF : E → E}
    {ξ : ℕ → Ω → S} {m : ℕ} {P : Measure Ω}
    (hξ_meas : ∀ t, Measurable (ξ t))
    (hξ_indep : iIndepFun (β := fun _ => S) ξ P)
    (hgL : Measurable (Function.uncurry gradL))
    (hgF_meas : Measurable gradF)
    (k : ℕ) :
    IndepFun
      (svrgOuterProcess w₀ η gradL gradF ξ m k)
      (fun ω => fun t : Fin m => (ξ_epoch ξ k m) t ω)
      P := by
  set F := sgdFiltration ξ hξ_meas with hF_def
  have h_adapted : Measurable[F (k * m)] (svrgOuterProcess w₀ η gradL gradF ξ m k) :=
    svrgOuterProcess_adapted hξ_meas hgL hgF_meas k |>.mono
      (by simp [hF_def, sgdFiltration]; exact iSup₂_mono' fun j hj => ⟨j, hj, le_rfl⟩) le_rfl
  have h_comap_le : (inferInstance : MeasurableSpace E).comap (svrgOuterProcess w₀ η gradL gradF ξ m k) ≤ F (k * m) :=
    measurable_iff_comap_le.mp h_adapted
  have h_iIndep : iIndep (fun i => (inferInstance : MeasurableSpace S).comap (ξ i)) P := hξ_indep
  have h_disj : Disjoint ({j : ℕ | j < k * m}) ({j : ℕ | k * m ≤ j ∧ j < (k + 1) * m}) :=
    Set.disjoint_left.mpr fun j hj hk => absurd (hk.1 ▸ hj) (Nat.lt_irrefl _)
  have h_le : ∀ i, (inferInstance : MeasurableSpace S).comap (ξ i) ≤ mΩ := fun i => (hξ_meas i).comap_le
  have h_F_k : F (k * m) = ⨆ j ∈ {j : ℕ | j < k * m}, (inferInstance : MeasurableSpace S).comap (ξ j) := by
    simp [hF_def, sgdFiltration, Set.mem_setOf_eq]
  have h_block_sigma : (⨆ t : Fin m, (inferInstance : MeasurableSpace S).comap ((ξ_epoch ξ k m) t)) =
      ⨆ j ∈ {j : ℕ | k * m ≤ j ∧ j < (k + 1) * m}, (inferInstance : MeasurableSpace S).comap (ξ j) := by
    simp [ξ_epoch, shift_xi, Set.mem_Ico]; congr; ext; simp
  have h_indep_blocks : Indep (F (k * m)) (⨆ t : Fin m, (inferInstance : MeasurableSpace S).comap ((ξ_epoch ξ k m) t)) P := by
    rw [h_F_k, h_block_sigma]
    exact indep_iSup_of_disjoint h_le h_iIndep h_disj
  exact indep_of_indep_of_le_left h_indep_blocks h_comap_le

/-- Bridge: For fixed snapshot value w_snap, construct valid SVRGSetup for inner epoch.
MUST 3: Verifies inner-loop hypotheses hold pointwise for random snapshot.
Used in: svrg_epoch_contraction (Algorithms/SVRGOuterLoop.lean, pointwise inner-loop setup for random snapshot) -/
noncomputable def svrg_outer_to_inner_hyps
    {setup : SGDSetup E S Ω} {m : ℕ} {k : ℕ} {w_snap : E}
    (hvar_inner : HasBoundedVariance' (svrgOracle w_snap (setup.gradF w_snap)) setup.sampleDist σ_eff)
    (hgL : Measurable (Function.uncurry setup.gradL))
    (hgF_meas : Measurable setup.gradF)
    (hunb : IsUnbiased setup.gradL setup.gradF setup.sampleDist) :
    SVRGSetup E S Ω where
  toSGDSetup := {
    w₀ := w_snap,
    η := fun t => if t < m then setup.η t else 0,
    gradL := setup.gradL,
    gradF := setup.gradF,
    ξ := ξ_epoch setup.ξ k m,
    P := setup.P,
    hP := setup.hP,
    hξ_meas := fun t => setup.hξ_meas (k * m + t),
    hξ_indep := iIndepFun.of_set (fun i => setup.ξ (k * m + i)) setup.hξ_indep (Set.Iio m),
    hξ_ident := fun t => setup.hξ_ident (k * m + t)
  }
  wTilde := w_snap
  gradLTilde := setup.gradF w_snap

/-- One-step epoch contraction: E[‖w_{k+1}−w*‖²] ≤ (1−ημ)^m E[‖w_k−w*‖²] + ησ_eff²/μ.
MUST 1: Uses dual integrability hypotheses (h_int_virtual for snapshot state, h_int_norm_sq for post-epoch state).
MUST 5: Variance hypothesis structured as ∀ w_snap, HasBoundedVariance' (svrgOracle ...) ν σ_eff.
Convention 5 Resolution B: σ_eff depends on domain bound R (documented in svrg_convergence_outer).
Proof strategy: Product measure factorization pattern from expectation_inner_gradL_eq (IndepExpect.lean, Pattern D).
Used in: svrg_convergence_outer (Algorithms/SVRGOuterLoop.lean, Step 1 — epoch-wise contraction) -/
theorem svrg_epoch_contraction
    {setup : SGDSetup E S Ω} {f : E → ℝ} {μ σ_eff η : ℝ} {wStar : E} {m : ℕ}
    (hsc : StrongConvexOn Set.univ μ f)
    (hgrad : IsGradientOf f setup.gradF)
    (hmin : IsMinimizer f wStar)
    (hμ_pos : 0 < μ)
    (hη_pos : 0 < η)
    (hημ : η * μ < 1)
    (hvar_inner : ∀ w_snap, HasBoundedVariance' (svrgOracle w_snap (setup.gradF w_snap)) setup.sampleDist σ_eff)
    (hunb : IsUnbiased setup.gradL setup.gradF setup.sampleDist)
    (hR : ∀ k ω, ‖svrgOuterProcess setup.w₀ η setup.gradL setup.gradF setup.ξ m k ω - wStar‖ ≤ R)
    (h_int_virtual : ∀ k, Integrable (fun ω => ‖svrgOuterProcess setup.w₀ η setup.gradL setup.gradF setup.ξ m k ω - wStar‖ ^ 2) setup.P)
    (h_int_norm_sq : ∀ k, Integrable (fun ω => ‖svrgOuterProcess setup.w₀ η setup.gradL setup.gradF setup.ξ m (k + 1) ω - wStar‖ ^ 2) setup.P)
    (hgL : Measurable (Function.uncurry setup.gradL))
    (hgF_meas : Measurable setup.gradF)
    (k : ℕ) :
    ∫ ω, ‖svrgOuterProcess setup.w₀ η setup.gradL setup.gradF setup.ξ m (k + 1) ω - wStar‖ ^ 2 ∂setup.P ≤
      (1 - η * μ) ^ m * ∫ ω, ‖svrgOuterProcess setup.w₀ η setup.gradL setup.gradF setup.ξ m k ω - wStar‖ ^ 2 ∂setup.P +
      η * σ_eff ^ 2 / μ := by
  sorry

/-- Full SVRG convergence over K outer epochs.
Archetype B: Outer-loop structure differs from SGD (snapshot updates every m steps).
Convention 5 Resolution B: Effective variance σ_eff depends on domain bound R via
  σ_eff² = 4L(f(w_snap) - f*) + 2‖∇F(w_snap) - ∇F(w*)‖² ≤ C(R) (bounded by hR hypothesis).
Used in: SVRG full convergence rate derivation (Algorithms/SVRGOuterLoop.lean, macro-level guarantee) -/
theorem svrg_convergence_outer
    {setup : SGDSetup E S Ω} {f : E → ℝ} {μ σ_eff η : ℝ} {wStar : E} {m K : ℕ}
    (hsc : StrongConvexOn Set.univ μ f)
    (hgrad : IsGradientOf f setup.gradF)
    (hmin : IsMinimizer f wStar)
    (hμ_pos : 0 < μ)
    (hη_pos : 0 < η)
    (hημ : η * μ < 1)
    (hvar_inner : ∀ w_snap, HasBoundedVariance' (svrgOracle w_snap (setup.gradF w_snap)) setup.sampleDist σ_eff)
    (hunb : IsUnbiased setup.gradL setup.gradF setup.sampleDist)
    (hR : ∀ k ω, ‖svrgOuterProcess setup.w₀ η setup.gradL setup.gradF setup.ξ m k ω - wStar‖ ≤ R)
    (h_int_virtual : ∀ k, Integrable (fun ω => ‖svrgOuterProcess setup.w₀ η setup.gradL setup.gradF setup.ξ m k ω - wStar‖ ^ 2) setup.P)
    (h_int_norm_sq : ∀ k, Integrable (fun ω => ‖svrgOuterProcess setup.w₀ η setup.gradL setup.gradF setup.ξ m (k + 1) ω - wStar‖ ^ 2) setup.P)
    (hgL : Measurable (Function.uncurry setup.gradL))
    (hgF_meas : Measurable setup.gradF) :
    ∫ ω, ‖svrgOuterProcess setup.w₀ η setup.gradL setup.gradF setup.ξ m K ω - wStar‖ ^ 2 ∂setup.P ≤
      (1 - η * μ) ^ (m * K) * ‖setup.w₀ - wStar‖ ^ 2 +
      (η * σ_eff ^ 2 / μ) * (1 - (1 - η * μ) ^ (m * K)) / (1 - (1 - η * μ) ^ m) := by
  sorry