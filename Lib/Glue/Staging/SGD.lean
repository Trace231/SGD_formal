import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Abel

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Used-in: SGD convergence theorems. -/
theorem sgd_glue_trivial (x : E) : x = x := by congr 1
