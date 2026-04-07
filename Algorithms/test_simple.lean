import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Basic

-- Three simple theorems with correct Lean 4 / Mathlib v4.28.0 signatures

theorem add_comm_example (a b : ℕ) : a + b = b + a := by ring

theorem sq_nonneg_example (x : ℝ) : 0 ≤ x ^ 2 := by exact sq_nonneg x

theorem le_of_lt_example (a b : ℝ) (h : a < b) : a ≤ b := by exact le_of_lt h
