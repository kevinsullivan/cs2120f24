import Mathlib.Data.Real.Basic

/-
An abstract specification, written in the logic
of the Lean prover. The function, a_relation, is
defined to take any *real* number, x, as an input
along with an unnamed "certificate" that provides
assurance that x ≥ 0, and it then returns the set
of values possible for a variable, out, where out
squared equals x and out is non-negative.

-/
def a_relation (x : ℝ) (_ : x ≥ 0) :=
  { out : ℝ |  (x = out ^ 2) ∧ (x ≥ 0) }
