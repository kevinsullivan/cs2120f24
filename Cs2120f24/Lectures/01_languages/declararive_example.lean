import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith.Frontend

namespace cs2120f24

/-
Declarative Specification

An abstract specification, written in the logic
of the Lean prover. The function, a_relation, is
defined to take any *real* number, x, as an input
along with an unnamed "certificate" that provides
assurance that x ≥ 0, and it then returns the set
of values possible for a variable, out, where out
squared equals x and out is non-negative.
-/

def sqrt (x : ℚ) (_ : x ≥ (0:ℚ)) :=
  { out : ℝ |  (out * out = x) ∧ (x ≥ 0) }  -- bug!

/-
Logical Reasoning (optional, no need to read this)

Just because you write in mathematical logic doesn't
mean that you can't make dumb mistakes. Here we have
not an implementation bug but a specification bug. Do
you see it? The consequence is that the relation we're
defining here includes negative square roots.
-/

/-
A declarative specification doesn't compute answers,
like our imperative, Python, program actually does.
Rather, it leaves it it to you to verify, by forming
a proof, that any give pair of values satisfies the
specific condition that defines what pairs (here of
values of the argument, x, and the variable, out.

In particular, we'll show that (4, 2) is in the set
of "square root pairs", but that (4, -2) is also in
the set, even though we said we wanted only positive
square roots for any given non-negative input value
for x.

-/

theorem sqrt_4_2 : sqrt 4 (by linarith) 2 := by
  unfold sqrt
  simp
  show 2 ∈ {out | out * out = 4}
  simp
  linarith

theorem sqrt_4_neg2 : sqrt 4 (by linarith) (-2) := by
  unfold sqrt
  simp
  show (-2) ∈ {out | out * out = 4}
  simp
  linarith

  /-
  Note however that, although it has a bug, the
  specification doesn't permit a proof of the false
  assertion that nine has two as a square root. Here
  is how we'd write that assertion. When we try to
  provie it, however, we get stuck. The rules of
  inference and arithmetic don't let us prove that
  2 * 2 = 9.
  -/

/-
theorem sqrt_9_2 : sqrt (9:ℚ) (by linarith) 2 := by
  unfold sqrt
  simp
  show 2 ∈ {out | out * out = 9}
  simp
-/

end cs2120f24
