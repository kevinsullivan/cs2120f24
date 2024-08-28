import Mathlib.Data.Real.Basic


def a_relation (x : ℝ) (_ : x ≥ 0) :=
  { out : ℝ |  x = out * out }
