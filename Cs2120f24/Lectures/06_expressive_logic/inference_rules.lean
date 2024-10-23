
/-!
## Summary
-/

/-
OR
-/
inductive OneOfThemIsFromCville : Type where
| intro_left  (k : K)
| intro_right (c : C)

def one : OneOfThemIsFromCville := OneOfThemIsFromCville.intro_left pfK
def other : OneOfThemIsFromCville := OneOfThemIsFromCville.intro_right pfC


/-!
NOT
-/

inductive KevinIsFromFinland : Type where
