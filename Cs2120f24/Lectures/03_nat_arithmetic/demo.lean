import Cs2120f24.Library.natArithmetic.semantics

namespace cs2120f24.natArithmetic
/-!
# Our Natural Number Arithmetic Language!
-/

open natArithmetic.syntax

-- some arithmetic literal expressions
def zero : Expr := Expr.lit 0
def one  : Expr := [1]    -- our notation

-- some arithmetic variable expressions
def X : Expr := Expr.var (Var.mk 0)
def Y := {⟨1⟩}    -- notation for same
def Z := {⟨2⟩}    -- etc.
def K := {⟨3⟩}
def M := {⟨4⟩}
def N := {⟨5⟩}

-- an example of the kinds of expressions we can now write
def e0 : Expr := [5]                -- literal expression
def e1 : Expr := X                  -- variable expression
def e2 : Expr := Y                  -- variable expression
def e3 : Expr := Z                  -- variable expression
def e4 : Expr := X + [2]            -- operator (+) expression
def e5 : Expr := X + ([2] * Y) - X  --
def e6 : Expr := X + [2] * Y  - X   --
def e7 : Expr := [2] * Y + X - X    --
def e8 : Expr := [10] - [2] * X     --
def e9 : Expr := [2] * Y - X        --

-- an interpretation: X = 1, Y = 2, Z = 3, rest = 0
def i123 : Var → Nat
| Var.mk 0  => 2    -- X = 2
| ⟨ 1 ⟩     => 5    -- Y = 5
| ⟨ 2 ⟩     => 11   -- Z = 11
| _         => 0

#eval i123 ⟨ 0 ⟩
#eval i123 ⟨ 1 ⟩
#eval i123 ⟨ 2 ⟩
#eval i123 ⟨ 3 ⟩

-- predict values of our six expressions under this interpretation
#eval semantics.evalExpr e0 i123    -- expect 5
#eval semantics.evalExpr e1 i123    -- expect 2
#eval semantics.evalExpr e2 i123    -- expect 5
#eval semantics.evalExpr e3 i123    -- expect 11
#eval semantics.evalExpr e4 i123    -- expect 2 + 2 = 4
#eval semantics.evalExpr e5 i123    -- expect 10
#eval semantics.evalExpr e6 i123    -- expect 10
#eval semantics.evalExpr e7 i123    -- expect 10
#eval semantics.evalExpr e8 i123    -- expect 6
#eval semantics.evalExpr e9 i123    -- expect 6

-- an interpretation: all variables evaluate to zero
def i0 (_ : Var) := 0
#eval semantics.evalExpr e0 i0
#eval semantics.evalExpr e1 i0
#eval semantics.evalExpr e2 i0
#eval semantics.evalExpr e3 i0
#eval semantics.evalExpr e4 i0
#eval semantics.evalExpr e5 i0

-- function: first six *variables* go to given values, rest to 0
def i230463 : Var → Nat
| ⟨ 0 ⟩ => 2          -- X := 2
| ⟨ 1 ⟩ => 3          -- Y := 3
| ⟨ 2 ⟩ => 0          -- Z := 0
| ⟨ 3 ⟩ => 4          -- N := 4
| ⟨ 4 ⟩  => 6          -- M := 6
| ⟨ 5 ⟩  => 3          -- P := 3
| _ => 0               -- any other variable := 0

#eval semantics.evalExpr e0 i230463
#eval semantics.evalExpr e1 i230463
#eval semantics.evalExpr e2 i230463
#eval semantics.evalExpr e3 i230463
#eval semantics.evalExpr e4 i230463
#eval semantics.evalExpr e5 i230463

end cs2120f24.natArithmetic
