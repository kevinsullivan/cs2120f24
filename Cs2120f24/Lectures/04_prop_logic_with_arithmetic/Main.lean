import Cs2120f24.Library.propLogicWithArith.semantics

open cs2120f24.natArithmetic.syntax

-- arithmetic *variables*: indexed/distinguished by natural numbers
def v0 : Var := Var.mk 0   -- abstract syntax: see natArithmetic.syntax.Var
def v1 : Var := ⟨ 1 ⟩      -- concrete syntax: see natArithmetic syntax file
def v2 : Var := ⟨ 2 ⟩      -- the 0, 1, 2 here are variable *indices* not values!

/-!
It's crucially important that you not confuse the natural
number *indices* of *variables* with the values that we will
assign to them. The values of these variables will be defined
by interpretations. Different interpretations associate different
natural number values with given *variables*.

It's just as important that you distinguish variables from variable
expressions. Variable expressions are expressions in the language of
natural number arithmetic that we're definining. Each *expression*
is constructed from a *variable.
-/

-- *variable expressions*, each constructed from a distinct *variable*
def N := Expr.var v0        -- abstract syntax: see natArithmetic.syntax.Expr
def M := { v1 }             -- concrete syntax: see natArithmetic.syntax.Expr
def P := { v2 }

/-!
And now that we have a few small *expressions* in hand (the variable
expressions M, N, and P) we can form even larger *expressions* using
available *operators*. Here's an example of a larger expression built
from a smaller one using the "+" operator.
-/

def e1 := N + M

/-!
It's crucially important to understand that we have not yet assigned
natural number values or mneaning to any of the the variables, variable
expressions, or operators that we've defined and used here. It's the role
of *semantics* to assign meanings to such syntactic elements.
-/

open cs2120f24.natArithmetic.semantics


/-!
Here's one possible interpretation (*function* fron variables to values).
The variable with index 0 is associated with the value, 2, etc. Be
sure you understand that an "Interp" is a *function* from *variables*
to values. There can be many different functions of this type.
-/

def i1 : Interp   -- see definition of natArithmetic.semantics.Interp
| Var.mk 0 => 2
| Var.mk 1 => 3
| Var.mk 2 => 5
| _ => 0

-- another possible interpretation: every variable's "value" is 0
def i2 : Interp
| _ => 0          -- v matches *any* variable

-- and one more interpretation
def i3 : Interp
| Var.mk 0 => 1
| Var.mk 1 => 10
| Var.mk 2 => 100
| _ => 0

/-
Now we have a set-up where different interpretation functions
associate different values with different variables. Here we are
applying interpretation functions to variables.
-/

#reduce i1 v0   -- expect 2
#reduce i1 v1   -- expect 3
#reduce i1 v2   -- expect 5

/-!
Remember: variables are not variable *expressions*. The latter are
elements in our language, each of which "contains" (is constructed
from) a variable. To evaluate a variable *expression* we apply our
*expression* evaluation function (here called evalExpr). Here we
evaluate the same *expression* using our different interpretations.
-/

#reduce evalExpr M i1    -- cs2120f24.natArithmetic.semantics.EvalExpr
#reduce evalExpr M i2
#reduce evalExpr M i3

#reduce evalExpr e1 i1    -- cs2120f24.natArithmetic.semantics.EvalExpr
#reduce evalExpr e1 i2
#reduce evalExpr e1 i3
