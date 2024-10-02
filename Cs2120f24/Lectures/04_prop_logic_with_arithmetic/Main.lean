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
def M := Expr.var v0  -- concrete syntax: see natArithmetic.syntax.Expr
def N := { v1 }       -- abstract syntax: see natArithmetic.syntax.Expr
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

-- Examples: evaluating variable expressions
-- cs2120f24.natArithmetic.semantics.EvalExpr
#reduce evalExpr M i1
#reduce evalExpr M i2
#reduce evalExpr M i3

-- Examples: evaluating operator expressions
#reduce evalExpr e1 i1    -- cs2120f24.natArithmetic.semantics.EvalExpr
#reduce evalExpr e1 i2
#reduce evalExpr e1 i3

def e4 : Expr := sorry + sorry  -- the arguments can by any *expressions*
def e4' : Expr := (M + N) + P
def e4'' : Expr :=
  Expr.binOp                  -- bin op expr
    BinOp.add                 -- op = +
      (Expr.binOp               -- e1 = (M + N)
        BinOp.add                 -- (op = +
        (Expr.var (Var.mk 0))     --  e1 = M
        (Expr.var (Var.mk 1)))    --  e2 = N
      (Expr.var (Var.mk 2))     -- e2 = P

/-!
You should now be able to understand
our syntax for *relational* expressions.

Its formal specification of the syntax of
our language is given by RelExpr. Speaking
informally, the syntax has only one form
of expression, namely "l op r", where op
is a relational operator (such as ≤), and
l and r are *arithmetic* expressions. An
example in the ordinary language of sixth
grade math: 3 < X: There is an arithmetic
literal expression on the left, variable
expresion on the right, and the relational
operator in the middle (infix notation).
-/

def r1 := (M ≤ [20])  -- var_expr op lit_expr
def r1' :=            -- its abstract syntax
  RelExpr.mk
    RelOp.le                -- ≤
    (Expr.var (Var.mk 0))     -- M
    (Expr.lit 20)             -- 20

def r2 : RelExpr := (M > N)

/-
Semantic evaluation, yielding Bool, is by
application of evalRelExpr to an expression
and a specific interpretation of the variables.
-/

-- evalating relational expressions under varying interpretations

#eval evalRelExpr r1 i1 -- 10 < 20, expect true
#eval evalRelExpr r1 i2
#eval evalRelExpr r1 i3

#eval evalRelExpr r2 i1
#eval evalRelExpr r2 i2
#eval evalRelExpr
        r2
        i3

#eval evalRelExpr       -- expect false
        ((M + N) > (N + M))
        i3

#eval evalRelExpr         -- expect false
        ([20] ≥ (N * P))  -- relational expression
        i3                -- arithmetic variable interpretation

/-!
O. M. Gosh, Yay. We now have a working formal specification
of a little expression language of natural number arithmetic.

Our specification defines both syntax (the Expr and RelExpr)
types, and an operational semantics (the evalPLAExpr function).
Given *any* expression and *any* variable interpretation, this
function actually "operates (works!)" to compute the meaning /
valye of the expression given an added interpretation function.
That's why we call it an "operational" semantics.

A hypothetical user of our little expression language would
generally want to write numerical and relational expression
using our concrete syntax, rather than using abstract syntax.

But you are not just a language user but a language designer!
In this capacity, you really must understand how expressions
using concrete syntax get "desugared" into abstract syntactic
expression. See the example, def e4' : Expr := (M + N) + P, a
few paragraphs back.
-/
