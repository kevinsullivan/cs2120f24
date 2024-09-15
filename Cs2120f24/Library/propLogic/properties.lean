import Cs2120f24.Lectures.«02_prop_logic».formal.truth_table

namespace cs2120f24

/-!
### Satisfiability

We built a satisfiability checker. The procedure it implements
*decides* whether any propositional logic expression, e, has at
least one interpretation, i, such that (i e) is true. It works
by generating all 2^n intepretation for any set of n propositional
variables, evaluating the expression under each interpretation,
then returning true if and only if any of the results are true.

With the same underlying machinery we can easily implement what
we will *decision procedures* that similarly answer two similar
questions: does a given expression, e, have the *property* of
being *unsatisfiable?* And does "e" have the property of being
*valid*.
-/

/-!
## Decision Procedures for Properties of PL Expressions
-/

/-!
INTERFACE
-/

/-!
Satisfiability means there's *some* interpretation for which e is true
-/
def is_sat :    PLExpr → Bool :=
  λ e : PLExpr => reduce_or (truthTableOutputs e)

/-!
Validity means that a proposition is true under all interpretations
-/
def is_valid :  PLExpr → Bool :=
  λ e : PLExpr => reduce_and (truthTableOutputs e)

def is_unsat : PLExpr → Bool :=
  λ e : PLExpr => not (is_sat e)

def is_model : BoolInterp → PLExpr → Bool :=
  fun i e => evalPLExpr e i

end cs2120f24
