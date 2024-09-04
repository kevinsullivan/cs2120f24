import Cs2120f24.Lectures.«02_prop_logic».formal.interpretation
import Cs2120f24.Lectures.«02_prop_logic».formal.properties
import Cs2120f24.Lectures.«02_prop_logic».formal.utilities

namespace cs2120f24

open PLExpr


/-!
SYNTAX
-/

-- Variables
def v₀ : BoolVar := BoolVar.mk 0
def v₁ : BoolVar := ⟨1⟩   -- Lean for structure constructor (mk)
def v₂ : BoolVar := ⟨2⟩

/-!
Variable expressions
-/
def P : PLExpr := PLExpr.var_expr v₀
def Q : PLExpr := { v₁ }  -- our notation for var_expr constructor
def R : PLExpr := { v₂ }

/-
Operator expression: abstract syntax
-/

def P_and_Q_abstract : PLExpr :=
  (PLExpr.bin_op_expr BinOp.and P Q)

-- Exact same expression using standard notation
def P_and_Q_concrete := P ∧ Q

-- de-sugars to the underlying astract syntax
#reduce P_and_Q_concrete


/-!
INTERPRETATIONS

The apparent ordering is off, backwards from
what we'd expect. For now it doesn't matter.
We've got it on our list of things to fix.
This example counts the number of variables in
(P ∧ Q), it's 2, and a list of all 2^2 = 4
possible interpretations for that expression
are returned.
-/
#reduce listListStringFromListInterps
          (listInterpsFromExpr (P ∧ Q))
          2
/-!
It's often helpful to list arguments
to functions properly indented across
multiple lines.
-/



/-!
TRUTH TABLES (output vectors). The returned
list is the semantic meaning of the single
given expression under each ]interpretation,
starting with all true and descending to all
false. (We have a note to clean this up.)
-/

#eval! (truthTableOutputVector (P))
#eval! (truthTableOutputVector (P ∧ Q))


/-!
Properties of Propositions (Expressions)!
-/

#reduce is_sat ⊤
#reduce is_sat ⊥

#reduce is_sat P
#reduce is_unsat P
#reduce is_valid P

#reduce is_sat ¬P
#reduce is_unsat ¬P
#reduce is_valid ¬P

#reduce is_sat (P ∨ ¬P)
#reduce is_unsat (P ∨ ¬P)
#reduce is_valid (P ∨ ¬P)

#reduce is_sat (P ∧ ¬P)
#reduce is_unsat (P ∧ ¬P)
#reduce is_valid (P ∧ ¬P)

#reduce is_sat (P ∧ Q)
#reduce is_unsat (P ∧ Q)
#reduce is_valid (P ∧ Q)

#reduce is_sat (P ∨ Q)
#reduce is_unsat (P ∨ Q)
#reduce is_valid (P ∨ Q)


/-!
Homework #1

1.Complete the sentence: If a proposition is not valid,
then there is at least one __________.

2. Read the following propositions in English and render
them into the formal language of propositional logic. We
will get you started by defining three new propositional
variables: isRaining, streetWet, and sprinklerOn. Now for
each of the following propositions expressed in English,
express it formally using these PL variable expressions.
Here then are our three new PL variable expressions. The
identifer's we're binding to these terms remind us what
we are going to want these terms to mean "in the world."
-/

def itsRaining : PLExpr := PLExpr.var_expr v₀
def sprinklerOn : PLExpr := PLExpr.var_expr v₁
def streetWet : PLExpr := PLExpr.var_expr v₂

/-
For each of the following English language expressions write
the corresponding expression using our concrete propositional
logic syntax. Give names to these propositions (PLExpr's) in
the pattern of p0, p1, p2, as seen below.
-/

/-!
It's raining and the sprinkler's on.
-/
def p0 : PLExpr := itsRaining ∧ sprinklerOn

/-!
The sprinler's on and it's raining.
-/
def p1  : PLExpr := sorry

/-!
If it's raining, then if the sprinkler's on, then it's
raining and the sprinkler is on. Conditional (if this
then that) expressions in natural language are written
formally in propositional and predicate logic using the
implication (implies) operator, imp (⇒ in our notation).
-/
def p2  : PLExpr := sorry

/-!
If it's raining and the sprinkler's running, then it's raining.
-/
def p3  : PLExpr := sorry

/-!
If it's raining ,then it's raining or the sprinkler's running.
-/
def p4  : PLExpr := sorry

/-!
If the sprinkler's running, it's raining or the sprinkler's running.
-/
def p5  : PLExpr := sorry

/-!
Whenever it's raining the streets are wet.
-/
def p6  : PLExpr := sorry

/-!
Whenever the sprinkler's running the streets are wet.
-/
def p7  : PLExpr := sorry

/-!
If (a) it's raining or the sprinkler's running, then (b) if
whenever it's raining then the streets are wet, then (c) if
whenever the sprinkler's running then the streets are wet, then
_________. What is the conclusion? Write the expression in PL.
-/
def p8  : PLExpr := sorry

/-!
If whenever it's raining, the streets are wet, then whenever the
streets are wet it's raining.
-/
def p9  : PLExpr := sorry


/-!
If whever it's raining then bottom, then it's not raining.
-/
def p10  : PLExpr := sorry

/-!
If it's raining or the sprinkler's running then if it's
not raining then the sprinkler's running.
-/
def p11 : PLExpr := sorry

/-!
If whenever it's raining the streets are wet, then whenever the
streets are not wet, it must not be raining.
-/
def p12 : PLExpr := sorry

/-!
-/
def p13 : PLExpr := sorry
def p14 : PLExpr := sorry
def p15 : PLExpr := sorry

end cs2120f24
