import «Cs2120f24».Lectures.«02_prop_logic».formal.properties
namespace cs2120f24

open PLExpr


/-!
SYNTAX

Suppose I want to write some propositional logic expressions
using the variable expressions, P, Q, and R, and building up
larger propositions using the propositional logic expression-
constructing operators. Here's how you do it.
-/

-- First define a disting variable for each variable expression
def v₀ : BoolVar := BoolVar.mk 0    -- abstract syntax
def v₁ : BoolVar := ⟨1⟩             -- Lean notation for mk
def v₂ : BoolVar := ⟨2⟩

/-!
Now you define the variable expressions you want to use. The
first line is using abstract syntax. The next two use our own
(non-standard) notation, desugaring to exactly that abstract
syntax.
-/
def P : PLExpr := PLExpr.var_expr v₀
def Q : PLExpr := { v₁ }  -- our notation for var_expr constructor
def R : PLExpr := { v₂ }

/-
Now that you have three variable expressions to work with,
you can use logical expression "connectives" (operators) to
build bigger expressions. Consider the expression, P ∧ Q,
for example. First we'll write it using abstract syntax,
then using concrete syntax.
-/

-- abstract syntax
def P_and_Q_abstract : PLExpr :=
  (PLExpr.bin_op_expr BinOp.and P Q)

-- Concrete syntax (standard math book) notation
def P_and_Q_concrete := P ∧ Q

-- Notation de-sugars to that astract syntax
#reduce P_and_Q_concrete


/-!
INTERPRETATIONS
-/

/-
Here's how we can see a list of interpretations
for a given expressions.
-/
#reduce interpStringsFromInterps
          (listInterpsFromExpr (P ∧ Q ∨ R))
          3 -- number of variables here


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

#eval! (truthTableOutputs (P))
#eval! (truthTableOutputs (P ∨ Q))


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
def p2  : PLExpr := itsRaining ⇒ sprinklerOn ⇒ p0

/-!
If it's raining and the sprinkler's running, then it's raining.
-/
def p3  : PLExpr := (itsRaining ∧ sprinklerOn) ⇒ itsRaining

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

def p8  : PLExpr := (itsRaining ∨ sprinklerOn) ⇒ (itsRaining ⇒ streetWet) ⇒ (sprinklerOn ⇒ streetWet) ⇒ streetWet
#eval! is_valid p8
#eval! is_sat p8
#eval! is_unsat p8



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
QUIZ: challenges to come
-/
def p13 : PLExpr := sorry
def p14 : PLExpr := sorry
def p15 : PLExpr := sorry

end cs2120f24
