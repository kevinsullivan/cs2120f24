import «Cs2120f24».Library.propLogic.syntax
import «Cs2120f24».Library.propLogic.model_theory.counterexamples

namespace cs2120f24.propLogic

/-!
# Exam 1: MidTerm

This is an individual exam. You must complete it entirely on your own,
with no outside inputs of any kind other than in response to questions
posed directly to the instructor. You must take the exam while in class
in the classroom. When you come in to the classroom, spread yourselves
out, mix up, and don't sit where you or someone you know of might hope to
catch a glance.

TO TAKE THIS EXAM: First copy it into your MyWork directory. Then complete
it. THEN SAVE IT. Then upload it. THEN CHECK YOUR UPLOAD, correcting it if
necessary.
-/



/-!
PART #1: Reading, writing, and expressing ideas in PL.
-/

/-
To begin with we give you declarations of three propositional logic
variables from which we'll construct variable *expressions* to use in
constructing larger propositions (expressions) in propositional logic.
The questions that then follow refer back to these propositions.
-/

-- First define a disting variable for each variable expression
def v₀ : BoolVar := BoolVar.mk 0    -- abstract syntax for a variable
def v₁ : BoolVar := ⟨1⟩             -- Lean gives this notation for mk
def v₂ : BoolVar := ⟨2⟩

-- With these variables, we can now constuct three variable expressions.
def P := PLExpr.var_expr v₀         -- abstract syntax for variable expression
def Q := { v₁ }                     -- we defined correspond concrete syntax
def R := { v₂ }

-- And now here are the expressions we car about
def e1 : PLExpr := (R ⇒ ⊥) ⇒ ¬R
def e2 : PLExpr :=
  (P ⇒ Q ⇒ P ∧ Q) ⇒
  (P ∧ Q ⇒ P) ⇒
  (P ∧ Q ⇒ Q) ⇒
  ((P ∧ Q) ⇒ (Q ∧ P))
def e3 := (P ↔ Q) ∧ (Q ↔ R) ⇒ (P ↔ R)
def e4 := ¬(P ∨ Q) ↔ (¬P ∧ ¬ Q)
def e5 := (P ⇒ Q) ⇒ P ⇒ R


/- Part #1, A
For each proposition, e1 - e5, (1) give a precise English language rendering
of the proposition from left to right, (2) then give an English rendering from
right to left.

Give you answers here:

e1:


e2:


e3:


e4:


e5:


-/

/- Part #1, B
Give formal versions of the following propositions expressed in English.
You may use the variable expressions, P, Q, and R in writing your answers.

A. "Going to school makes you smart."

(Use "P" for the proposition, "GoesToSchool" and "Q" for "IsSmart".
-/
def f1 : PLExpr := _

/-
B. If you learn at home (P) or you learn at school (Q) then you'll be smart (R)
-/
def f2 : PLExpr := _

/-
C. It's not true that truth is (equivalent to) not truth.
-/
def f3 : PLExpr := _



/-
Part $2: Semantic Validity

#A. Write a truth table for the proposition (P ⇒ Q) ⇒ (Q ⇒ P)

| P | Q | (P ⇒ Q) | (Q ⇒ P) | (P ⇒ Q) ⇒ (Q ⇒ Q) |
|
|
|
|

Part #2, B: The proposition is not valid. Give an interpretation
that serves as a counter-example and a corresponding real world example
where some condition P implies some condition Q, but where Q being the
case does not necessarily mean that P is, too.


Part #2, C: From the truth table, identify an interpretation that serves
as a counter-example to the proposition.


Part #2, D. Suppose you have a function that, when given any proposition in
PL, returns a list of its models, but that you need a function that returns
a list of its counterexamples. Describe very briefly how you'd implement a
new counterexamples-finding function, given a models finder. What type of
argument(s) would your new function take, and what would it do with it/them
to compute the desired answer.

Answer here:

MODEST EXTRA CREDIT: Suppose you have a models-finding function. We use
"sorry" in the first definition below to tell Lean just to assume we've
provided a definition of a modelsFinding function. Just pretend that it
is fully defined and that it works. Complete the implementation of the
counterexamples-finder.
-/

def modelsFinder : PLExpr → List BoolInterp := sorry

-- complete this definition
def counterexamplesFinder : PLExpr → List BoolInterp
| e => _



/-
PART #3: Counting Things
-/

/-
A. Suppose you have a PL expression that uses N distinct PL variables. Give a
formula that tells you how many interpretations there are for that expression.


B. Give an algebraic formula for the number of distinct functions there are
from N Boolean input values to a Boolean output. Two functions are equal in
our formulation if they produce the same outputs on *all* inputs, otherwise
they are unequal/distinct.


C. Consider a language of arithmetic expressions, where variables now have
natural number values, rather than Boolean values like PL variables. How
many interpretations are there for this expression: (X + 2) * (Y - 5) = 0?

Answer:

Tiny extra credit: give both a model and a counterexample for this formula.

Answer:

-/


/- Part #4: Inductive thinking

Inductive data type definitions and recursive functions are vital
to how we've defined both the syntax and semantics of PL and other
expression languages. This question is meant to test your ability
to read and complete such definitions.

Here's a definition of a "NatTree" data type that we just made
up. A NatTree is either empty, or it's a node holding a Nat value
and two smaller trees.

Complete the definition of the function, given here, that takes a
NatTree and returns the number of nodes it contains.
-/

inductive NatTree : Type where
| empty
| node (n : Nat) (left : NatTree) (right : NatTree)

open NatTree

-- Complete this definition by replacing the line with the sorry

def numNatTreeNodes : NatTree → Nat
| empty => 0
| _ => sorry

end cs2120f24.propLogic
