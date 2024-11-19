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

Give your answers here: (EACH DIRECTION WORTH 1PT)

e1:
  - If R implies false then ¬R can be judged to be true.
  - If R being true produced a contradiction, then R must be false and ¬R must be true


e2:
If whenever P is true and Q is true then P ∧ Q is true,
then if whenever P ∧ Q is true then P is true, and
if whenver P ∧ Q is Q is true, then if P ∧ Q is true
then so is Q ∧ P.


e3:
- If P is equivalent to (iff) Q and Q is equivalent to (iff) R then P is equivalent to (iff) R
- If whenever P is equivalent to Q and Q is equivalent to R then P is equivalent to R

e4:
- If P or Q is false, then both P and Q must be false
- etc

e5:
- If whenever P is true, so is Q, and if P is also true, then R must be true
- or equivalent (note that this proposition is not valid, but that's not what we're asking about here)

-/

/- Part #1, B (5 points each)

Give formal versions of the following propositions expressed in English.
You may use the variable expressions, P, Q, and R in writing your answers.

A. "Going to school makes you smart."

(Use "P" for the proposition, "GoesToSchool" and "Q" for "IsSmart".
-/
def f1 : PLExpr := P ⇒ Q

/-
B. If you learn at home (P) or you learn at school (Q) then you'll be smart (R)
-/
def f2 : PLExpr := P ∨ Q ⇒ R

/-
C. It's not true that truth is (equivalent to) not truth.
-/
def f3 : PLExpr := ¬(⊤ ↔ ¬⊤)



/-
Part #2: Semantic Validity (1 point for free, 9 points each)

#A. Write a truth table for the proposition (P ⇒ Q) ⇒ (Q ⇒ P)

| P | Q | (P ⇒ Q) | (Q ⇒ P) | (P ⇒ Q) ⇒ (Q ⇒ P) |
| 0   0     1         1               1
| 0   1     1         0               0
| 1   0     0         1               1
| 1   1     1         1               1

Part #2, B: The proposition is not valid. Give an interpretation
that serves as a counter-example and a corresponding real world example
where some condition P implies some condition Q, but where Q being the
case does not necessarily mean that P is, too.

Counterexample: P is false and Q is true.

Example: Even if going to school makes you smart, it's not necessarily
the case that being smart means you go to school. There are plenty of
very smart people who, for one reason or another, don't go to school.


-- Part #2, C; DELETED FROM EXAM; NO STUDENTS ANSWERS NEEDED OR CONSIDERED

Part #2, D. Suppose you have a function that, when given any proposition in
PL, returns a list of its models, but that you need a function that returns
a list of its counterexamples. Describe very briefly how you'd implement a
new counterexamples-finding function, given a models finder. What type of
argument(s) would your new function take, and what would it do with it/them
to compute the desired answer.

Answer here: I'd implement a counter-examples-finder, that takes any PL
expression, e, and returns a list of all of its counterexamples, by calling
the model finder with the proposition, ¬e. A model of ¬e (an interpretation
that makes ¬e true) is a counterexample to e insofar as is makes e false.

MODEST EXTRA CREDIT: Suppose you have a models-finding function. We use
"sorry" in the first definition below to tell Lean just to assume we've
provided a definition of a modelsFinding function. Just pretend that it
is fully defined and that it works. Complete the implementation of the
counterexamples-finder.
-/

def modelsFinder : PLExpr → List BoolInterp := sorry

-- complete this definition
def counterexamplesFinder : PLExpr → List BoolInterp
| e => modelsFinder ¬e



/-
PART #3: Counting Things (1 pt free, 9 points each, 5 pts extra credit)
-/

/-
A. Suppose you have a PL expression that uses N distinct PL variables. Give a
formula that tells you how many interpretations there are for that expression.

Answer: We assert, and accept, maybe largely based on insight and good sense,
that with n PL varibles there are 2^n interpretations. We can easily express
this idea formally (here, in Lean).
-/

def numInterpForNVars (n : Nat) : Nat := 2^n

/-
And now that we've automated that computation, we can use it to
see just how explosively the number of interpretations grows in
relation to just incremental increases in the number of variables
used in a give expression.
-/

#eval numInterpForNVars 0
#eval numInterpForNVars 1
#eval numInterpForNVars 2
#eval numInterpForNVars 3
#eval numInterpForNVars 4
#eval numInterpForNVars 5
#eval numInterpForNVars 6
#eval numInterpForNVars 7
#eval numInterpForNVars 8
#eval numInterpForNVars 9
#eval numInterpForNVars 10
#eval numInterpForNVars 20
#eval numInterpForNVars 30
#eval numInterpForNVars 40
#eval numInterpForNVars 50

/-
B. Give an algebraic formula for the number of distinct functions there are
from N Boolean input values to a Boolean output. Two functions are equal in
our formulation if they produce the same outputs on *all* inputs, otherwise
they are unequal/distinct.

One variable, say P, can evaluate to one of the two Bool values. The
interpretations are P = ⊤ and P = ⊥.  So a truth table for P has these
two interpretations as its rows, like this.

------+-------
  P   | Result
------+-------
  ⊤   | _
  ⊥   | _

The bindings of the output values to Boolean values in the Result column
defines a *single* function. So, now how many such functions are there if
*for each possible set of input values* there are two possible outputs?
How many functions are there that take two Boolean arguments, P and Q,
and that return Bool results?

With *one* variable, P, there are two interpretations, and 2^n which is to
say *four* functions of type Bool → Bool. What if there are two variables?
Then there are four interpretations, and how many functions?

It's 2^(2^n), where n is the number of variables. Do you understand? How
many functions are there from a single *8-bit byte* (short int) to Bool?
Well, there are 2^8 byte values, and for each we need to pick a Boolean
return value, and we need to do that 2^8 times, giving us 2^(2^8), which
is 2^256. That's more than 1 then 77 zeros. That's a lot of functions.
-/


/-
C. Consider a language of arithmetic expressions, where variables now have
natural number values, rather than Boolean values like PL variables. How
many interpretations are there for this expression: (X + 2) * (Y - 5) = 0?

Answer: Infinite. X could have any natural number value, so could Y.

Tiny extra credit: give both a model and a counterexample for this formula.

Answer:

MODEL: Y = 5, X = <anything>
COUNTER: X = 0, Y = 0.
-/


/- Part #4: Inductive thinking (16 pts for good answer)

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
| node _ l r => 1 + numNatTreeNodes l + numNatTreeNodes r

end cs2120f24.propLogic
