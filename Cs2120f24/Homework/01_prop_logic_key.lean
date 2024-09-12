import «Cs2120f24».Lectures.«02_prop_logic».formal.syntax
import «Cs2120f24».Lectures.«02_prop_logic».formal.semantics
import «Cs2120f24».Lectures.«02_prop_logic».formal.properties

/-!
CS 2120-002 F24 Homework #1: Propositional Logic
-/

namespace cs2120f24
open PLExpr


/-!
First, we define three propositional variables: Wet, Rain, and
Sprink, following the exmaple presented in class, with shorter
but still suggestive variable names, for ease of reading and
writing propositional logic expressions -- aka "propositions."

Your first task is to be sure you understand the notation we're
using. Consider the first line below:

def wet : PLExpr := {⟨0⟩}.

We break that down here. *Study this material.* It's not very
difficult, and you really do need to understand this notation
easily going forward.

def       -- keyword to bind name (wet) to a value (here {⟨0⟩})
: PLExpr  -- defines the type of value to be bound (here, PLExpr)
:=        -- separates "variable type declaration" from value
⟨ 0 ⟩     -- Lean-defined shorthand for (BoolExpr.mk 0)
{ ... }   -- our concrete syntax for PLExpr.var_expr.mk

The parts here that might cause some conflusion are ⟨ _ ⟩ and
{ _ }. First, the funny angle brackets are not on your keyboard;
they are special characters you need to enter in VSCode using
\< and \>. Enter these strings then a space to get these
characters. Second, a "structure" type in Lean is an inductive
type with *just one constructor* that defaults in name to "mk".
An example is BoolVar.mk. Rather than typing that constructor
expression each time you want a new value *of *any* structure
type), you can use this this angle bracket notation instead.
Lean just has to be able to figure out from context what type
of object is needed so that it can translate ⟨ ⟩ into a call
to the "mk" constructor for the right structure type.

Next, the {...} notation is a concrete syntax notation that we
ourselves have defined (in syntax.lean) for PLExpr.var_expr. It
in turn expects a BoolVar argument, which is how Lean know what
constructor to use for the ⟨_⟩ notation: namely BoolVar.mk.

The reading should help with the ⟨_⟩ notation. And you should be
able to understand how we've defined { } as a concrete syntax in
syntax.lean.
-/


def wet : PLExpr := {⟨0⟩}
def rain : PLExpr := {⟨1⟩}
def sprink : PLExpr := {⟨2⟩}


/-!
ENGLISH TO FORMAL PROPOSITIONAL LOGIC

Problem #1: 50 points. Using the variable names, wet, rain,
and sprink, write propositional logic expressions for each of
the given propositions (expressions) written in natural language.
For example, "it's raining and the springler is running" would be
(rain ∧ sprink). Wtite your expressions in place of the sorrys.

Once you've written your expression, add a line of "code" to
check your expressions for *validity*. Then, if the expression
is *not* valid, in English explain very briefly a situation in
which the proposition is not true. For example, you know that
raining ∧ sprinking is not valid, and in this case it would be
ok to write "if it's not raining then this proposition is false"
-/

/-!
A. It's raining and the sprinkler is running.
-/
def formal_0 : PLExpr := rain ∧ sprink


/-!
B. If it's raining then it's raining or the sprinkler's running.
Rememver to use \=> for the implies "connective" (expression
builder).
-/
def formal_1  : PLExpr := rain ⇒ (rain ∨ sprink)

/-!
C. If the sprinkler's running then it's raining or it's sprinkling.
-/
def formal_2  : PLExpr := sprink ⇒ (rain ∨ sprink)

/-!
D. Whenever it's raining the streets are wet. You can express the same
idea as "if it's raining then the streets are wet." Be sure you see that
these two English-language phrases mean the same thing. You will want to
use the "whenever" form sometimes and the "if then" form sometimes when
writing logic in English.
-/
def formal_3  : PLExpr := rain ⇒ wet

/-!
E. Whenever the sprinkler's running the streets are wet.
-/
def formal_4 : PLExpr := sprink ⇒ wet
#eval! is_valid formal_4

/-!
Here's an example, from class, of a proposition built up in
part from several smaller *implies* propositions. This is a
reminder to help you with any similar cases that follow.

If it's raining or the sprinkler's running, then if whenever
it's raining then the streets are wet, then if whenever the
sprinkler's running then the streets are wet, then the streets
are wet.

Add a check for the validity of this expression. The *example*
keyword in Lean asks Lean to check a term without binding a
name to it.
-/
def foo : PLExpr :=
  (rain ∨ sprink) ⇒
  (rain ⇒ wet) ⇒
  (sprink ⇒ wet) ⇒
  wet

-- Write your validity check here
#eval! is_valid ((rain ∨ sprink) ⇒ (rain ⇒ wet) ⇒ (sprink ⇒ wet) ⇒ wet)
#eval! is_valid foo

/-!
If (whenever it's raining, the streets are wet), then (whenever the
streets are wet it's raining.)
-/
def formal_5 : PLExpr := (rain ⇒ wet) ⇒ (wet ⇒ rain)
#eval! is_valid formal_5

-- NO formal_06


/-!
If (whever it's raining then bottom)/false, then (it's not raining).
-/
def formal_7  : PLExpr := (rain ⇒ ⊥) ⇒ ¬rain
#eval! is_valid formal_7


/-!
If whenever it's raining the streets are wet, then whenever it's not
raining the streets are not wet.
-/
def formal_8 : PLExpr := (rain ⇒ wet) ⇒ (¬rain ⇒ ¬wet)
#eval! is_valid formal_8


/-!
If whenever it's raining the streets are wet, then whenever the
streets are not wet, it's not be raining.
-/
def formal_9 : PLExpr := (rain ⇒ wet) ⇒ (¬wet ⇒ ¬rain)
#eval! is_valid formal_9

/-!
PROPOSITIONAL LOGIC TO ENGLISH: 50 points

For each of the following propositions in propositional logic,
open up some space after the proposition, in a comment block
give a corresponding English-language form of that proposition;
then *think* about whether the proposition is valid or not; and
add a validity check using our validity checker. Finally, if
a proposition is not valid, in English describe a case where
the proposition is not true. Notice but don't worry (yet) about
the funny names we assign to these propositions.
-/

def and_intro := sprink ⇒ rain ⇒ sprink ∧ rain
/-!
If it's sprinkling, and then if it's (also) raining, then
it's sprinkling and it's raining.
-/

def and_elim_left := sprink ∧ rain ⇒ sprink
/-!
If it's sprinkingling and raining, then it's sprinking.
-/

def and_elim_right := sprink ∧ rain ⇒ rain
/-!
If it's sprinkingling and raining, then it's raining.
-/


def or_intro_left := sprink ⇒ sprink ∨ rain
/-!
If it's sprinkling then it's sprinkling or it's raining.
-/

def or_intro_right :=  rain ⇒ sprink ∨ rain
/-!
If it's raining then it's sprinkling or it's raining.
-/

def or_elim := rain ∨ sprink ⇒ (rain ⇒ wet) ⇒ (sprink ⇒ wet) ⇒ wet
/-!
If it's raining or sprinkling, then if it's also the case that
whenever it's raining it's wet, then if in addition it's the case
that whenever it's sprinkling it's wet, then it's wet. (The idea is
that because at least one of the cases of the *disjunction* is true
and in either case it's wet, then it must be wet.)
-/

def neg_intro := (sprink ⇒ ⊥) ⇒ ¬sprink
/-!
If whenever it's sprinkling false is true then it's not sprinkling.

We could also say that if sprinkling being true leads to a
contradiction, then it must not be sprinkling. This proposition is
also known as "proof by negation:" To show that it's not sprinking
it *suffices* to show that, if it were, an impossibiliity occurs.
As that cannot happen in our logic, it must not be sprinkling.
-/

def neg_elim := ¬¬sprink ⇒ sprink
/-!
If it's not not sprinkling then it is sprinkling.

At the heart of propositional logic is what we call
"the law of the excluded middle," which states that
there every proposition is either true or false: one
or the other must hold.

In particular, sprink must be true or it must be false.
In it's true, ¬sprink is false, and ¬(false) is true,
and true ⇒ true is true, so the overall proposition is
true in this case. Next, if sprink is false, well, then
¬ false is true, and ¬ true is false, so we have that
false ⇒ false, and that's also true. *So the proposition
is true in either case *and, as, those are the only two
possible cases by the law of the excluded middle*, the
proposition is invariably true, thus valid.
-/

def imp_intro := sprink ⇒ wet ⇒ (sprink ⇒ wet)
/-!
If it's sprinkling, then if (in that *context*) it's
also wet, then we can conclude that if it's sprinkling
then it's wet.

Implies needs to be right associative so that we can
read it left to right gather a context of assumptions.
Here we first assume sprink, then we assume wet, then
*in that context*, we want to know if sprink ⇒ wet.
-/

def imp_elim := (sprink ⇒ wet) ⇒ sprink ⇒ wet
/-
If whenever it's sprinkling it's wet, then if (in that
context) it's sprinkling then it must be wet.
-/

def equiv_intro := (sprink ⇒ wet) ⇒ (wet ⇒ sprink) ⇒ (sprink ↔ wet)
/-
If whenever it's sprinking it's wet, then if whevever
it's wet it's sprinkling, then sprinkling and wet are
equivalent: it's sprinkling if and only if it's wet.
-/

def equiv_elim_left := (sprink ↔ wet) ⇒ (sprink ⇒ wet)
/-
If it's sprinkling if and only if it's wet, then if it's
sprinkling then it's wet.
-/

def equiv_elim_right := (sprink ↔ wet) ⇒ (wet ⇒ sprink)
/-
If it's sprinkling if and only if it's wet, then if it's
wet then it's sprinkling.
-/
#eval! is_valid equiv_elim_right

def affirm_disjunct := (rain ∨ sprink) ⇒ rain ⇒ ¬sprink
/-!
If it's wet or sprinkling then if it's not wet it's not
sprinkling.

This one is easier to understand is the identiers line
up with our intuition: (rain ∨ sprink) ⇒ rain ⇒ ¬sprink.
This says if it's raining or sprinking and not raining
then it's sprinkling. Why is that wrong?
-/


def affirm_consequent := (sprink ⇒ wet) ⇒ wet ⇒ sprink
/-!
If whenever it's sprinkling it's wet, then whenever it's
wet it must be sprinkling.

Why is this wrong?
-/

def deny_antecedent := (sprink ⇒ wet) ⇒ ¬sprink ⇒ ¬wet
/-
If whenever it's sprinkling it's wet, then if it's not
sprinkling it must not be wet.

Why is this wrong?
-/


/-
Are they valid?
-/

#eval! is_valid  and_intro
#eval! is_valid  and_elim_left
#eval! is_valid  and_elim_right

#eval! is_valid  or_intro_left
#eval! is_valid  or_intro_right
#eval! is_valid  or_elim

#eval! is_valid  neg_intro
#eval! is_valid  neg_elim

#eval! is_valid  imp_intro
#eval! is_valid  imp_elim

#eval! is_valid  equiv_intro
#eval! is_valid  equiv_elim_left
#eval! is_valid  equiv_elim_right

#eval! is_valid  affirm_disjunct
#eval! is_valid  affirm_consequent
#eval! is_valid  deny_antecedent

end cs2120f24
