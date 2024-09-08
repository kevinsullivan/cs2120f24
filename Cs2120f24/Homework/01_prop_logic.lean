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
def formal_0 : PLExpr := sorry


/-!
B. If it's raining then it's raining or the sprinkler's running.
Rememver to use \=> for the implies "connective" (expression
builder).
-/
def formal_1  : PLExpr := sorry

/-!
C. If the sprinkler's running then it's raining or it's sprinkling.
-/
def formal_2  : PLExpr := sorry

/-!
D. Whenever it's raining the streets are wet. You can express the same
idea as "if it's raining then the streets are wet." Be sure you see that
these two English-language phrases mean the same thing. You will want to
use the "whenever" form sometimes and the "if then" form sometimes when
writing logic in English.
-/
def formal_3  : PLExpr := sorry

/-!
E. Whenever the sprinkler's running the streets are wet.
-/
def formal_4 : PLExpr := sorry

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
example  : PLExpr :=
  rain ∨ sprink ⇒
  (rain ⇒ wet) ⇒
  (sprink ⇒ wet) ⇒
  wet

-- Write your validity check here


/-!
If (whenever it's raining, the streets are wet), then (whenever the
streets are wet it's raining.)
-/
def formal_5 : PLExpr := sorry


/-!
If (whever it's raining then bottom)/false, then (it's not raining).
-/
def formal_7  : PLExpr := sorry


/-!
If whenever it's raining the streets are wet, then whenever it's not
raining the streets are not wet.
-/
def formal_8 : PLExpr := (rain ⇒ wet) ⇒ ((¬rain) ⇒ (¬wet))

/-!
If whenever it's raining the streets are wet, then whenever the
streets are not wet, it's not be raining.
-/
def formal_9 : PLExpr := sorry


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
def and_elim_left := sprink ∧ rain ⇒ sprink
def and_elim_right := sprink ∧ rain ⇒ rain

def or_intro_left := sprink ⇒ sprink ∨ rain
def or_intro_right :=  rain ⇒ sprink ∨ rain
def or_elim := rain ∨ sprink ⇒ (rain ⇒ wet) ⇒ (sprink ⇒ wet) ⇒ wet

def not_intro := (sprink ⇒ ⊥) ⇒ ¬sprink
def not_elim := ¬¬sprink ⇒ sprink

def imp_intro := sprink ⇒ wet ⇒ (sprink ⇒ wet)
def imp_elim := (sprink ⇒ wet) ⇒ sprink ⇒ wet

def equiv_intro := (sprink ⇒ wet) ⇒ (wet ⇒ sprink) ⇒ (sprink ↔ wet)
def equiv_elim_left := (sprink ↔ wet) ⇒ (sprink ⇒ wet)
def equiv_elim_right := (sprink ↔ wet) ⇒ (wet ⇒ sprink)

def affirm_disjunct := (wet ∨ sprink) ⇒ wet ⇒ ¬sprink
def affirm_consequent := (sprink ⇒ wet) ⇒ wet ⇒ sprink
def deny_antecedent := (sprink ⇒ wet) ⇒ ¬wet ⇒ ¬sprink

end cs2120f24
