import Cs2120f24.Lectures.«02_prop_logic».formal.properties
import Cs2120f24.Lectures.«02_prop_logic».formal.interpretation
import Cs2120f24.Lectures.«02_prop_logic».formal.semantics
import Cs2120f24.Lectures.«02_prop_logic».formal.truth_table
import Cs2120f24.Lectures.«02_prop_logic».formal.utilities

namespace cs2120f24

/-!
As a final chapter in our unit on propositional logic, we
now present the concepts of models and counter-examples.

Given a proposition (PLExpr), e, and an interpretation for
the variables in e, we can apply our semantic evalation
function, evalPLExpr, to e and i, to compute the truth
value of the proposition, e, when understood to be about
the "situation" or "world" or "state of affairs" described
by i.
-/


/-!
Examples. Will be moved to Main.lean at some point.
-/

-- Propositional variables for our examples
def P : PLExpr := { ⟨ 0 ⟩ }
def Q : PLExpr := { ⟨ 1 ⟩ }
def R : PLExpr := { ⟨ 2 ⟩ }

-- an more interesting proposition (expression), e

def e := ¬(P ∧ Q) ⇒ ¬P ∨ ¬Q

-- It uses just two propositional variables, P and Q

-- This function returns this value for any expression
#eval numVarsFromExpr e   -- expect 2 for e

/-! INTERPRETATIONS

We can easily enumerate all possible interpretations.
That's jsut the "input" side of a truth table. Notice
that this part doesn't depend on the details of e (an
expression) at all. The driving factor is the number
number of *variables* (columns). The number of rows is
then 2^#columns. But there's more. What relationship
do you see between the row indices and the row contents?
-/

/-!
            var
           0   1
  index  | P | Q | e
    0    | 0 | 0 | _
    1    | 0 | 1 | _
    2    | 1 | 0 | _
    3    | 1 | 1 | _
-/

/-!
Recall that we represent each interpretation (each row)
as a function. That function takes a variable (it's index)
as an actual parameter, and returns the Boolean value for
that variable *in that row* ("under that interpretation").

But of course the value for that variable in that row is
just the (0 for false / 1 for true) Boolean value in the
*binary expansion* of the row index. Is everyone okay with
base 2 arithmetic? So all of this can easily programmed.

Here we compute the interpretation in row index 2 in the
preceding example. Note that e's not involved except to
the extent that it determines the number of variables in
one.
-/

def i := InterpFromRowCols 2 2
#check i

/-!
Applying i to a *variable*, with indices 0 or 1, should
return the values in row 2, namely 1 and 0. Does it work?
(Remember ⟨⟩ notation for applying structure constructor,
so here ⟨0⟩ is (BoolVar.mk 0), a "variable" in our lexicon.)
-/

#eval! i ⟨0⟩    -- expect true
#eval! i ⟨1⟩    -- expect false

/-!
 It's exactly this trick that is used in the semantic
evaluation function that defines for us an operational
semantics for propositional logic. That means that we
have a *function* for computing expression meanings.
-/

#eval! evalPLExpr e i

/-!
Given the semantic meanings (Boolean functions) that
we've given our syntactic operators, we see that the
proposition/expression e evaluates to true under the
interpretation, i. We will thus say that i is a model
of e. It represents a world in which e is true.
-/

/-!
CONVENIENCE FUNCTIONS FOR WORKING WITH INTERPRETATIONS

An interpretation, i, is a function. It's generally not
helpful to print functions in Lean. If you want to see a
string representation of an interpretation, we do have a
function for that. You pass it the interpretation and how
many columns you want to see. An interpretation function
is technicallky defined as false for all column indices
beyond those of interest in a given case.
-/

#eval! listBitStringFromInterp i 2

/-!
We also provide a function for converting a list of Bool
values into an interpretation.
-/

def i2 := interpFromBools [true, false, true]
#eval! listBitStringFromInterp i2 3

/-!
And finally a way to get a printable list of multiple
(typically all) interpretations.
-/

/-!
ALL INTERPRETATIONS

Up to now we've been working with one interpretation, i.
We can also easily obtain, and provide a function, for
getting a list of *all* interpretations for an expression
with "n" variables, for any number, n. This function first
counts the number of variables in e and then constructs a
list of interpretatins, one for each index from 2^n-1 to 0.
-/

def all_interps_e := listInterpsFromExpr e

/-!
TRUTH TABLES

You already know you can get the results of evaluating an
expression e for each interpretation in a given list of them.
-/

#eval! truthTableOutputs e

/-
We see that e (go back and see how we defined it) is actually
valid. And now of course you can see how we check validity for
any expression. We count the variables in it, we generate 2^n

-/

#eval! truthTableOutputs ¬e


/-!
PROPERTIES OF EXPRESSIONS

As you know, validity just means that a proposition is true
under every interpretation -- in all worlds -- making it into
a general-purpose reasoning principle. The is_valid function
takes an expression, computes its number of variable, gets a
list of all interpretations
-/

#eval! is_valid e
#eval! is_sat e
#eval! is_unsat ¬e


/-!
MODELS

A model is an interpretation that makes a proposition true.
A "SAT solver" (like is_sat) returns true if  there's at least
one such interpretation. A function that actually returns such
an interpretation (not just a Boolean value) is called a model
finder. A related problem is to find *all* models of a given
proposition. How would you do that?
-/

def findModel (e : PLExpr) : Option BoolInterp :=
  let modelIndex := indexFirstTrue (truthTableOutputs e)
  match modelIndex with
  | none => none
  | some n => interpFromRowCols n (numVarsFromExpr e)

#print e
#reduce match (findModel e) with | none => [] | some i => listBitStringFromInterp i (numVarsFromExpr e)
#reduce match (findModel ¬e) with | none => [] | some i => listBitStringFromInterp i (numVarsFromExpr ¬e)



/-
COUNTEREXAMPLES

A counterexample is an interpretation that makes a proposition
false. If you write a *specification*, S, about a system in the
form of a proposition that should be true of all possible system
behaviors, you'd like to know if there are any behaviors that
do *not* satisfy the specification. Such a behavior would be
a *counterexample* to the specification. So how might we put
together a method for finding a counterexample if there is one?
-/

def findCounterExample : PLExpr → Option BoolInterp
| e => findModel ¬e

#reduce match (findCounterExample e) with
  | none => []
  | some i => listBitStringFromInterp i (numVarsFromExpr e)

#reduce match (findCounterExample ¬e) with
  | none => []
  | some i => listBitStringFromInterp i (numVarsFromExpr ¬e)


end cs2120f24
