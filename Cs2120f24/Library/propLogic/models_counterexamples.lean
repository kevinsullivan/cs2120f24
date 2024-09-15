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
MODELS

A model is an interpretation that makes a proposition true.
A "SAT solver" (like is_sat) returns true if  there's at least
one such interpretation. A function that actually returns such
an interpretation (not just a Boolean value) is called a model
finder. A related problem is to find *all* models of a given
proposition. How would you do that?
-/

def findModels (e : PLExpr) : List BoolInterp :=
  List.filter
    (fun i => evalPLExpr e i = true) -- given i, true iff i is model of e
    (listInterpsFromExpr e)

def findModel :  PLExpr → Option BoolInterp
| e =>
  let ms := findModels e
  match ms with
  | [] => none
  | h::_ => h

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

def findCounterexamples (e : PLExpr) : List BoolInterp := findModels ¬e
def findCounterexample (e : PLExpr) : Option BoolInterp := findModel ¬e

/-!
These functions use types you don't yet know about: namely List and Option.
You should understand lists intuitively from CS1. You can think of an option
as a list of length either zero (called none) or one (called some e), where
e the specific value in the length-one list of values (an interpertation).
-/
end cs2120f24
