import Cs2120f24.Lectures.«02_prop_logic».formal.model_theory.models


namespace cs2120f24.lecture.prop_logic

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
end cs2120f24.lecture.prop_logic
