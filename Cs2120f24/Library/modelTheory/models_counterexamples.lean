import Cs2120f24.Lectures.«02_prop_logic».formal.properties
import Cs2120f24.Lectures.«02_prop_logic».formal.interpretation
import Cs2120f24.Lectures.«02_prop_logic».formal.semantics
import Cs2120f24.Lectures.«02_prop_logic».formal.truth_table
import Cs2120f24.Lectures.«02_prop_logic».formal.utilities

namespace cs2120f24

/-!
MODELS

A model is an interpretation that makes a proposition true.
A "SAT solver" (like is_sat) returns true if  there's at least
one such interpretation. A function that actually returns such
an interpretation (not just a Boolean value) is called a model
finder. A related problem is to find *all* models of a given
proposition. How would you do that? You can use the function,
findModels. It returns a list of all models of a given expression
(but will run out of space or time quickly as the problem size
grows).
-/

def findModels (e : PLExpr) : List BoolInterp :=
  List.filter
    (fun i => evalPLExpr e i = true) -- given i, true iff i is model of e
    (listInterpsFromExpr e)

/-!
Finds all models, if any, and returns either none, if there
wasn't one, or some m, where m is firstin the returned list
of models.
-/
def findModel :  PLExpr → Option BoolInterp
| e =>
  let ms := findModels e
  match ms with
  | [] => none
  | h::_ => h

/-
COUNTEREXAMPLES

We return all counterexamples, or one if there was one, for
any given expression. These operations find models of the negation
of the given expression, which amount to counterexamples for it.
-/

def findCounterexamples (e : PLExpr) : List BoolInterp := findModels ¬e
def findCounterexample (e : PLExpr) : Option BoolInterp := findModel ¬e

end cs2120f24
