import Cs2120f24.Lectures.«02_prop_logic».formal.model_theory.truth_table

namespace cs2120f24.lecture.prop_logic

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

end cs2120f24.lecture.prop_logic
