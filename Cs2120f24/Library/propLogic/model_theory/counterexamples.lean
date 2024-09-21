import Cs2120f24.Library.propLogic.model_theory.models

namespace cs2120f24.propLogic

/-
COUNTEREXAMPLES

We return all counterexamples, or one if there was one, for
any given expression. These operations find models of the negation
of the given expression, which amount to counterexamples for it.
-/

def findCounterexamples (e : PLExpr) : List BoolInterp := findModels ¬e
def findCounterexample (e : PLExpr) : Option BoolInterp := findModel ¬e

end cs2120f24.propLogic
