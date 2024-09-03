import Cs2120f24.Lectures.«02_prop_logic».formal.semantics
import Cs2120f24.Lectures.«02_prop_logic».formal.interpretation
import Cs2120f24.Lectures.«02_prop_logic».formal.truth_table
import Cs2120f24.Lectures.«02_prop_logic».formal.utilities

namespace cs2120f24

/-!
### Satisfiability

We built a satisfiability checker for propositional logic,
in several pieces. This subsection includes all definitions.

-/

/-!
## Satisfiability Checkers
-/

-- INTERFACE
-- Three main functions: test given expression for satsfiability properties
-- reduce_or (map (eval e) all_interps)

def is_sat : PLExpr → Bool := λ e : PLExpr => reduce_or (truthTableOutputVector e)
def is_valid : PLExpr → Bool := λ e : PLExpr => reduce_and (truthTableOutputVector e)
def is_unsat : PLExpr → Bool := λ e : PLExpr => not (is_sat e)
def is_model : BoolInterp → PLExpr → Bool := fun i e => evalBoolExpr e i

end cs2120f24
