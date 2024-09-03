import Cs2120f24.Lectures.«02_prop_logic».formal.semantics
import Cs2120f24.Lectures.«02_prop_logic».formal.interpretation

namespace cs2120f24

/-!
#### Truth Table Output Column

Given expression, return truth table outputs by ascending row
index, and where the all false row thus appears at the "top" of
the "table", and each subsequent row is "incremented" in binary
arithmetic up to the row at index 2^n-1, where n is the number
of variables.
-/

def truth_table_outputs : PLExpr → List Bool
| e =>  eval_expr_interps (expr_to_all_interps e) e where
eval_expr_interps : List BoolInterp → PLExpr → List Bool
| [], _ => []
| h::t, e => [eval_expr e h] ++ eval_expr_interps t e

end cs2120f24
