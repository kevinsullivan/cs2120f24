import Cs2120f24.Lectures.«02_prop_logic».syntax

namespace cs2120f24

/-!
### Semantics
-/

-- missing binary Boolean operators
def implies : Bool → Bool → Bool
| true, false => false
| _, _ => true

def iff : Bool → Bool → Bool
| true, true => true
| false, false => true
| _, _ => false

-- meanings of unary operators
def eval_un_op : un_op → (Bool → Bool)
| (un_op.not) => not

-- meanings of binary operators
def eval_bin_op : bin_op → (Bool → Bool → Bool)
| bin_op.and => and
| bin_op.or => or
| bin_op.imp => implies
| bin_op.iff => iff

-- The interpretation type
def Interp := var → Bool

open Expr

-- The meanings of expressions "under" given interpretations
def eval_expr : Expr → Interp → Bool
| lit_expr b,          _ => b
| (var_expr v),        i => i v
| (un_op_expr op e),      i => (eval_un_op op) (eval_expr e i)
| (bin_op_expr op e1 e2), i => (eval_bin_op op) (eval_expr e1 i) (eval_expr e2 i)


end cs2120f24
