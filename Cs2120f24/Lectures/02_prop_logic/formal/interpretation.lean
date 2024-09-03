import Cs2120f24.Lectures.«02_prop_logic».formal.syntax
import Cs2120f24.Lectures.«02_prop_logic».formal.semantics
import Cs2120f24.Lectures.«02_prop_logic».formal.utilities

/-!
#### Boolean Interpretation
-/

namespace cs2120f24

-- Return the  the number of variables in a given expression.
def num_vars_in_expr : PLExpr → Nat := (fun e => max_variable_index e + 1) where
max_variable_index : PLExpr → Nat
| PLExpr.lit_expr _ => 0
| PLExpr.var_expr (BoolVar.mk i) => i
| PLExpr.un_op_expr _ e => max_variable_index e
| PLExpr.bin_op_expr _ e1 e2 => max (max_variable_index e1) (max_variable_index e2)

-- From interpretation, variable, and new Bool, override that interpretation to assign that new value to that variable
def override_var_val_in_interp : BoolInterp → BoolVar → Bool → BoolInterp
| i, v, b =>
  λ (v' : BoolVar) =>
    if (v'.index == v.index)  -- if index is variables overridden
        then b                -- return new value
        else (i v')           -- else value under old interp

-- Helper for mk_row_interp function that follows
-- Convert a given list of Bool to an Interp function
def list_bool_to_interp : List Bool → BoolInterp
  | l => bools_to_interp_helper l.length l
where bools_to_interp_helper : (vars : Nat) → (vals : List Bool) → BoolInterp
  | _, [] => (λ _ => false)
  | vars, h::t =>
    let len := (h::t).length
    override_var_val_in_interp
      (bools_to_interp_helper vars t)
      (BoolVar.mk (vars - len)) h

/-!
Make an interpretation *function* for row index "row"
a truth table with "vars" variables/columns.
-/
-- DEPENDENCY: mk_row_bools is from utilities
def row_index_and_vars_to_interp : (row: Nat) → (vars: Nat) → BoolInterp
| index, cols =>
  list_bool_to_interp (list_bool_from_row_index_and_cols index cols)

/-
def all_interps_n_vars : Nat → List (List Bool)
| 0 => []
| (n' + 1) => [([false]::(all_interps_n_vars n')), true::(all_interps_n_vars n')]
-/

/-!
Given the number, n, of variables, return a list of its 2^n interpretations.
Watch out, as the size of the constsructed lists grows very quickly.
-/
def list_interps_for_n_variables (vars : Nat) : List BoolInterp :=
  mk_interps_helper (2^vars) vars
where mk_interps_helper : (rows : Nat) → (vars : Nat) → List BoolInterp
  | 0, _         => []
  | (n' + 1), v  =>
      (row_index_and_vars_to_interp n' v)::
      mk_interps_helper n' v

/-!
Given a PLExpr
-/
def expr_to_all_interps : PLExpr → List BoolInterp
| e => let n := num_vars_in_expr e; list_interps_for_n_variables n

/-!
Given interp, i, return list of "0"/"1" strings of width n
By case analysis on the width argument
-/
def interp_to_string : (i : BoolInterp) → (n : Nat) → List String
| _, 0 => []
| i, (n' + 1) =>
  let b := if (i ⟨n'⟩ ) then "1" else "0"
  b::interp_to_string i n'

/-!
Given a list of Bool interps and a width n, output them as a list of list of Bool
-/
def interps_to_list_list_string : List BoolInterp → Nat → List (List String)
| [], _ => []
| h::t, n => (interp_to_string h n)::(interps_to_list_list_string t n)
