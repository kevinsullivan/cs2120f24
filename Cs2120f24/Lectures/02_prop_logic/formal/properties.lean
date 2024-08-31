import Cs2120f24.Lectures.«02_prop_logic».syntax
import Cs2120f24.Lectures.«02_prop_logic».semantics

namespace cs2120f24

/-!
### Satisfiability

We built a satisfiability checker for propositional logic,
in several pieces. This subsection includes all definitions.

#### Low-level bit vector routines
-/


-- rightmost bit in binary representation of given natural number, n
def right_bit (n : Nat) := n%2

-- dividing n by 2 discards rightmost bit in binary representation of n
def shift_right (n : Nat) := n/2

-- convert natural number to corresponding list of bits (nat, 0 or 1)
def nat_to_bin : Nat → List Nat
| 0     => [0]
| 1     => [1]
| n' + 2 =>
  have : (shift_right (n' + 2)) < (n' + 2) := by sorry
  nat_to_bin (shift_right (n' + 2)) ++ [right_bit (n' + 2)]

-- Left pad list of nats with zeros
def zero_pad : Nat → List Nat → List Nat
  | n, l => zero_pad_recursive (n - (l.length)) l
where zero_pad_recursive : Nat → List Nat → List Nat
  | 0, l => l
  | n'+1, l => zero_pad_recursive n' (0::l)

-- Make row of bits at index "row" padded to "cols" wide
def mk_bit_row : (row: Nat) → (cols : Nat) → List Nat
| r, c => zero_pad c (nat_to_bin r)

-- Convert list of bits to list of bools
def bit_to_bool : Nat → Bool
| 0 => false
| _ => true

-- convert list of bits (Nat value 0 or 1) to list Bools
def bit_list_to_bool_list : List Nat → List Bool
| [] => []
| h::t => (bit_to_bool h) :: (bit_list_to_bool_list t)

-- Make row'th row of truth table with vars variables
def mk_row_bools : (row : Nat) → (vars : Nat) → List Bool
| r, v => bit_list_to_bool_list (mk_bit_row r v)

/-!
#### Interpretations
-/

open Expr

/-
Return the  the number of variables in a given expression.

-/
def num_vars : Expr → Nat := λ e => max_variable_index e + 1 where
max_variable_index : Expr → Nat
| lit_expr true => 0
| lit_expr false => 0
| var_expr (var.mk i) => i
| un_op_expr _ e => max_variable_index e
| bin_op_expr _ e1 e2 => max (max_variable_index e1) (max_variable_index e2)

-- Override value of given var with value of given Bool in given Interp
def override : Interp → var → Bool → Interp
| old_interp, var, new_val =>
  (λ v => if (v.n == var.n)     -- when applied to var
          then new_val          -- return new value
          else old_interp v)  -- else retur old value

-- Convert a given list of Bool to an Interp function
def bools_to_interp : List Bool → Interp
  | l => bools_to_interp_helper l.length l
where bools_to_interp_helper : (vars : Nat) → (vals : List Bool) → Interp
  | _, [] => (λ _ => false)
  | vars, h::t =>
    let len := (h::t).length
    override (bools_to_interp_helper vars t) (var.mk (vars - len)) h

-- Make an interpretation for row "row" for expression with "vars" variables
def mk_interp_vars_row : (vars: Nat) → (row: Nat) → Interp
| v, r => bools_to_interp (mk_row_bools r v)

-- INTERFACE:
-- Given number, n, of variables, return list of all 2^n interpretations
def mk_interps (vars : Nat) : List Interp :=
  mk_interps_helper (2^vars) vars
where mk_interps_helper : (rows : Nat) → (vars : Nat) → List Interp
  | 0, _         => []
  | (n' + 1), v  => (mk_interp_vars_row v n')::mk_interps_helper n' v

/-!
#### Truth Table Output Column
-/
def eval_expr_interps : List Interp → Expr → List Bool
| [], _ => []
| h::t, e => eval_expr_interps t e ++ [eval_expr e h]

-- Given expression, return truth table outputs by ascending row index
def truth_table_outputs : Expr → List Bool
| e =>  eval_expr_interps (mk_interps (num_vars e)) e

/-!
### Satisfiability Checkers
-/

-- functions to check if bool list has any, resp. all, values true
def reduce_or : List Bool → Bool
| [] => false
| h::t => or h (reduce_or t)

def reduce_and : List Bool → Bool
| [] => true
| h::t => and h (reduce_and t)

-- INTERFACE
-- Three main functions: test given expression for satsfiability properties
-- reduce_or (map (eval e) all_interps)

def is_sat : Expr → Bool := λ e : Expr => reduce_or (truth_table_outputs e)
def is_valid : Expr → Bool := λ e : Expr => reduce_and (truth_table_outputs e)
def is_unsat : Expr → Bool := λ e : Expr => not (is_sat e)

end cs2120f24
