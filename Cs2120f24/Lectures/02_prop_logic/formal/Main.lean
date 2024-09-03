import Cs2120f24.Lectures.«02_prop_logic».formal.interpretation
import Cs2120f24.Lectures.«02_prop_logic».formal.properties
import Cs2120f24.Lectures.«02_prop_logic».formal.utilities

namespace cs2120f24
open PLExpr


-- Variables
def v₀ : BoolVar := ⟨0⟩
def v₁ : BoolVar := ⟨1⟩
def v₂ : BoolVar := ⟨2⟩

/-!
Variable expressions
-/
def P : PLExpr := { v₀ }
def Q : PLExpr := { v₁ }
def R : PLExpr := { v₂ }

/-
Operator expression: abstract syntax
-/

/-
In the first example below, we explciitly
state that the name, "hard_to_read", should
be bound to the expression our *abstract*
syntax representing the expression *P ∧ Q*,
using concrete syntactic notations. You can
see how much easier it is to use standard
mathematical notations, especially when each
has standard precedence and associativity.
-/

def P_and_Q_abstract_syntax : PLExpr := bin_op_expr Bin_op.and P Q
def P_and_Q_concrete_syntax := P ∧ Q

/-
Hover your cursor over #reduce. You will see that
Lean "de-sugars" the concrete to *the same abstract
syntax: bin_op_expr bin_op.and {var_[0]} {var_[1]}.
Note that {var_[0]} is exactly our concrete notation
for Expr.var_expr (var.mk 0). Expr.var_expr constructs
an expression from a variable, and the variable here
is the first (0th) in our endless supply of variables.
-/
#reduce P_and_Q_concrete_syntax

/-!
Properties!
-/

#reduce is_sat P
#reduce is_unsat P
#reduce is_valid P

#reduce is_sat (P ∨ Q)
#reduce is_unsat (P ∨ Q)
#reduce is_valid (P ∨ Q)

#reduce is_sat (P ∧ Q)
#reduce is_unsat (P ∧ Q)
#reduce is_valid (P ∧ Q)






/-!
You can use #check to see the types of all these things.
Hover over the Lean #check commands to see the output.
-/

#check 0                                -- natural number
#check BoolVar.mk                           -- constructor takes nat
#check BoolVar.mk 0                         -- applied to a nat yields BoolVar

#check PLExpr                             -- the type of expression values

-- quick introduction to "partial evaluation"
#check PLExpr.bin_op_expr                 -- binary connective expression builder
#check PLExpr.bin_op_expr Bin_op.and      -- specializ to *and* expression builder
#check PLExpr.bin_op_expr Bin_op.and P    -- applied to one expression: whaah?
#check PLExpr.bin_op_expr Bin_op.and P Q  -- applied to two expressions, voila!


-- now wouldn't you rather write this?!
#check P ∧ Q                            -- same thing with concrete syntax

/-
Now you can construct as many syntactically correct
expressions in propositional logic as you want. We
have formally specified the exact structures of the
values/terms, in Lean, that we will use for literal,
variable, and (unary and binary) operator expressions.

Given the rules we've defined for constructing these
propositional logic expression (Expr) values/terms,
it's simply not possible to construct terms that are
not syntactically correct. Lean continually checks to
ensure that terms are of the types they are meant to
be. If you get one of these structures wrong, Lean
will reject it as not being a value of the right type,
namely of the type of terms defined by the construction
"rules" we've given to the Expr type.

Note, however, that we've said nothing at all yet
about what all of these expressions should be defined
to mean!
-/

/-!
Interpretations. Remember that interpretations
are functions and won't print well natively.
-/

#reduce nat_to_bin 5
#reduce list_nat_zero_pad (nat_to_bin 5) 6
#reduce mk_bit_row_pad 5 6

def row_5_vars_3 := list_bool_from_row_index_and_cols 5 3
#reduce row_5_vars_3  -- [true,false,true]


def lb2i := list_bool_to_interp [true,true,true]
def r5v3 := list_bool_to_interp row_5_vars_3
#eval! interp_to_string lb2i 5 -- bug
#eval! interp_to_string r5v3 5 -- bug


def i1 := list_interps_for_n_variables 1
def i2 := list_interps_for_n_variables 2
def i3 := list_interps_for_n_variables 3
def i4 := list_interps_for_n_variables 4
#reduce interps_to_list_list_string i1 4
#reduce interps_to_list_list_string i2 4
#reduce interps_to_list_list_string i3 4
#reduce interps_to_list_list_string i4 4

#reduce  (mk_bit_row_pad 5 6)
#reduce bit_list_to_bool_list (mk_bit_row_pad 5 6)
#reduce list_bool_from_row_index_and_cols 5 6

-- this is a function and so doesn't print nicely
#reduce row_index_and_vars_to_interp 6 3


#reduce interp_to_string (row_index_and_vars_to_interp 6 3) 5

#eval! (list_bool_from_row_index_and_cols 4 3).toString
#reduce interp_to_string (row_index_and_vars_to_interp 2 2) 4
/-!
Truth Table Outputs
-/


#check (P ∧ Q)

#reduce (truth_table_outputs (P ∧ Q)).length
#eval! (truth_table_outputs (P ∧ Q)).toString
#eval! (truth_table_outputs (P)).length
#eval! (truth_table_outputs (P)).toString



end cs2120f24
