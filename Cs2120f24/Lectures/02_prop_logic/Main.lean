import Cs2120f24.Lectures.«02_prop_logic».prop_logic_syntax

open cs2120f24
open Expr


-- Variables
def v₀ : var := var_[0]
def v₁ : var := var_[1]
def v₂ : var := var_[2]

/-!
Variable expressions
-/
def P : Expr := { v₀ }
def Q : Expr := { v₁ }
def R : Expr := { v₂ }

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

def P_and_Q_abstract := bin_op_expr bin_op.and P Q
def P_and_Q_concrete := P ∧ Q

#reduce P_and_Q_concrete  -- desugars to abstract syntax

/-
Now you can make as many syntactically correct
expressions (proposisions!) in propositional logic
as you might want. Furthermore, you can't construct
any syntactically incorrect ones! The syntax does
not allow it.

Note, however, that we've said nothing at all yet
about what all of these expressions should be defined
to mean!
-/
