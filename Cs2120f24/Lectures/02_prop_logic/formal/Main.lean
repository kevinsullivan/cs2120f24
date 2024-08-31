import Cs2120f24.Lectures.«02_prop_logic».formal.syntax
import Cs2120f24.Lectures.«02_prop_logic».formal.semantics

open cs2120f24
open Expr


-- Variables
def v₀ : var := ⟨0⟩
def v₁ : var := ⟨1⟩
def v₂ : var := ⟨2⟩

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

def P_and_Q_abstract_syntax := bin_op_expr bin_op.and P Q
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
You can use #check to see the types of all these things.
Hover over the Lean #check commands to see the output.
-/

#check 0                                -- natural number
#check var.mk                           -- constructor takes nat
#check var.mk 0                         -- applied to a nat yields var
#check Expr.bin_op_expr                 -- binary connective expression builder
#check Expr.bin_op_expr bin_op.and      -- specializ to *and* expression builder
#check Expr.bin_op_expr bin_op.and P Q  -- applied to two expressions, voila!
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
