import Cs2120f24.Lectures.«02_prop_logic».formal.interpretation
import Cs2120f24.Lectures.«02_prop_logic».formal.properties
import Cs2120f24.Lectures.«02_prop_logic».formal.utilities

namespace cs2120f24
open PLExpr


/-!
SYNTAX
-/

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

def P_and_Q_abstract : PLExpr := bin_op_expr BinOp.and P Q
def P_and_Q_concrete:= P ∧ Q
#reduce P_and_Q_concrete

/-
Truth table output vectors
-/

#reduce truthTableOutputVector (P ∧ Q)

/-!
Properties!
-/

#reduce is_sat P
#reduce is_unsat P
#reduce is_valid P

#reduce is_sat (P ∨ ¬P)
#reduce is_unsat (P ∨ ¬P)
#reduce is_valid (P ∨ ¬P)

#reduce is_sat (P ∧ ¬P)
#reduce is_unsat (P ∧ ¬P)
#reduce is_valid (P ∧ ¬P)

#reduce is_sat (P ∨ Q)
#reduce is_unsat (P ∨ Q)
#reduce is_valid (P ∨ Q)

#reduce is_sat (P ∧ Q)
#reduce is_unsat (P ∧ Q)
#reduce is_valid (P ∧ Q)


/-!
Truth Table Outputs
-/


#check (P ∧ Q)

#reduce (truthTableOutputVector (P ∧ Q)).length
#eval! (truthTableOutputVector (P ∧ Q)).toString
#eval! (truthTableOutputVector (P)).length
#eval! (truthTableOutputVector (P)).toString



end cs2120f24
