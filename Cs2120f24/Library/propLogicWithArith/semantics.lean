import «Cs2120f24».Library.propLogicWithArith.syntax
import «Cs2120f24».Library.propLogicWithArith.domain
import «Cs2120f24».Library.natArithmetic.semantics


/-!
# Semantics
-/

namespace cs2120f24.propLogicwithArith

open propLogicWithArith

-- open natArithmetic
open PLExpr

def evalUnOp : propLogicWithArith.UnOp → (Bool → Bool)
| (UnOp.not) => not

def evalBinOp : propLogicWithArith.BinOp → (Bool → Bool → Bool)
| BinOp.and => and
| BinOp.or => or
| BinOp.imp => imp
| BinOp.iff => iff

abbrev BoolInterp := BoolVar → Bool -- varInterp would be better name

#check natArithmetic.evalExpr
#check natArithmetic.ArithExpr
#check natArithmetic.evalRelOp
#check natArithmetic.NatVar

abbrev ArithInterp := natArithmetic.NatVar → Nat

def evalPLExpr : PLExpr → BoolInterp → ArithInterp → Bool
| lit_expr b,             _, _ => b
| (var_expr v),           i, _ => i v
| (un_op_expr op e),      i, a => (evalUnOp op) (evalPLExpr e i a)
| (bin_op_expr op e1 e2), i, a => (evalBinOp op) (evalPLExpr e1 i a) (evalPLExpr e2 i a)
| (rel_op_expr op a1 a2), _, a => (natArithmetic.evalRelOp op)
                                  (natArithmetic.evalExpr a1 a)
                                  (natArithmetic.evalExpr a2 a)
#check natArithmetic.RelOp.le
#eval evalPLExpr (PLExpr.rel_op_expr (natArithmetic.RelOp.le) (natArithmetic.ArithExpr.lit 9) (natArithmetic.ArithExpr.lit 10)) (λ _ => true) (λ _ => 0)

end cs2120f24.propLogicwithArith
