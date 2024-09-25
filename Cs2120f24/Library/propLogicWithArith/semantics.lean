import «Cs2120f24».Library.natArithmetic.semantics
import «Cs2120f24».Library.propLogicWithArith.syntax
import «Cs2120f24».Library.propLogicWithArith.domain


/-!
# Semantics
-/

namespace cs2120f24.propLogicwithArith

open propLogicWithArith
open natArithmetic
open PLExpr

def evalUnOp : propLogicWithArith.UnOp → (Bool → Bool)
| (UnOp.not) => not

def evalBinOp : propLogicWithArith.BinOp → (Bool → Bool → Bool)
| BinOp.and => and
| BinOp.or => or
| BinOp.imp => imp
| BinOp.iff => iff

abbrev BoolInterp := BoolVar → Bool -- varInterp would be better name

#check evalExpr
#check ArithExpr
#check evalRelOp

abbrev ArithInterp := Var → Nat

def evalPLExpr : PLExpr → BoolInterp → ArithInterp → Bool
| lit_expr b,             _, _ => b
| (var_expr v),           i, a => i v
| (un_op_expr op e),      i, a => (evalUnOp op) (evalPLExpr e i a)
| (bin_op_expr op e1 e2), i, a => (evalBinOp op) (evalPLExpr e1 i a) (evalPLExpr e2 i a)
| (rel_op_expr op a1 a2), i, a => (evalRelOp op)
                                  (evalExpr a1 a)
                                  (evalExpr a2 a)
#check RelOp.le
#eval evalPLExpr (PLExpr.rel_op_expr (RelOp.le) (ArithExpr.lit 9) (ArithExpr.lit 8)) (λ v => true) (λ v => 0)

end cs2120f24.propLogicwithArith
