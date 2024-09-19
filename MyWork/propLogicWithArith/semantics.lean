import Cs2120f24.Library.propLogicWithArith.syntax

namespace cs2120f24.arith

/-!
# Semantics
-/

def evalUnOp : UnOp → (Bool → Bool)
| (UnOp.not) => not

def evalBinOp : BinOp → (Bool → Bool → Bool)
| BinOp.and => and
| BinOp.or => or
| BinOp.imp => imp
| BinOp.iff => iff

open PLExpr

abbrev BoolInterp := BoolVar → Bool -- varInterp would be better name

def evalPLExpr : PLExpr → BoolInterp → ArithVarInterp → Bool
| lit_expr b,             _, _ => b
| (var_expr v),           i, a => i v
| (un_op_expr op e),      i, a => (evalUnOp op) (evalPLExpr e i a)
| (bin_op_expr op e1 e2), i, a => (evalBinOp op) (evalPLExpr e1 i a) (evalPLExpr e2 i a)
| arith_rel_expr e,       i, a => arithEval e a

end cs2120f24.arith
