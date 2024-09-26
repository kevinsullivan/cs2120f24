import «Cs2120f24».Library.propLogicWithArith.syntax
import «Cs2120f24».Library.propLogicWithArith.domain
import «Cs2120f24».Library.natArithmetic.semantics

/-!
# Semantics of Propositional Logic with Arithmetic Relations
-/

namespace cs2120f24.propLogicwithArith.semantics

open cs2120f24.propLogicWithArith.syntax

def evalUnOp : UnOp → (Bool → Bool)
| (UnOp.not) => not

def evalBinOp : BinOp → (Bool → Bool → Bool)
| BinOp.and => and
| BinOp.or => or
| BinOp.imp => propLogicwithArith.domain.imp
| BinOp.iff => cs2120f24.propLogicwithArith.domain.iff

abbrev BoolInterp := BoolVar → Bool -- varInterp would be better name

#check natArithmetic.semantics.evalExpr
#check natArithmetic.syntax.ArithExpr
#check natArithmetic.semantics.evalRelOp
#check natArithmetic.syntax.NatVar

abbrev ArithInterp := natArithmetic.syntax.NatVar → Nat

open cs2120f24.natArithmetic

#check natArithmetic.syntax.RelOp

def evalPLAExpr : PLAExpr → BoolInterp → ArithInterp → Bool
| (PLAExpr.lit_expr b),             _, _ => b
| (PLAExpr.var_expr v),           i, _ => i v
| (PLAExpr.un_op_expr op e),      i, a => (evalUnOp op) (evalPLAExpr e i a)
| (PLAExpr.bin_op_expr op e1 e2), i, a => (evalBinOp op) (evalPLAExpr e1 i a) (evalPLAExpr e2 i a)
| (PLAExpr.rel_op_expr op a1 a2), _, a => (natArithmetic.semantics.evalRelOp op)
                                           (natArithmetic.semantics.evalExpr a1 a)
                                           (natArithmetic.semantics.evalExpr a2 a)
#check natArithmetic.syntax.RelOp.le

#eval evalPLAExpr
  (PLAExpr.rel_op_expr
    (natArithmetic.syntax.RelOp.le)
    (natArithmetic.syntax.ArithExpr.lit 9)
    (natArithmetic.syntax.ArithExpr.lit 6))
    (fun _ => true)
    (fun _ => 0)

#check ([5] : syntax.ArithExpr)

#eval semantics.evalRelExpr
  ([9] ≤ [8])
  (fun _ => 0)

end cs2120f24.propLogicwithArith.semantics
