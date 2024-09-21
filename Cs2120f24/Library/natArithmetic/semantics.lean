import «cs2120f24».Library.natArithmetic.syntax
import «cs2120f24».Library.natArithmetic.domain

namespace cs2120f24.arith




def evalUnOp : unOp → (Nat → Nat)
| unOp.inc => Nat.succ
| unOp.dec => Nat.pred
| unOp.doub => (fun n => n * 2)
| unOp.halv => (fun n => n / 2)
| unOp.fac => fac

-- predicates
-- | isZero =>


#check ArithExpr

-- Semantics (incomplete, to be finished in homework)
def arithEval : ArithExpr → (ArithVar → Nat) → Nat
| ArithExpr.lit (fromNat : Nat),      i =>  fromNat
| ArithExpr.var (fromVar : ArithVar), i => i fromVar
| ArithExpr.unOp op e,                i => (evalUnOp op) () ()
| ArithExpr.binOp op e1 e2,           i => 0

end cs2120f24.arith
