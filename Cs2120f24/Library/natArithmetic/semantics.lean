import «cs2120f24».Library.natArithmetic.syntax
import «cs2120f24».Library.natArithmetic.domain

namespace cs2120f24.natArithmetic

#check UnOp


def evalUnOp : UnOp → (Nat → Nat)
| inc => Nat.succ
| dec => Nat.pred
| doub => (fun n => n * 2)
| halv => (fun n => n / 2)
| fac => fac

-- predicates
-- | isZero =>


#check ArithExpr

-- Semantics (incomplete, to be finished in homework)
def arithEval : ArithExpr → (ArithVar → Nat) → Nat
| ArithExpr.lit (fromNat : Nat),      i =>  fromNat
| ArithExpr.var (fromVar : ArithVar), i => i fromVar
| ArithExpr.unOp op e,                i => (evalUnOp op) () ()
| ArithExpr.binOp op e1 e2,           i => 0

end cs2120f24.natArithmetic
