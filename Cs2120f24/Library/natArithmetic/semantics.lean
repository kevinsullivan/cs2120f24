import «cs2120f24».Library.natArithmetic.syntax
import «cs2120f24».Library.natArithmetic.domain


namespace cs2120f24.natArithmetic



def evalUnOp : UnOp → (Nat → Nat)
| UnOp.inc => Nat.succ
| UnOp.dec => Nat.pred
| UnOp.doub => (fun n => n * 2)
| UnOp.halv => (fun n => n / 2)
| UnOp.fac => fac

-- predicates
-- | isZero =>


#check Expr

-- Semantics (incomplete, to be finished in homework)
def arithEval : Expr → (Var → Nat) → Nat
| Expr.lit (fromNat : Nat),      i =>  fromNat
| Expr.var (fromVar : Var), i => i fromVar
| Expr.unOp op e,                i => (evalUnOp op) sorry
| Expr.binOp op e1 e2,           i => 0

end cs2120f24.natArithmetic
