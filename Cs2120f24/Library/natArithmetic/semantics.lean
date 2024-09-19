import «cs2120f24».Library.natArithmetic.syntax

namespace cs2120f24.arith

#check ArithExpr

-- Semantics (incomplete, to be finished in homework)
def arithEval : ArithExpr → (ArithVar → Nat) → Nat
| ArithExpr.lit (fromNat : Nat),      i =>  fromNat
| ArithExpr.var (fromVar : ArithVar), i => i fromVar
| ArithExpr.unOp op e,                i => 0
| ArithExpr.binOp op e1 e2,           i => 0

end cs2120f24.arith
