import «cs2120f24».Library.natArithmetic.syntax
import «cs2120f24».Library.natArithmetic.domain


namespace cs2120f24.natArithmetic

def evalUnOp : UnOp → (Nat → Nat)
| UnOp.inc => Nat.succ
| UnOp.dec => Nat.pred
| UnOp.doub => (fun n => n * 2)
| UnOp.halv => (fun n => n / 2)
| UnOp.fac => fac

def evalBinOp : BinOp → (Nat → Nat → Nat)
| BinOp.add => Nat.add
| BinOp.sub => Nat.sub
| BinOp.mul => Nat.mul

def Interp := Var → Nat

def evalVar : Var → Interp → Nat
| v, i => i v

-- Semantics (incomplete, to be finished in homework)
def evalExpr : Expr → (Var → Nat) → Nat
| Expr.lit (n : Nat),    _ =>  n
| Expr.var (v : Var),    i => i v
| Expr.unOp op e,        i => (evalUnOp op) (evalExpr e i)
| Expr.binOp op e1 e2,   i => (evalBinOp op) (evalExpr e1 i) (evalExpr e2 i)

end cs2120f24.natArithmetic
