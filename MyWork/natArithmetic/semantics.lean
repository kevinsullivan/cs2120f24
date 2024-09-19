import «cs2120f24».Library.natArithmetic.syntax

namespace cs2120f24.arith

/-!
Factorial function -- extra credit
-/

-- case analysis on constructors
-- prefer Lean-provided notations
def fac : Nat → Nat
| 0 => 0                        -- Nat.zero
| n' + 1 => (n' + 1) * fac n'   -- Nat.succ n'

def unOpInterp : ArithUnOp → (Nat → Nat)
| ArithUnOp.fac => fac

def binOpInterp : ArithBinOp → (Nat → Nat → Nat)
| ArithBinOp.add => Nat.add
| ArithBinOp.sub => Nat.sub
| ArithBinOp.mul => Nat.mul

def arithVarInterp := ArithVar → Nat

-- Semantics (incomplete, to be finished in homework)
def arithEval : ArithExpr → arithVarInterp → Nat
| ArithExpr.lit (fromNat : Nat),      i =>  fromNat
| ArithExpr.var (fromVar : ArithVar), i => i fromVar
| ArithExpr.unOp op e,                i => (unOpInterp op) (arithEval e i)
| ArithExpr.binOp op e1 e2,           i => (binOpInterp op) (arithEval e1 i) (arithEval e2 i)

end cs2120f24.arith
