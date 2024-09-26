import «cs2120f24».Library.natArithmetic.syntax
import «cs2120f24».Library.natArithmetic.domain

namespace cs2120f24.natArithmetic.semantics


-- given syntactic operator terms, return corresponding Nat- and Bool-valued functions
open natArithmetic.syntax

def evalUnOp : UnOp → (Nat → Nat)
| UnOp.inc    => Nat.succ
| UnOp.dec    => Nat.pred
| UnOp.doub   => (fun n => n * 2)
| UnOp.halve  => (fun n => n / 2)
| UnOp.fac    => domain.fac

def evalBinOp : BinOp → (Nat → Nat → Nat)
| BinOp.add => Nat.add
| BinOp.sub => Nat.sub
| BinOp.mul => Nat.mul

def evalRelOp : RelOp → (Nat → Nat → Bool)
| RelOp.eq => domain.eq    -- eq is from from natArithmetic.domain
| RelOp.le => domain.le    -- etc.
| RelOp.lt => domain.lt
| RelOp.ge => domain.ge
| RelOp.gt => domain.gt


-- Helper function to evaluate a variable under an interpretation


-- A function for evaluating variable values under given interpretations
def Interp := Var → Nat

def evalVar : Var → Interp → Nat
| v, i => i v   -- apply interpretation function i to variable v


-- Semantic evaluation of arithmetic expression (yielding Nat)
def evalExpr : Expr → Interp → Nat
| Expr.lit n,          _   =>  n
| Expr.var v,          i   => (evalVar v i)
| Expr.unOp op e,      i   => (evalUnOp op) (evalExpr e i)
| Expr.binOp op e1 e2, i   => (evalBinOp op) (evalExpr e1 i) (evalExpr e2 i)


-- Semantic evaluation of arithmetic relational expression (yielding Bool)
def evalRelExpr : syntax.RelExpr → Interp → Bool
| RelExpr.mk op a1 a2, i =>  (evalRelOp op) (evalExpr a1 i) (evalExpr a2 i)


end cs2120f24.natArithmetic.semantics
