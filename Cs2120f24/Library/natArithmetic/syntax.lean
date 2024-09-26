namespace cs2120f24.natArithmetic.syntax

/-!
# Syntax: Expression Language of Arithmetic
-/

structure NatVar : Type where
(index: Nat)

/-!
Unary arithmetic operators.
-/
inductive UnOp : Type where
| inc
| dec
| doub
| halve
| fac

/-!
Binary arithmetic operators
-/
inductive BinOp : Type where
| add
| sub
| mul

/-!
Binary relational operators
-/
inductive RelOp : Type
| eq
| le
| lt
| ge
| gt

/-!
Syntax of arithmetic (Nat returning) expressions
-/
inductive ArithExpr : Type where
| lit (from_nat : Nat) : ArithExpr
| var (from_var : NatVar)
| unOp (op : UnOp) (e : ArithExpr)
| binOp (op : BinOp) (e1 e2 : ArithExpr)

/-!
Syntax of relational (Bool returning) expressions
-/
inductive RelExpr : Type where
| mk (op : RelOp) (a1 a2 : ArithExpr)

/-!
Concrete notations for our abstract syntax. Note: Lean

-/
notation " { " v " } " => ArithExpr.var v
notation " [ " n " ] " => ArithExpr.lit n

-- Lean knows precedences and associativites for standard notations
notation e " ! " => ArithExpr.unOp UnOp.fac e
notation e1 " + " e2 => ArithExpr.binOp BinOp.add e1 e2
notation e1 " - " e2 => ArithExpr.binOp BinOp.sub e1 e2
notation e1 " * " e2 => ArithExpr.binOp BinOp.mul e1 e2

notation a1 " ≤ " a2 => RelExpr.mk RelOp.le a1 a2
notation a1 " = " a2 => RelExpr.mk RelOp.eq a1 a2

end cs2120f24.natArithmetic.syntax
