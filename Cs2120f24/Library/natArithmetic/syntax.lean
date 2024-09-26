namespace cs2120f24.natArithmetic.syntax


-- variables indexed by Nat
structure Var : Type where
(index: Nat)


-- Unary arithmetic operators.
inductive UnOp : Type where
| inc
| dec
| doub
| halve
| fac


-- Binary arithmetic operators
inductive BinOp : Type where
| add
| sub
| mul


-- Binary relational operators
inductive RelOp : Type
| eq
| le
| lt
| ge
| gt


-- Syntax of arithmetic (Nat returning) expressions
inductive Expr : Type where
| lit (from_nat : Nat) : Expr
| var (from_var : Var)
| unOp (op : UnOp) (e : Expr)
| binOp (op : BinOp) (e1 e2 : Expr)


-- Syntax of relational (Bool returning) expressions
inductive RelExpr : Type where
| mk (op : RelOp) (e1 e2 : Expr)


-- Nnotations for our abstract syntax
notation " { " v " } " => Expr.var v
notation " [ " n " ] " => Expr.lit n


-- Lean knows precedences and associativites for standard notations
notation:max e " ! " => Expr.unOp UnOp.fac e
notation e1 " + " e2 => Expr.binOp BinOp.add e1 e2
notation e1 " - " e2 => Expr.binOp BinOp.sub e1 e2
notation e1 " * " e2 => Expr.binOp BinOp.mul e1 e2


-- including for these relational operators
notation e1 " = " e2 => RelExpr.mk RelOp.eq e1 e2
notation e1 " ≤ " e2 => RelExpr.mk RelOp.le e1 e2
notation e1 " < " e2 => RelExpr.mk RelOp.lt e1 e2
notation e1 " ≥ " e2 => RelExpr.mk RelOp.ge e1 e2
notation e1 " > " e2 => RelExpr.mk RelOp.gt e1 e2


end cs2120f24.natArithmetic.syntax
