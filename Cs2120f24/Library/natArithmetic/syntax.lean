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
notation:max " { " v " } " => Expr.var v
notation:max " [ " n " ] " => Expr.lit n


-- Lean knows precedences and associativites for standard notations
notation:max e " ! " => Expr.unOp UnOp.fac e
infixl:65 " + " => Expr.binOp BinOp.add
infixl:65 " - " => Expr.binOp BinOp.sub
infixl:70 " * " => Expr.binOp BinOp.mul


-- including for these relational operators
infix:50 " = " => RelExpr.mk RelOp.eq
infix:50 " ≤ " => RelExpr.mk RelOp.le
infix:50 " < " => RelExpr.mk RelOp.lt
infix:50 " ≥ " => RelExpr.mk RelOp.ge
infix:50 " > " => RelExpr.mk RelOp.gt

end cs2120f24.natArithmetic.syntax
