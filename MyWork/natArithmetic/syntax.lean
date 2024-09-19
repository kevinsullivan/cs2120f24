namespace cs2120f24.arith

/-!
# Syntax: Expression Language of Arithmetic

Ok, so now that we have the semantic domain, what
about our expression language? We'll you write it
almost exactly as for predicate logic, but now the
arguments and operators are arithmetic, which is to
say they yield arithmetic results (natural numbers
in this work).

Just as before we have literals, as before, we'll
have a *literal* (arithmetic) expression for each
Nat; we'll have variables and interpretations that
take variables arguments and return the numerical
values that the particular interpretation assigns
to them.
-/

structure ArithVar : Type :=
  mk :: (index: Nat)
deriving Repr


inductive ArithUnOp : Type
| fac
deriving Repr


inductive ArithBinOp : Type
| add
| sub
| mul
deriving Repr

-- abstract syntax
inductive ArithExpr : Type
| lit (from_nat : Nat) : ArithExpr
| var (from_var : ArithVar)
| unOp (op : ArithUnOp) (e : ArithExpr)
| binOp (op : ArithBinOp) (e1 e2 : ArithExpr)
deriving Repr

-- concrete syntax
notation " { " v " } " => ArithExpr.var v
notation " [ " n " ] " => ArithExpr.lit n
notation e " ! " => ArithExpr.unOp ArithUnOp.fac e
notation e1 " + " e2 => ArithExpr.binOp ArithBinOp.add e1 e2
notation e1 " - " e2 => ArithExpr.binOp ArithBinOp.sub e1 e2
notation e1 " * " e2 => ArithExpr.binOp ArithBinOp.mul e1 e2

end cs2120f24.arith
