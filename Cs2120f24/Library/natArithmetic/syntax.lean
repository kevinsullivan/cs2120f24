namespace cs2120f24.natArithmetic

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

structure Var : Type :=
  mk :: (index: Nat)


-- pull from semantic domain: give syntax to concepts
inductive UnOp : Type where
| inc
| dec
| doub
| halve
| fac

-- pull from semantic domain: give syntax to concepts
inductive BinOp : Type where
| add
| sub
| mul

inductive RelOp : Type
| eq
| le
| lt
| ge
| gt

inductive ArithExpr : Type where
| lit (from_nat : Nat) : ArithExpr
| var (from_var : Var)
| unOp (op : UnOp) (e : ArithExpr)
| binOp (op : BinOp) (e1 e2 : ArithExpr)

inductive RelExpr : Type where
| mk (op : RelOp) (a1 a2 : ArithExpr)

-- concrete syntax
notation " { " v " } " => ArithExpr.var v
notation " [ " n " ] " => ArithExpr.lit n
notation e " ! " => ArithExpr.unOp UnOp.fac e
notation e1 " + " e2 => ArithExpr.binOp BinOp.add e1 e2
notation e1 " - " e2 => ArithExpr.binOp BinOp.sub e1 e2
notation e1 " * " e2 => ArithExpr.binOp BinOp.mul e1 e2

end cs2120f24.natArithmetic
