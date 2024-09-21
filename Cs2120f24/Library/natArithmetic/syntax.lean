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
deriving Repr


-- pull from semantic domain: give syntax to concepts
inductive UnOp : Type
inductive unOp
| inc
| dec
| doub
| halv
| fac
deriving Repr


-- pull from semantic domain: give syntax to concepts
inductive BinOp : Type
| add
| sub
| mul
deriving Repr

-- abstract syntax

inductive Expr : Type
| lit (from_nat : Nat) : Expr
| var (from_var : Var)
| unOp (op : UnOp) (e : Expr)
| binOp (op : BinOp) (e1 e2 : Expr)
-- deriving Repr

-- concrete syntax
notation " { " v " } " => Expr.var v
notation " [ " n " ] " => Expr.lit n
notation e " ! " => Expr.unOp UnOp.fac e
notation e1 " + " e2 => Expr.binOp BinOp.add e1 e2
notation e1 " - " e2 => Expr.binOp BinOp.sub e1 e2
notation e1 " * " e2 => Expr.binOp BinOp.mul e1 e2

end cs2120f24.natArithmetic
