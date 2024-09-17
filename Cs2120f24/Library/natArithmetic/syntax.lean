namespace cs2120f24.arith

/-!
# Expression Language of Arithmetic

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


/-!
## Syntax
-/

-- arithmetic variables
structure natVar where
  (index : Nat)

-- unary arithmetic operators (here increment, decrement)
inductive arith_UnOp where
| fac

-- binary arithemtic operators (here +, -, and *)
inductive arith_BinOp where
| add
| sub
| mul

-- abstract syntax
inductive arithExpr
| lit (n : Nat)
| var (v : natVar)
| UnOp (op : arith_UnOp) (e : arithExpr)
| BinOp (op : arith_BinOp) (e1 e2 : arithExpr)

-- concrete syntax
notation " { " v " } " => arithExpr.var v
notation:max "++" n => arithExpr.UnOp arith_UnOp.inc n
notation:max "--" n => arithExpr.UnOp arith_UnOp.dec n
notation e1 "+" e2 => arithExpr.BinOp arith_BinOp.add e1 e2
notation e1 "-" e2 => arithExpr.BinOp arith_BinOp.sub e1 e2
notation e1 "*" e2 => arithExpr.BinOp arith_BinOp.mul e1 e2

end cs2120f24.arith
