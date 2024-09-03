namespace cs2120f24

/-!
# Language of Arithmetic Expressions

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

## Syntax
-/

-- arithmetic variables
structure nat_var where
  (index : Nat)

-- type of interpretation of arithmetic variables
def arith_interp := nat_var → Nat

inductive arith_UnOp where
| inc
| dec

inductive arith_BinOp where
| add
| sub
| mul


-- abstract syntax of expresion language
inductive arith_expr
| lit (n : Nat)
| var (v : var)
| UnOp (op : arith_UnOp) (e : arith_expr)
| BinOp (op : arith_BinOp) (e1 e2 : arith_expr)

-- concrete syntax
notation "++" n => arith_expr.arith_UnOp.inc n
notation "--" n => arith_expr.arith_UnOp.dec n
