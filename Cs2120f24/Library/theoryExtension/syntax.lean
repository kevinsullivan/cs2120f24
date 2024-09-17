import «Cs2120f24».Library.natArithmetic.semantics

namespace cs2120f24

/-!
# Propositional Logic with Nat Arithmetic

The key idea in our semantic evaluation of a propositional
logic expression is that we can compute the Boolean meanings
of all the kinds of subexpressions -- operator, variable, and
literal -- each reducing to a Boolean value.

But now we've met another kind expression that reduces to a
Boolean, namely an arithmetic *relational* expression, such
as X < Y, where X and Y are now *arithmetic* values, having
natural numbers as their meanings, and X < Y is a *predicate*
expression.

The insight we develop now is that relational expressions are
also expresions with Boolean meansings, so we should be able
to incorporate them into our *propositional logic* language,
so we can write expressions like this: (X < Y) ∧ (Z == 3). Be
sure to see how "at the top level" this is still an expression
in propositional logic, but we've added a new expression type,
for arithmetic relational expression.


## Abstract Syntax of Propositional Logic with Arithmetic
-/

inductive PLExpr : Type
| lit_expr (from_bool : Bool) : PLExpr
| var_expr (from_var : BoolVar)
| arith_expr (aExpr : arithExpr)
| un_op_expr (op : UnOp) (e : PLExpr)
| bin_op_expr (op : BinOp) (e1 e2 : PLExpr)
deriving Repr

/-!
The "deriving Repr" here is a detail you can ignore for
now. It's explained in the book. In a nutshell it causes
Lean to try to synthesize a function to convert any value
of this type to a string to help in presenting values as
properly formatted output strings. Anyway, a detail.
-/

/-
Every type encloses the names of its constructors
in a snamespace with the same name as the type. So
Expr is now a namespace, and the constructor names
(lit_expr, etc.) are referred to as Expr.lit_expr,
etc. To avoid having to repeat that Expr. bit all
the time, one can "open" the namespace. Just don't
do this if it would result in names having multiple
different definitions being "directly visible."
-/
open PLExpr



/-
## Concrete Syntax: All the Usual Notations

A well designed, user tested, concrete syntax for a
given formal language can be a huge aid to the human
of abstract formal definitions in that language. We
prefer to write (3 + 4) over (add 3 4), for example.
We don't expect you to have justifiable confidence
in your deep understanding of this notation stuff at
this point! We encourge you to follow it carefully
to get the gist.
-/

-- (lit true) and (lit false) expressions
-- a variable expression constructed from from a variable

-- our single unary connective, *not* (¬)
-- we set it to have maximum precedence (binding strength)

/-!
Here are concrete notations for our binary connectives.
The letter "l" after infix specifies left associativity.
The numbers after the colons specify binding strengths.
The de-sugared versions follow after the arrows.
-/

notation:max " ⊤ " => (PLExpr.lit_expr true)
notation:max " ⊥ " => (lit_expr false)
notation:max "{" v "}" => (var_expr v)
notation:max "¬" p:40 => un_op_expr UnOp.not p
infixr:35 " ∧ "  =>  PLExpr.bin_op_expr BinOp.and
infixr:30 " ∨  "  => PLExpr.bin_op_expr BinOp.or
infixr:20 " ↔ " => bin_op_expr BinOp.iff
infixr:25 " ⇒ " => bin_op_expr BinOp.imp

/-
Now head off to the Main.lean file in this same directory,
copy it into your MyWork directory tree, and plan around with
building expressions in our logic.
-/

end cs2120f24
