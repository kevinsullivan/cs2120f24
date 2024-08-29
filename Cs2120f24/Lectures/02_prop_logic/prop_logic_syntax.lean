namespace cs2120f24

/-!
## Propositional Logic: Syntax, Sematics, Satisfiability

This section of the exam simply includes our formal
definition of the syntax and semantics of propositional
logic and of functions that determine whether a given
expression is valid, satisfiable, or unsatisfiable.

### Syntax

The syntax specifies the set of all and only syntactically
correct propositional logic expressions. Roughly speaking,
the syntax defines "literal" and "variable" expressions and
a collection of composition operators that take any smaller
expressions as arguments and produce larger expressions. We
are not talking abouting semantic meanings yet: just proper
formation of propositional logic expressions.

We will specify the syntax in terms of
- two literal expressions (litTrue and litFalse)
-/

/-
structure litExpr : Type :=
(fromBool : Bool)
-/

-- inductive ç : Type
-- | litTrue : LiteralExpr
-- | litFalse : LiteralExpr

/-
Next come variable expressions. to support this concept, we
introduce the type of *variables*. A *variable expression* is
parameterized by (wraps) a variable. To have an inexhaustible
supply of different variables, we specify that each instance
of the var type will be constructed from a natural numbers,
and it in turn uniquely specifies that one variable "thing."
-/
-- variables
structure var : Type :=
(n: Nat)

/-
Different variable expressions "wrapping" the same underlying
variable will be treated as identical in our implementation of
propositional logic.
-/

-- structure VariableExpression : Type :=
-- (from_variable : var)


/-
Finally we have *operator* or *logical connective* expressions,
such as ¬X or X ∧ Y. ¬ is a unary operator, building a bigger
expression (with a not in front) from any given smaller one.
The and operator on the other hand is a binary connective or
operator, in that it constructs a new expression from *two*
smaller expressions, as in "P ∧ Q", where P and Q can stand for
any such smaller expressions.
-/

-- we have only one unary connective operator: not
inductive un_op : Type | not

-- structure UnaryOperatorExpression : Type :=
-- (op : unary_op)

-- seeral binary expression-building (connective) operators
inductive bin_op : Type
| and
| or
| imp
| iff

-- structure BinaryOperatorExpression : Type :=
-- (op : bin_op)

-- expressions (abstract syntax)
inductive Expr : Type
| lit_expr (fromBool : Bool) : Expr
| var_expr (v : var)
| un_op_expr(op : un_op) (e : Expr)
| bin_op_expr (op : bin_op) (e1 e2 : Expr)

open Expr

-- concrete syntax: notations fro the two literal expressions
notation " ⊤ " => lit_expr true
notation " ⊥ " => lit_expr false

-- our made up non-standard notation for a variable expression
notation "{"v"}" => var_expr v

-- the one unary connective, ¬
prefix:max "¬" => Expr.un_op_expr un_op.not

-- and most of the most important binary connectives
infixr:35 " ∧ " => bin_op_expr bin_op.and
infixr:30 " ∨ " => bin_op_expr bin_op.or
infixr:25 " ⇒ " =>  bin_op_expr bin_op.imp
infixr:20 " ⇔ " => bin_op_expr bin_op.iff

end cs2120f24
