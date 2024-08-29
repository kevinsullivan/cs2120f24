namespace cs2120f24

/-!
# Propositional Logic Syntax: Abstract and Concrete

This section of the exam simply includes our formal
definition of the syntax and semantics of propositional
logic and of functions that determine whether a given
expression is valid, satisfiable, or unsatisfiable.

## Abstract Syntax

The syntax specifies the set of all and only syntactically
correct propositional logic expressions. Roughly speaking,
the syntax defines "literal" and "variable" expressions and
a collection of expression-composiing operators that take
smaller expressions as arguments to yield larger expressions
as results. Remember: we're not talking abouting meanings,
just the possible forms of a propositional logic expression.
So let's get started.
-/

/-
First, for reasons that will become clear, we distinguish
between variables, and variable expressions, in our formal
definition. The following definition can be read as saying
that *var* is the type of variables and that a new variable
term/object/value can be constructed by applying the "mk"
*constructor* to any natural number, n. The following terms
are thus defined: (var.mk 0), (var.mk 1), etc. In ordinary
mathematical notations, we might say that v₀, v₁, etc. are
variables in our language. In other words, the set of all
variables is *indexed* by the natural numbers.
-/

-- variables
structure var : Type :=
mk :: (n: Nat)

/-
Next we specify the *syntactic operator* of propositional logic.
These are also known as the *logical connectives*. Each operator
takes one (not) or two (and, or, implies, iff) expressions as its
arguments and constructs a larger expression from them. Literal
and variable expressions are the basic starting points for building
larger expressions in propositional logic. For example, if P, Q,
and R are expressions, then so are (not P), (and P Q), etc.
-/

/-
We have only one unary expression-building operator: not. We
represent the collection of unary operators as the values of a
new data type we'll call un_op, for "unary operator".
-/

inductive un_op : Type | not

-- We similarly define bin_op as the set of available binary operators
inductive bin_op : Type
| and
| or
| imp
| iff

/-!
Now we get to the heart of the matter. With those preliminary
dependencies out of the way, we now formally specify the complete
(abstract) syntax of propositional logic. We do this by defining
yet another data type. The idea is that values of this type will
be (really will represent) expressions in propositional logic. In
fact, in Lean, this type specifies the set of *all* and *only*
the expressions legal in propositional logic.
-/

-- expressions (abstract syntax)
inductive Expr : Type
| lit_expr (fromBool : Bool) : Expr
| var_expr (v : var)
| un_op_expr(op : un_op) (e : Expr)
| bin_op_expr (op : bin_op) (e1 e2 : Expr)

open Expr

/-
### Concrete Syntax
-/

-- concrete syntax for literal true and literal false
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
