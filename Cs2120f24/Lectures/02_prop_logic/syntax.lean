namespace cs2120f24

/-!
# Propositional Logic: Syntax

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

/-!
### Literal Expressions

We need literal expressions meaning Boolean true and
Boolean false, respectively. We'll write these literal
expressions as (lit true) and llit false). For concrete
syntax we'll use ⊤ for (lit true) and ⊥ for (lit false).
-/

/-!
### Variable Expressions

Next we tackle *variable* expressions. For this we will
separately define variables and variable expressions. A
variable expression will be constructed from the variable
it represents as an expression in propositional logic.

#### Variables

We define *var* to be the type of *variables* as we've
been using the term: they are not themselves expressions
but are necessary values for making variable expressions.

The structure keyword indicates we're defining a data
type with just one constructor, here called *mk*. In this
case, it takes on argument, a natural number. The result
of applying var.mk to the number 3 is the term (var.mk 3).
This is the actual term in Lean that we've now defined to
represent what in concrete syntax we might write as v₃,
the variable with (natural number) index 3 into the set
of all of "countably" many distinct *variables* that we
can now use in building propositional logic expressions.
-/

-- abstract syntax for variables (var)
structure var : Type :=
  mk :: (n: Nat)

-- concrete syntax: "var_[n]" for "(var.mk n)"
notation "var_[" n "]" => var.mk n


/-!
#### Variable Expressions

Now we just defined variables expressions as expressions
of the form (var_expr v). We define var_expr shortly. Just
see it as the method for constructing a variable expression
from a variable. ANd given a variable expression, you can
get the underlying variable back out to work with. We'll
need that when it comes to defining interpretations as
functions that take *variables* in and that return values
from the semantic domain, here just of Boolean values.
-/

/-!
### Operator Expressions

Next we define the *expression-composing operator* (also
called *connectives*) of propositional logic. Each such
operator takes at least one expression as an argument and
uses it in constructing a larger expression.

- applying the *not* operator to an expression e yields the expression (not e)
- applying a *binary* operator, op, to e1 and e2, yields the expression (op e1 e2)
- here, op can be and, or, not, implies, iff, and so forth
-/

/-
We call the only unary operator *not*.
-/

inductive un_op : Type | not


/-
We also give usual names to four binary operators
-/
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

### Definition: The Abstract Syntax of Propositional Logic
-/

inductive Expr : Type
| lit_expr (fromBool : Bool) : Expr
| var_expr (from_var : var)
| un_op_expr(op : un_op) (e : Expr)
| bin_op_expr (op : bin_op) (e1 e2 : Expr)

/-!
It will be a good practice to infer from this
definition a range of expressions, which is to
say, values that can be constructed using these
constructors and any values for their arguments.

PRACTICE:
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
open Expr

/-
## Concrete Syntax

A well designed, user tested, concrete syntax for a
given formal language can be a huge aid to the human
of abstract formal definitions in that language. We
prefer to write (3 + 4) over (add 3 4), for example.

We don't expect you to have justifiable confidence
in your deep understanding of this notation stuff at
this point! We encourge you to follow it carefully
to get the gist.
-/

-- concrete syntax for (lit true) and (lit false) expressions
notation " ⊤ " => lit_expr true
notation " ⊥ " => lit_expr false

-- our non-standard notation for a variable expression from a variable
notation "{" v "}" => var_expr v

-- our single unary connective, *not* (¬)
-- we set it to have maximum precedence (binding strength)
prefix:max "¬" => un_op_expr un_op.not

-- and here are concrete notations for our binary connectives
-- the letter "l" after infix specifies left associativity
-- rhw numbers after the colons specify relative binding strengths
-- in parens are the concrete notations
-- the de-sugared versions follow after the =>s
infixr:35 " ∧ " => bin_op_expr bin_op.and
infixr:30 " ∨ " => bin_op_expr bin_op.or
infixr:25 " ⇒ " =>  bin_op_expr bin_op.imp
infixr:20 " ⇔ " => bin_op_expr bin_op.iff

/-
Now head off to the Main.lean file in this same directory,
copy it into your MyWork directory tree, and plan around with
building expressions in our logic.
-/

end cs2120f24
