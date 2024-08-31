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
as results.

- literal expressions
- variable expressions
- operator (application) expressions

Remember: we're not talking about Boolean meanings of
literals, variables, or bigger expressions here. The
syntax of a languages defines the set of syntactically
constructible expressions in our language, and that's
all.

Now what's interesting is that we formalized the set of
all correct expressions as Expr. It's a type. And now
any particular logical expression is just a data value of
this Expr type. The available constructors describe all
all and only the ways to construct a term of this type,
that we take to encode a propositional logic expression,
that Lean checks automatically for syntactic correctness.

Let's dive down into literal, variable, and application
(operator application, if you want) expressions and how
we represent them in Lean.
-/

/-!
### Literal Expressions

Our implementation of propositional logic defines two
literal values, each built (a) by a constructor called
lit, (b) from one of the two Boolean values, provided
as an argument (true or false). Our syntactic language
now includes two expressions: (lit true) and (lit false).
In concrete syntax ⊤ is (lit true) and ⊥ is (lit false).
-/

/-!
### Variable Expressions

Variable expressions are a little more complicated, but
not much. Just as a lit expression is built from a Boolean
value (and incorporated as a value into the resulting term),
a variable expression is built from a variable (a value of
a type we'll call var). Each var object in turn is built
from a natural number (0, 1, 2, ...). The natural number
in one var distinguishes that var from any var having a
different natural number "index." This design provides us
as future authors of masterpieces in propositional logic
an infinite supply of distinct variables to use in writing
our logical opus magni. So, again, lets dig down a little
more.

#### Variables

We define *var* to be the type of *variables* as we've
been using the term: they are not themselves expressions
but are necessary values for making variable expressions.
-/

/-!
##### abstract syntax for variables (var)
-/
structure var : Type :=
  mk :: (index: Nat)

/-!
The structure keyword indicates we're defining a data
type with just one constructor, here called *mk*. In this
case, it takes one argument, a natural number. The result
of applying var.mk to the number 3 is the term (var.mk 3),
which we will take to mean "the particular variable from
our set of infinitely many, built from the Nat value 3".
Here's a shorthand notation we just made up. You can use
var_[3], for example, to mean (var.mk 3). It't not a lot
of help, but
-/

/-!
##### concrete syntax for variables (var)

We could define our own concrete notation for variables,
but Lean provides one automatically for any "structure"
type. A structure type has exactly one constructor. You
can give it a name, but Lean defines *mk* as the default.
This constructor will take zero or more argument. So, to
build a value of such a type you can use ⟨ a, b, c,... ⟩
notation as a shorthand for, say, "var.mk a b c ....".
We do need to let Lean know the result show be a "var".
-/
#check (⟨3⟩ : var)   -- it's a variable (var)


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

PRACTICE: Coming your way soon.
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
