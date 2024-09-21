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

The idea is that eventually an interpretation function
will take a BoolVar object as arguments and return the
Boolean values that that interpretation assigns to it.
-/
structure BoolVar : Type :=
  mk :: (index: Nat)
deriving Repr


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
##### Concrete syntax for variables (var)

We could define our own concrete notation for variables,
but Lean provides one automatically for any "structure"
type. A structure type has exactly one constructor. You
can give it a name, but Lean defines *mk* as the default.
This constructor will take zero or more argument. So, to
build a value of such a type you can use ⟨ a, b, c,... ⟩
notation as a shorthand for, say, "var.mk a b c ....".
We do need to let Lean know the result show be a "var".
-/
#check (⟨3⟩ : BoolVar)    -- it's a variable (var)
-- #check ⟨3⟩             -- not unique constructor expr
-- But where Lean can infer BoolVar type ⟨3⟩ will suffice


/-!
Now we just defined variables expressions as expressions
of the form (var_expr v). We define var_expr shortly. View
var_expr as the method for constructing a variable expression
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

We call the only unary operator *not*, and the usual binary operators
by their usual names. Remeber, these are meaningless symbols in the formal
*syntax* of propositional logic. We give them names that will reflect their
usual meanings when we define *semantics* for syntact expressions.
-/

-- unary connective (syntactic expression composers)
inductive UnOp : Type
| not
deriving Repr

-- binary connectives (syntactic expression composers)
inductive BinOp : Type
| and
| or
| imp
| iff
deriving Repr

/-!
Now we get to the heart of the matter. With those preliminary
dependencies out of the way, we now formally specify the complete
(abstract) syntax of propositional logic. We do this by defining
yet another data type. The idea is that values of this type will
be (really will represent) expressions in propositional logic. In
fact, in Lean, this type specifies the set of *all* and *only*
the expressions legal in propositional logic.

### Formal Syntax of Propositional Logic
-/

inductive PLExpr : Type
| lit_expr (from_bool : Bool) : PLExpr
| var_expr (from_var : BoolVar)
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
