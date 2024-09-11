import Cs2120f24.Lectures.«02_prop_logic».formal.syntax
import Cs2120f24.Lectures.«02_prop_logic».formal.domain

namespace cs2120f24

/-!
### Semantics

The idea of semantics in Propositional Logic is simple:
every expression has, as its meaning, a Boolean value.
For literal expressions, easy. For variable expresssions,
you need a interpretation function, then you extract the
variable from the variable expressions, then you apply
the interpretation function to the variable to get the
Boolean value "assigned to it by that interpretation."
Finally, you evaluate big expressions by evaluating the
subexpressions, getting Bools, which you then combing
using the Boolean function specified by the *syntactic*
operator (logical connective): and, or, not, or whatever.
That's it!
-/

/-!
#### Interpretation of Unary Connectives

The first thing we'll do is define what Boolean operators
we mean by the names of our unary and binary "conenctives".
-/

-- function takes unary operator and returns *unary* Boolean function
-- (Bool -> Bool) means takes *one* Bool argument and "returns" a Bool

def evalUnOp : UnOp → (Bool → Bool)
| (UnOp.not) => not


/-!
#### Interpretation of Binary Connectives

- takes a binary operator and returns corresponding *binary* Boolean function
- (Bool → Bool → Bool means takes two Bools and finally returns one at the end)
-/

def evalBinOp : BinOp → (Bool → Bool → Bool)
| BinOp.and => and
| BinOp.or => or
| BinOp.imp => imp
| BinOp.iff => iff

/-!
We've now understood that an "interpretation" can be understood
to be and can at least here actually be *used* as a function that
takes a variable (var) as an argument and that returns the Boolean
value that that interpretation assigns to it.

To understand the next line, understand that (var → Bool) in Lean
is the type of any function that takes a var argument and returns a
Bool value. Here we just give this *type* a name to make subsequent
code just a easier for people to read and understand.
-/

abbrev BoolInterp := BoolVar → Bool

open PLExpr

/-!
#### Operational Semantics of Propositional Logic

NB: This is the material you most need and want to grok.

Finally now here is the central definition: the semantics of
propositional logic, specified in terms of our representations
of interpretations, variables, etc.

The first line defines evalBoolExpr to be some function taking
an expression, e, and an interpretation, i, as arguments and
returning the Boolean meaining of e in the "world" (binding
of all variables to Boolean values) expressed by that i.
-/

def evalPLExpr : PLExpr → BoolInterp → Bool
| lit_expr b,             _ => b
| (var_expr v),           i => i v
| (un_op_expr op e),      i => (evalUnOp op) (evalPLExpr e i)
| (bin_op_expr op e1 e2), i => (evalBinOp op) (evalPLExpr e1 i) (evalPLExpr e2 i)

/-!
That's it. From this material you should be able to aquire
a justifiably confident grasp of essentially every aspect
of the syntax and semantics of propositional logic.
-/
end cs2120f24
