import «Cs2120f24».Lectures.«02_prop_logic».formal.properties
import «Cs2120f24».Lectures.«02_prop_logic».formal.interpretation
import «Cs2120f24».Lectures.«02_prop_logic».formal.models_counterexamples
import Cs2120f24.Lectures.«02_prop_logic».formal.semantics
import Cs2120f24.Lectures.«02_prop_logic».formal.syntax
namespace cs2120f24

open PLExpr


/-!
SYNTAX

Suppose I want to write some propositional logic expressions
using the variable expressions, P, Q, and R, and building up
larger propositions using the propositional logic expression-
constructing operators. Here's how you do it.
-/

-- First define a disting variable for each variable expression
def v₀ : BoolVar := BoolVar.mk 0    -- abstract syntax
def v₁ : BoolVar := ⟨1⟩             -- Lean notation for mk
def v₂ : BoolVar := ⟨2⟩

/-!
Now you define the variable expressions you want to use. The
first line is using abstract syntax. The next two use our own
(non-standard) notation, desugaring to exactly that abstract
syntax.

These variables are already declared at this point. This is a
small design glitch that could be cleaned up. We comment them
out for now so as not to introduce conflicting definitions.
-/

def P : PLExpr := PLExpr.var_expr v₀
def Q : PLExpr := { v₁ }  -- our notation for var_expr constructor
def R : PLExpr := { v₂ }

/-
Now that you have three variable expressions to work with,
you can use logical expression "connectives" (operators) to
build bigger expressions. Consider the expression, P ∧ Q,
for example. First we'll write it using abstract syntax,
then using concrete syntax.
-/

/-!
Here we show the equivalence of abstract and concrete syntax.
-/
def P_and_Q_abstract : PLExpr :=
  (PLExpr.bin_op_expr BinOp.and P Q)

/-!
Standard concrete infix notation for (PLExpr.bin_op_expr BinOp.and
That is the actual desugarad representation of ∧. Other propositional
logic concrete notations (and the concepts they represent) reduce to
these abstract sybtax repreesentations.
-/
def P_and_Q_concrete := P ∧ Q
#reduce P_and_Q_concrete
/-!
(bin_op_expr BinOp.and) -- this is ∧
  (var_expr { index := 0 }) -- the first conjunct, P
  (var_expr { index := 1 }) -- the second conjunct, Q
-/


/-! SEMANTICS UNDER INTERPRETATIONS

We can easily enumerate all possible interpretations.
That's jsut the "input" side of a truth table. Notice
that this part doesn't depend on the details of e (an
expression) at all. The driving factor is the number
number of *variables* (columns). The number of rows is
then 2^#columns. But there's more. What relationship
do you see between the row indices and the row contents?
-/

/-!
            var
           0   1
  index  | P | Q | e
    0    | 0 | 0 | _
    1    | 0 | 1 | _
    2    | 1 | 0 | _
    3    | 1 | 1 | _
-/

/-!
Recall that we represent each interpretation (each row)
as a function. That function takes a variable (it's index)
as an actual parameter, and returns the Boolean value for
that variable *in that row* ("under that interpretation").

But of course the value for that variable in that row is
just the (0 for false / 1 for true) Boolean value in the
*binary expansion* of the row index. Is everyone okay with
base 2 arithmetic? So all of this can easily programmed.

Here we compute the interpretation in row index 2 in the
preceding example. Note that e's not involved except to
the extent that it determines the number of variables in
one.
-/

def i := InterpFromRowCols 2 2
#check i

/-!
Applying i to a *variable*, with indices 0 or 1, should
return the values in row 2, namely 1 and 0. Does it work?
(Remember ⟨⟩ notation for applying structure constructor,
so here ⟨0⟩ is (BoolVar.mk 0), a "variable" in our lexicon.)
-/

#eval! i ⟨0⟩    -- expect true
#eval! i ⟨1⟩    -- expect false

/-!
 It's exactly this trick that is used in the semantic
evaluation function that defines for us an operational
semantics for propositional logic. That means that we
have a *function* for computing an expression's meaning
given an interpretation, i, giving the semantic values
of the variables in the expression.
-/

def e := P_and_Q_concrete

#eval! evalPLExpr e i

/-!
Given the semantic meanings (Boolean functions) that
we've given our syntactic operators, we see that the
proposition/expression e evaluates to true under the
interpretation, i. We will thus say that i is a model
of e. It represents a world in which e is true.
-/

/-!
Convenience functions for working with our representations of interpretations

An interpretation, i, is a function. It's generally not
helpful to print functions in Lean. If you want to see a
string representation of an interpretation, we do have a
function for that. You pass it the interpretation and how
many columns you want to see. An interpretation function
is technicallky defined as false for all column indices
beyond those of interest in a given case.
-/

#eval! bitStringsFromInterp i 2

/-!
We also provide a function for converting a list of Bool
values into an interpretation.
-/

def i2 := interpFromBools [true, false, true]
#eval! bitStringsFromInterp i2 3

/-!
And finally a way to get a printable list of multiple
(typically all) interpretations.
-/

/-!
All interpretations

Up to now we've been working with one interpretation, i.
We can also easily obtain, and provide a function, for
getting a list of *all* interpretations for an expression
with "n" variables, for any number, n. This function first
counts the number of variables in e and then constructs a
list of interpretatins, one for each index from 2^n-1 to 0.
-/

def all_interps_e := listInterpsFromExpr e



/-!
TRUTH TABLES

You already know you can get the results of evaluating an
expression e for each interpretation in a given list of them.
-/

#eval! truthTableOutputs e

/-
We see that e (go back and see how we defined it) is actually
valid. And now of course you can see how we check validity for
any expression. We count the variables in it, we generate 2^n

-/

#eval! truthTableOutputs ¬e


/-!
PROPERTIES OF EXPRESSIONS

As you know, validity just means that a proposition is true
under every interpretation -- in all worlds -- making it into
a general-purpose reasoning principle. The is_valid function
takes an expression, computes its number of variable, gets a
list of all interpretations
-/

#eval! is_valid e
#eval! is_sat e
#eval! is_unsat ¬e


/-!
TRUTH TABLES (output vectors). The returned
list is the semantic meaning of the single
given expression under each ]interpretation,
starting with all true and descending to all
false. (We have a note to clean this up.)
-/

#eval! (truthTableOutputs (P))
#eval! (truthTableOutputs (P ∨ Q))


/-!
Examples: Checking satisfiability-related properties of a few expressions
-/

#reduce is_sat ⊤
#reduce is_sat ⊥

#reduce is_sat P
#reduce is_unsat P
#reduce is_valid P

#reduce is_sat ¬P
#reduce is_unsat ¬P
#reduce is_valid ¬P

#reduce is_sat (P ∨ ¬P)
#reduce is_unsat (P ∨ ¬P)
#reduce is_valid (P ∨ ¬P)

#reduce is_sat (P ∧ ¬P)
#reduce is_unsat (P ∧ ¬P)
#reduce is_valid (P ∧ ¬P)

#reduce is_sat (P ∧ Q)
#reduce is_unsat (P ∧ Q)
#reduce is_valid (P ∧ Q)

#reduce is_sat (P ∨ Q)
#reduce is_unsat (P ∨ Q)
#reduce is_valid (P ∨ Q)



/-
MODELS AND COUNTEREXAMPLES

Please read about models and counterexamples in models.lean.
Then come here and predict the answers for each of the following
problems before seeing what our model finder says. Notice that in
each case we're asking to find all models, or counterexamples, for
a given expression.

Details: The numeric argument determines should reflect how many
variables there are in the expression being analyzed. The number
is used to determine how many variables each interpretation should
be output as strings in the resulting lists of lists of strings.

To decode the outputs remember that P refers to variable 0, Q
to variable 1, R to variable 2. So in a list of strings for one
interpretation, you'd want to print its values for these three
variables. The ouput would be something like this [["0","1","1"]]
meaning that P is assigned 0; Q, 1; R, 1, by that interpretation.
-/

-- the numeric argument determines how many variables in expr
#eval! interpStringsFromInterps
        (findModels P)
        1

#eval! interpStringsFromInterps
        (findModels ¬P)
        1
#eval! interpStringsFromInterps
        (findModels (P ∨ Q))
        2

#eval! interpStringsFromInterps
        (findModels (P ∧ Q))
        2

#eval! interpStringsFromInterps
        (findModels (P ↔ Q))
        2


#eval! interpStringsFromInterps
        (findCounterexamples P)
        1

#eval! interpStringsFromInterps
        (findCounterexamples ¬P)
        1

#eval! interpStringsFromInterps
        (findCounterexamples (P ∨ Q))
        2

#eval! interpStringsFromInterps
        (findCounterexamples (P ∧ Q))
        2

#eval! interpStringsFromInterps
        (findCounterexamples (P ↔ Q))
        2

#eval! interpStringsFromInterps
        (findCounterexamples      -- a list of interpretations for ...
          ((P ⇒ Q) ⇒ (¬P ⇒ ¬Q)))  -- this proposition (parens needed)
        2                         -- number of variables in result strings

end cs2120f24
