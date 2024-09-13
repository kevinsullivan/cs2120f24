import «Cs2120f24».Lectures.«02_prop_logic».formal.properties
import «Cs2120f24».Lectures.«02_prop_logic».formal.interpretation
import «Cs2120f24».Lectures.«02_prop_logic».formal.models_counterexamples
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
/-
def P : PLExpr := PLExpr.var_expr v₀
def Q : PLExpr := { v₁ }  -- our notation for var_expr constructor
def R : PLExpr := { v₂ }
-/

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


/-!
INTERPRETATIONS
-/

/-
Here's how we can see a list of interpretations
for a given expressions.
-/
#reduce interpStringsFromInterps
          (listInterpsFromExpr (P ∧ Q ∨ R))
          3 -- number of variables here


/-!
It's often helpful to list arguments
to functions properly indented across
multiple lines.
-/



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
Properties of Propositions (Expressions)!
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
Models and counterexamples.

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
        2                    -- width to print each interpretation

end cs2120f24
