import «Cs2120f24».Lectures.«02_prop_logic».formal.models_counterexamples

namespace cs2120f24

/-! HOMEWORK #2: Models and Counterexamples

An interpretation, i, of an expression, e, is said to be a *model* of
e if e evaluates to true under i: that is, *evalPLExor e i = true*. On
the other hand, if e is false for i, then is i is  a *counterexample*
for e.

It is incredibly useful to be able to find models and counterexamples
of propositions/expressions in propositional logic. It is already clear
to everyone here that a given expression could be true under zero, some,
or all of its possible interpretations.

We already have functions that decide whether given expressions are valid,
satisfiable, or unsatisfiable; and we know those work by iterating over all
2^n possible interpretations for an expression with n distinct variables,
evaluating the expression for each, and then combining the answers in the
right way: reducing the results using ∧ to see if *all* results are true
(validity checking); using ∨ to see if *any* are true (sat checking); and
∨ checking to see if they're all false (unsat checking).

Insight: Instead of collecting Bool values, computed by (evalPLExpr e i)
we could just collect the interpretations thenselves that make e true. An
interpretation in the resulting list would be a model, while one in a list
for ¬e, would be a model of ¬e and thus a counterexample for e (a list of
variable/value bindings under which e is false, which is what we want in a
counterexample).

It shouldn't be hard to adapt what we already have to produce model and
counterexample finders. To make things even easier, all we really need
to provide is one function that takes an expression argument and returns
a list of all its models. We can then implement model and counterexample
finders using that function as a tool.

And so, yes, that's what we've done for you. You can find the names and
types (as well as the implementation definitions) of these functions in
the file, models_counterexamples.lean.

In engineering practice, model and counterexample finders for large and
complex propositional logic expressions are incredibly important. Now you
know what they do, even if it'd take another course to see how they do it
*efficiently* for kinds of problems that often arise in practice.

To be sure you're good using the tools we've provided please copy this
file to MyWork, the complete the homework following the instructions
below.
-/


-- Here we declare names for two propositional variable *expressions*
def isRaining := {⟨0⟩}
def isSprinkling := {⟨1⟩}

-- Now we give standard names to three logical fallacies we've already seen
def affirm_disjunct := (isRaining ∨ isSprinkling) ⇒ isRaining ⇒ ¬isSprinkling
def deny_antecedent := (isSprinkling ⇒ isRaining) ⇒ ¬isSprinkling ⇒ ¬isRaining -- correction here 9/15/24
def affirm_consequent := (isSprinkling ⇒ isRaining) ⇒ isRaining ⇒ isSprinkling


/- #1: [25 points]. Using our counterexample finder

Replace _ with the expression to get the list of counterexamples to affirm_disjunct
-/
def cxs : List BoolInterp := sorry

-- This "code" should display the resulting interpretations lists of 0/1 strings
-- It'll work when you fill in an answer above.
#eval! interpStringsFromInterps cxs 2


/- #2: [25 points]. Translating counterexamples back into English.

For each counterexample found, first translate it into English. Replace
the Boolean values indexed by position in the counterexample print-outs
with  meaningful natural language variables names and truth values, and
briefly explain why the proposition is false under that interpretation.

Example: variables are happy, blue; expression is happy ∧ blue; counterexample
is ["0","1"]; and explanation: conjunction requires that both conjuncts (happy,
and blue) be true for the expression to be true, but here is an interpretation
in which that's just not the case: not happy and blue.
-/

/-
You answers here:

-/

/- #3 [50 points].

Do the same thing with each of the other two fallacies.

- get and display (via #eval! the a list of counterexamples
- explain each counterexample in English
- explain briefly why the result of evaluation under this interpretation is false
-/

/-
Your answers here:

-/

/- #4 [unmarked].

Finish your assigned reading. Don't just skim. Try hard to learn it.
Relate it back to details of our specification of propositional logic. Go through, read,
play with, and understand the material on syntax, variable and operator interpretations,
truth_tables, properties of expressions, and models and counterexamples. Main.lean has
examples of using most of the important functions in our specification of propositional
logic. The code in the interpretations.lean file is most complex. I don't expect you to
understand the implementations, but but you can still understand *what* the functions do
based on comments. We're coming to the close of the unit on propositional logic. Take time
now to nail down your understanding of propositional logic in all of the dimensions we've
covered.
-/

namespace cs2120f24
