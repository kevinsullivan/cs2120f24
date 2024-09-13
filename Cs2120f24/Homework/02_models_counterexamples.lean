import «Cs2120f24».Lectures.«02_prop_logic».formal.properties

/-!
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
-/
