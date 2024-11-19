-- Suppse P, Q, and R are arbitrary propositions
axiom P : Prop
axiom Q : Prop
axiom R : Prop

/-!
Here we address case analysis. As a running example
we'll take P ∨ Q → R as an example. Unless R is already
known to be true, and proof of this will require a case
analysis, and to show that R is true in either case.
-/


/-!
We've used the following definition by cases syntax a lot
-/
example : P ∨ Q → R
-- eliminate P ∨ Q and show that R follows is each case
| (Or.inl p) => (sorry)   -- from p : P construct proof of R
| (Or.inr q) => (sorry)   -- from q : Q construct proof of R

/-!
In the last class we saw more clearly that that's really
just nice concrete notation, provided by Lean (libraries)
for the application of the elimination rule for Or.
-/
example : P ∨ Q → R :=
fun (h : P ∨ Q) =>
  (Or.elim
    h
    (sorry)
    (sorry)
  )

/-!
Finally, some of you have remembered the match construct
in Lean. It let's you use "pattern matching" syntax within
the definition of a function.
-/
example : P ∨ Q → R :=
fun (h : P ∨ Q) =>
  (match h with
    | (Or.inl p) => (sorry)
    | (Or.inr q) => (sorry)
  )

/-!
These are three expressions for exactly the same proof
term in Lean. The most fundamental of them is the second:
a direct application of the Or.elim axiom. The other two
are often nicer ways to write it. You may use whichever
concrete syntax you want for now. We generally don't apply
Or.elim directly but prefer to use match or the "by cases"
syntax in the first example.

We've left all three proof terms with remaining typed holes
to be some (pr : P → R) and some (qr : Q → R), as we mean to
focus on the case analysis on the assumed proof of P ∨ Q and
then what else is needed to complete the proofs.
-/
