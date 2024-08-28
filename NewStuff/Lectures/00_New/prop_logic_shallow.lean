open Classical

axiom em (P : Prop) : P ∨ ¬P

#check choice

/-
The Lean libraries don't actually define
em as an axiom but as a theorem (a proof of
the proposition). This proof, in turn, uses
some other inference "rules" that Lean does
define as axioms. The names of these inference
rules are choice, functional extensionality,
and propositional extensionality.

Choice (here) asserts that if you're given any
non-empty type (set) of objects, then you can
always choose, and thus get some specific object
in that set. That means if you have in infinite
sequence of sets, you can in a sense iterate
over them, choosing one specific element from
each set, and using those elements construct a
new set. If you don't assume the axiom of choice
in mathematics, you cannot use this principle
to construct proofs of propositions.

The underlying idea is that
to choose an element, you have to have a specific
way to choose an element.


Suppose A and B are "functions". An extensional
definition of equality leads one to judge A = B
based on their observable behavior. So A = B if,
for any argument, A and B return the same result.
An intensional definition of equality focuses on
the defintions of the functions. For example you
would generally not say that a Python program is
equal to a C++ program even if they compute the
very same set of input-output pairs.

/-
The Lean libraries
-/


-/




-- From now on

variable (P Q R : Prop)

-- constructive proof

theorem imp_equiv1: (¬P ∨ Q) → (P → Q) := by
  intro h
  intro p
  cases h with
  | inl np => contradiction
  | inr q => assumption


theorem imp_equiv2 (P Q : Prop): (¬P ∨ Q) → (P → Q) := by

  -- implies (arrow) introduction
  intro nporq

  -- Proof is by case analysis on P.
  cases Classical.em P with

  -- Case where P is true
  | inl p =>

    -- Proof where P is true is by case analysis on Q
    cases Classical.em Q with

    -- Case where Q is true
    | inl q =>
      intro _
      assumption

    -- case where Q is false
    | inr nq =>

      -- Proof by by case analysis on nporq
      cases nporq with

      -- Case where it's true because ¬P is true
      | inl np => contradiction   -- proof by false elimination

      -- Case where it's true because Q is true
      | inr q => contradiction    -- proof by false elimination


  -- Case where P is false
  | inr np =>

    -- Proof is by case analysis on Q
    cases Classical.em Q with

    -- Case where Q is true
    | inl q =>
      cases nporq with
      | inl np => intro _; assumption   -- proof by assumption
      | inr q => intro _; assumption    -- proof by assumption

    -- case where Q is false
    | inr nq => intro p; contradiction  -- proof by false elimination


/-
Probably best to do this with
-/

theorem neg_elim : ¬¬P → P :=
by
  cases (Classical.em P)
  intro nnp; assumption
  intro nnp; contradiction
