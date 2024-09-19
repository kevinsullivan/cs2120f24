import Cs2120f24.Lectures.«02_prop_logic».formal.properties
import Cs2120f24.Lectures.«02_prop_logic».formal.interpretation
import Cs2120f24.Lectures.«02_prop_logic».formal.semantics
import Cs2120f24.Lectures.«02_prop_logic».formal.truth_table
import Cs2120f24.Lectures.«02_prop_logic».formal.utilities


/-!
- Accept certain "rules of inference/reasoning" as valid
- For PL: accept the *semantically valid* facts from HW1

Goal is to show proposition true under given assumptions

- set-up problem as a sequent: *assumptions ⊢ goal*
- apply rules to transform sequent until no goals remain
-/

/-!
AXIOMS

-- And
and_intro :=          S ⇒ R ⇒ S ∧ R
and_elim_left :=      S ∧ R ⇒ S
and_elim_right :=     S ∧ R ⇒ R

-- Or
or_intro_left :=      S ⇒ S ∨ R
or_intro_right :=     R ⇒ S ∨ R
or_elim :=            R ∨ S ⇒ (R ⇒ W) ⇒ (S ⇒ W) ⇒ W

-- Negation
not_intro :=          (S ⇒ ⊥) ⇒ ¬S
not_elim :=           ¬¬S ⇒ S

-- Implies
imp_intro :=          S ⇒ W ⇒ (S ⇒ W)
imp_elim :=           (S ⇒ W) ⇒ S ⇒ W

-- Equivalence
equiv_intro :=        (S ⇒ W) ⇒ (W ⇒ S) ⇒ (S ↔ W)
equiv_elim_left :=    (S ↔ W) ⇒ (S ⇒ W)
equiv_elim_right :=   (S ↔ W) ⇒ (W ⇒ S)
-/


/-!
Example #1: and_intro

Suppose R and S are true; show R ∧ S is then true.

First, set up problem as sequent:

R, S ⊢ R ∧ S

Now use the axioms or any other validated propositions to derive
the truth of the goal proposition.

We know what we need. What do we have to work with? The assumptions!

- "apply" the and_intro "inference rule" to R and S to derive the truth of R ∧ S
- R ∧ S can now be removed as a goal and added to the context leaving nothing left to prove

R, S, R ∧ S ⊢ {}

-/

/-!
Example #2: and_intro

Problem: Show that P ∧ Q is valid.

There are no assumptions in this problem, just the goal.
This is the typical starting point for proving any kind
of proposition. We know that this goal proposition is not
valid *semantically*. Let's see where we get stuck trying
to prove it by natural deduction.

⊢ P ∧ Q

The only way we ultimately have to derive the truth of P ∧ Q
is to apply and_intro to the truth of P and the truth of Q.
The problem is that we haven't either assumed or shown that
either P or Q is true.

The best we can do is to *apply and_intro to arguments that we
don't yet have *but promise to deliver in the future*. We write
that like this: and_intro _ _. If we *had* the arguments that
we need (truth of P, and truth of Q) we'd be done, as and_intro
applied to them would derive the truth of P ∧ Q, which is what
we want. But we don't have these argument values and so we are
left is with two new goals: derive the truth of P, and derive
the truth of Q.

⊢ P
⊢ Q

Sadly we have no additional information to derive the truth of
either of them, We're stuck and can't complete the derivation.
-/

/-!
Example 3: But there's something really interesting going on
there. Applying a rule to the *missing arguments* left us with
two new sub-goals.

Let's return to the first problem and see how this works out.

Show R, S ⊢ R ∧ S.

First apply "and_intro _ _" to construct a proof of R ∧ S but
with the two sub-goals left to prove: R, and S, respectively.
Here are the resulting sequents.

R, S ⊢ R
R, S ⊢ S

Second, in each of these cases, the goal that's left to prove
is already *assumed* to be true, these two goals, and there is
nothing left to prove.

R, S ⊢ {}
R, S ⊢ {}

Example #1 is an example of a "bottom-up" proof, where we apply
rules to already known facts to derive new ones. This example is
a "top-down" proof, where we provided a *compelete* proof but for
certain remaining "holes," which become new "smaller" sub-goals.
Once we "prove/construct" each of the arguments, the application
of the top-level rule, and_intro, can complete, finishing off the
proof.
-/

/-!
Example #4: and_elim

Suppose R ∧ S is true. Show that R is true.

Sequent: R ∧ S ⊢ R

apply *and_elim_left* to R ∧ S to derive R, add it to the context
and remove it from the context

R ∧ S, R ⊢ R

Now R is accepted as true and can be removed as a goal. We can say
it's already an assumption, so the proof is complete.

R ∧ S, R ⊢ ⊤    -- QED
-/


/-!
affirm_disjunct :=    (W ∨ S) ⇒ W ⇒ ¬S
affirm_consequent :=  (S ⇒ W) ⇒ W ⇒ S
deny_antecedent :=    (S ⇒ W) ⇒ ¬S ⇒ ¬W
-/
