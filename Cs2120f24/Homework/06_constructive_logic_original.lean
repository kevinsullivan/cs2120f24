namespace cs2120f24.constructiveLogic

/-! HOMEWORK #5. COUNTS FOR TWO ASSIGNMENTS.

This is an important homework. It gives you an
opportunity to work out many of the kinks in your
understanding of predicate logic and deductive
proofs in type theory. With P, Q, and R accepted
as propositions, you are to give proofs of all of
the identities from Library/propLogic/identities,
which I've rewritten in Lean for you. There's one
of these axioms that has no constructive proof (in
just one direction). You can just identify it.
-/


-- Suppse P, Q, and R are arbitrary propositions
axiom P : Prop
axiom Q : Prop
axiom R : Prop

/-!
Give proofs in Lean that each of the following identities
is valid. We already know they're classically valid as we
validated their propositional logic analogics semantically
using our model / validity checker. To get you started with
a concrete example, we prove the first one for you and give
a little English explanation after. You should od the same
for each proposition you prove.
-/


def andIdempotent   : P ↔ (P ∧ P) :=
Iff.intro
  -- forward direction: P → P ∧ P
  -- assume p : P, show P ∧ P
  (fun (p : P) => And.intro p p)
  -- backwards direction: P ∧ P → P
  (fun (pimpp : P ∧ P) => pimpp.left)

/-!
In English. We are to show that any proposition
P is equivalent to P ∧ P. By the Iff.intro axiom,
it will suffice to first prove P → P ∧ P and then
to prove P ∧ P → P. With that we'll be done.

Proof of forward direction: P → P ∧ P. Assume we
have a proof (p : P). Then applying the axiom
of And introduction to p and p, we can derive the
proof of P ∧ P that will show that if P is true,
then P ∧ P is true. So P → P ∧ P.

Proof of backward direction. P ∧ P → P. Assume
we have a proof, pandp : P ∧ P. By either one of
the two elimination axioms we can derive a proof
of p: as either pandp.left or pandp.right.
-/

def orIdempotent    : P ↔ (P ∨ P) :=
_

def andCommutative  : (P ∧ Q) ↔ (Q ∧ P) :=
_

def orCommutative   : (P ∨ Q) ↔ (Q ∨ P) :=
_

def identityAnd     : (P ∧ True) ↔ P :=
_

def identityOr      : (P ∨ False) ↔ P :=
_

def annhilateAnd    : (P ∧ False) ↔ False  :=
_

def annhilateOr     : (P ∨ True) ↔ True :=
_

def orAssociative   : ((P ∨ Q) ∨ R) ↔ (P ∨ (Q ∨ R)) :=
_

def andAssociative  : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) :=
_

def distribAndOr    : (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) :=
_

def distribOrAnd    : (P ∨ (Q ∧ R)) ↔ ((P ∨ Q) ∧ (P ∨ R)) :=
_

def equivalence     : (P ↔ Q) ↔ ((P → Q) ∧ (Q → P)) :=
_

def implication     : (P → Q) ↔ (¬P ∨ Q) :=
_

def exportation     : ((P ∧ Q) → R) ↔ (P → Q → R) :=
_

def absurdity       : (P → Q) ∧ (P → ¬Q) → ¬P :=
λ h =>
  (
    λ a => _
  )

def distribNotAnd   : ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) :=
_

def distribNotOr    : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) :=
_



/-!

-/


/-!
EXTRA CREDIT: apply the axiom of the excluded middle
to give a classical proof of the one proposition that
you identified as having no constructive proof. The
axiom is available as Classical.em (p : Prop) : p ∨ ¬p.
-/

#check Classical.em
-- Classical.em (p : Prop) : p ∨ ¬p
-- Given any proposition p, you can have a proof of p ∨ ¬p
-- You then have two cases: one with a proof of p, one with ¬p
example (A : Prop) : A ∨ ¬A := Classical.em A
