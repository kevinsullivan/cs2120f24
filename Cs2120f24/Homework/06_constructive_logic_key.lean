namespace cs2120f24.constructiveLogic

/-! HOMEWORK #6. COUNTS FOR TWO ASSIGNMENTS.

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

-- #1
def andIdempotent   : P ↔ (P ∧ P) :=
Iff.intro
  -- forward direction: P → P ∧ P
  -- assume p : P, show P ∧ P
  (fun (p : P) => (And.intro p p))
  -- backwards direction: P ∧ P → P
  -- assume P ∧ P, show P
  (fun (h : And P P) => h.right)

/-!
In English: To prove P ↔ P ∧ P it will suffice to
apply the "iff intro" inference rule to proofs of
(P → (P ∧ P)) and ((P ∧ P) → P).

Forward direction:

To prove P → P ∧ P, we need to show that if P is
true, now based on the assumption that there is a
proof of it, (p : P)), that you can then construct
a proof of (P ∧ P). In constructive logic, a proof
is given by a *function* of *type* P → P ∧ P. It
will be a function that given *any* proof of P will
return a proof of P ∧ P. Given a proof, (p : P) it
is easy to return a proof of P ∧ P: And.intro p p.
Lean's notation for this term is ⟨ p, p ⟩.

Backward direction:

To prove P ∧ P → P, assume we're given that P ∧ P
is true; then we must show that P is true. In our
constructive logic we show that by showing there is
a function that takes a proof, (h : P ∧ P), as an
argument (assumption) and that yields a proof of P
as a result. From  proof, h, of P ∧ P, we derive a
proof of P through application of either of the the
"and" elimination" inference rules, h.left, h.right.

With these proofs, call them forward and backward,
we can then construct a proof of the *equivalence*
by applying the "iff introduction" inference rule
to them.
-/

-- #2
-- What we are to prove is that ∨ is idemponent
-- That is, that for any P, P ↔ (P ∨ P).
def orIdempotent    : P ↔ (P ∨ P) :=
-- Proof: by application if iff.intro
-- iff intro
(
  Iff.intro
  -- Proof of P → P ∨ P
  (fun (p : P) => Or.inl p)
  -- Required proof of backward implication
  (fun (h : P ∨ P) =>
    (Or.elim
      h
      (fun p => p)
      (fun p => p)
    )
  )
)

/-!
To prove the equivalence, P ↔ P ∨ P, we need to
prove the forward and backwards implication. To
prove P → P ∨ P, assume P is true (with a proof,
(p : P)), then show that P ∨ P must be true by
constructing a proof of it. The latter can be
done by applying either of the "or introduction"
inference rules. The proof above uses the "left"
introduction rule. The "right" would also work.
Either proof is equally as good at showing that
P ↔ (P ∨ P) is a *valid* equivalence. With the
two proofs (call them f and b) we now construct
a proof of P ↔ P ∨ P by apply the "iff intro"
inference rule to both proofs. In Lean that is
(Iff.intro f b). That is exactly what the formal
proof is: that term, (Iff.intro f b). If you're
not sure why, go look at the definition of Iff
in Lean.
-/

-- #3
def andCommutative  : (P ∧ Q) ↔ (Q ∧ P) :=
Iff.intro
-- forward
(fun h => ⟨ h.right, h.left ⟩)
-- backward
(fun h => ⟨ h.right, h.left⟩)

/-
To prove: (P ∧ Q) ↔ (Q ∧ P).
Proof: By applying the "iff intro" inference rule
to the forward and backward implications. It will
thus suffice to prove those proofs. Here they are.
QED.

Forward: Assume (h : P ∧ Q). A proof of (Q ∧ P)
can then be constructed by applying the "and intro"
inference rule to proofs of Q and P in that order,
which can be derived from h using the right and left
"and elimination" inference rules, as h.right and
h.left.

Backward. The proof is symmetrical with the first.
-/

-- #4
def orCommutative   : (P ∨ Q) ↔ (Q ∨ P) :=
Iff.intro
(fun (h : P ∨ Q) =>
  (
    match h with
    | Or.inl p => Or.inr p
    | Or.inr q => Or.inl q
  )
)
(
  fun (h : Q ∨ P) =>
  (
    match h with
    | Or.inl q => Or.inr q
    | Or.inr p => Or.inl p
  )
)

/-!
Prove (P ∨ Q) ↔ (Q ∨ P).
Proof: By applying the "iff introduction" inference
rule to proofs of the forward and backward implications,
(P ∨ Q) ↔ (Q ∨ P) and (Q ∨ P) ↔ (P ∨ Q). We give such
proofs next, completing our proof of (P ∨ Q) ↔ (Q ∨ P).
QED.

Forward: Assume (P ∨ Q). We have to show (Q ∨ P).
In particular, we need to show (Q ∨ P) whether
(P ∨ Q) is true because P is true or because Q is.
In other words, we need to proofs of P → Q ∨ P and
of Q → Q ∨ P. We must perform a *case analysis* on
the assumed proof of P ∨ Q.

Case 1L Assume P ∨ Q is true because P is true,
with (in constructive logic) a proof (p : P). We
can then construct a proof of Q ∨ P by applying
the right "or introduction" inference rule to p,
showing that P → Q ∨ P (see P is on the right in
the conclusion of the implication, so given p,
all we can do is use *right* introduction with p).
In the second case, where P ∨ Q is true because Q
is, with a proof (q : Q), we can construct a proof of
(Q ∨ P) by applying the left "or introduction" rule
to q. That shows that Q → Q ∨ P.

We now have all the elements needed to apply the
"or elimination rule" to deduce (by constructing
a proof of) P ∨ Q → Q ∨ P using the "or elimination"
inference rule to our proofs of (1) h : P ∨ Q, and
the proofs given by each case: (2) P → Q ∨ P, and
(3) Q → Q ∨ P.

We thus prove the forward implication, P ∨ Q → Q ∨ P,
in constructive logic by showing that we can define a
*function* of *type* P ∨ Q → Q ∨ P.

Bacward: The backward proof is symmetrical.
-/


-- #5
def identityAnd     : (P ∧ True) ↔ P :=
Iff.intro
  (fun h => h.left)
  (fun h => ⟨ h, True.intro ⟩)

/-!
Prove: (P ∧ True) ↔ P
Proof: By applying "iff introduction" to proofs of
the forward and backward implications, which we give
below. QED.

Forward: assume the truth (and a proof, h) of P ∧ True.
We need to show the truth of P, in constructive logic
by showing that we can construct a proof of t. A proof
of P is obtained from a proof, h, of P and True, by the
left "and elimination" inference rule applied to h.

Backward: assume the truth (and a proof, h) of P. We need
to show the truth of P ∧ True. We do this by applying the
"and introduction" inference rule to two proofs, one of
P and one of True. From h a proof of P is obtained by
applying the left "and elimination" rule. A proof of
True is always available by the "true introduction" rule.
In Lean, that's the the proof value, True.intro.
-/

/-!
Read and understand what is to be proved. You should see
right away that you'll need to prove (P ∨ False) → P, the
forward implication, that this proof will first assume that
a *disjunction* (or) is true, and then show the conclusion
is true *in either case* that could explain how P ∨ False
is true: either because P is or because False is. Those
are the only two cases to consider for the argument, and
from each case you need to be able to prove the conclusion,
P.
-/

-- #6
def identityOr      : (P ∨ False) ↔ P :=
Iff.intro
  -- forwards
  (fun (h : P ∨ False) =>
    (Or.elim h
      (fun (p : P) => p)
      (fun (f : False) => False.elim f)
    )
  )
  -- backwards
  (fun (p : P) =>
    (Or.inl p)
  )

/-!
Prove: (P ∨ False) ↔ P.
Proof: By iff introduction applied to the forward and
backward implications, which we prove below. QED.

Forward; assume (h : P ∨ False), show (construct a proof
of) P. The proof in this direction is by application of
the "or elimination" inference rule to h. In addition to
h, we need proofs for each case of h. Case 1: It's true
because P is true, In this case, we have the proof we
seek, of P. In the second case, P ∨ False is true because
False is true, but that can never happen, so we dismiss
this case by applying the false elimination rule to the
presumed proof of false.

Backward; We assume we have a proof, (p : P), and we then
constuct the required proof of P ∨ False by applying the
left "or introduction" inference rule to p. There *is* no
proof of False, so there is no possibility of using the
right introduction rule to prove (P ∨ False).
-/


-- #7
def annhilateAnd  : (P ∧ False) ↔ False  :=
Iff.intro
(fun h => (False.elim h.right))
(fun f => False.elim f)

-- You could also write it using nomatch in Lean
example           : (P ∧ False) ↔ False  :=
Iff.intro
(fun h => nomatch h.right)
(fun f => nomatch f)

/-!
Now I want to tell you that while the proof terms we're
given are "top down" (by the application of Iff.intro to
two sub-proofs, each elaborated "in place" where they are
given as arguments), we can also first construct the two
sub-proofs and then apply Iff.intro to the results. In
Lean (and many other functional languages) we use "let"
expressions to bind names to values that we want to use
later on. Here's what it looks like in Lean. We name and
specify the required lower-level proofs first and then at
the end we write an expression for the final result using
these named intermediate values as arguments.
-/

example           : (P ∧ False) ↔ False  :=
  let forward := (fun h => nomatch h.right)
  let backward := (fun f => nomatch f)
  Iff.intro forward backward

/-!
The bottom-up "style" can be seen in natural language proof
sketches. For example you might express this proof in the
following way.

Prove: (P ∧ False) ↔ False
Proof. It will suffice, by application of iff introduction,
to have proofs of the forward and backward implications as
its arguments.

Let "forward" be a proof of (P ∧ False → False) in the form
of a total function from ...

Let "backward" be a proof of the reverse implication, in
the form of a total function from ...

A proof of the equivalence is then obtained by applying
the iff introduction inference rule to the "forward" and
"backward" proofs. QED.

Note that the names we give the intermediate values are
arbitrary as far as the logic is concerned. They could just
as well have been fred and wilma, then we'd simply write
(Iff.intro fred wilma) as the final required proof term.
-/


/-!
Look at what's to be proved. See that the top-level
connective is ↔. That tells you that you will *have to*
apply the iff introduction rule to proofs of the one-way
implications, forward and backward. Next see that in the
forward direction, you must assume proof of a disjunction
and then return a proof of True. That's easy! In the back
direction, given a proof of true you need to construct a
proof of (P ∨ True), but that's always true by applying
the "right or introduction" inference rule to a proof of
true, always available, in Lean as True.intro. QED.
-/


-- #8
def annhilateOr     : (P ∨ True) ↔ True :=
Iff.intro
  (fun h => True.intro)
  (_)

/-!
Most of the proofs in this assignments are proofs of
equivalences (bi-implications). They will thus *all*
be constructed at the top level by applying Iff.intro
to proofs of the forward and backwards implications.
Henceforth we'll just explain in English the forward
and backward proofs. In the formal proof we present
here, the forward proof is in top-down style while the
backward proof is in bottom–up style. This latter proof
has the advantage of making the application of Or.elim
explict, whereas in the top-down proofs it's implicit
in the "case analysis" using match.
-/

-- #9
def orAssociative   : ((P ∨ Q) ∨ R) ↔ (P ∨ (Q ∨ R)) :=
Iff.intro

  -- forward: prove ((P ∨ Q) ∨ R) → (P ∨ (Q ∨ R)), i.e., from (P ∨ Q) ∨ R) show (P ∨ (Q ∨ R))
  -- proof by application of or elimination ("case analysis") to proof of ((P ∨ Q) ∨ R)
  (fun (porq_or : ((P ∨ Q) ∨ R)) =>
    (match porq_or with                       -- case analysis on (h : (P ∨ Q) ∨ R)
      | Or.inl porq =>                          -- case 1: from (porq : P ∨ Q) show  (P ∨ (Q ∨ R))
          match porq with                         -- proof by case analysis of (porq : P ∨ Q)
          | Or.inl p => Or.inl p                  -- case 1: from (p : P) show (P ∨ (Q ∨ R))
          | Or.inr q => (Or.inr (Or.inl q))       -- case 2: from (q : Q) show (P ∨ (Q ∨ R))
      | Or.inr r => Or.inr (Or.inr r)           -- case 2: from R show ((P ∨ Q) ∨ R)
    )
  )

  -- backward: prove (P ∨ (Q ∨ R)) → ((P ∨ Q) ∨ R), i.e.,, from P ∨ (Q ∨ R)) show ((P ∨ Q) ∨ R)
  -- proof by case analysis (or elimination) of (P ∨ (Q ∨ R))
  (fun (por_qorr : (P ∨ (Q ∨ R))) =>   -- convert any h : (P ∨ (Q ∨ R)) to proof of (P ∨ Q) ∨ R)

    -- case 1 for (P ∨ (Q ∨ R)): from (p : P) show ((P ∨ Q) ∨ R); top-down proof
    let from_p : P → ((P ∨ Q) ∨ R) := (fun p => Or.inl (Or.inl p))

    -- case 2 for (P ∨ (Q ∨ R)): from (Q ∨ R) show show ((P ∨ Q) ∨ R)
    let from_qorr : (Q ∨ R) → ((P ∨ Q) ∨ R) :=
      -- proof is by case analysis on proof of Q ∨ R
      (fun from_qorr : (Q ∨ R) =>

        -- case 1 for Q ∨ R: from Q show ((P ∨ Q) ∨ R)
        let from_q : Q → ((P ∨ Q) ∨ R) := (fun q => Or.inl (Or.inr q))

        -- case 2 for Q ∨ R: from R show ((P ∨ Q) ∨ R)
        let from_r : R → ((P ∨ Q) ∨ R) := (fun r => Or.inr r)

        -- now by or elimination prove (Q ∨ R) → ((P ∨ Q) ∨ R)
        Or.elim from_qorr from_q from_r
      )
    -- note that we've proved (P ∨ (Q ∨ R)), P → ((P ∨ Q) ∨ R), (Q ∨ R) → (P ∨ (Q ∨ R)),
    -- now by or elimination, with proofs for both cases, prove (P ∨ (Q ∨ R)) → ((P ∨ Q) ∨ R)
    Or.elim por_qorr from_p from_qorr
  )


-- #10
def andAssociative  : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) :=
Iff.intro
  -- forward: from (P ∧ Q) ∧ R show P ∧ (Q ∧ R), in bottom up proof style
  (fun (pandq_andr : (P ∧ Q) ∧ R) =>
    -- proof of P ∧ Q by and elim left applied to (P ∧ Q) ∧ R)
    let pandq := pandq_andr.left
    -- proof of by and elim right by and elim right applied to (P ∧ Q) ∧ R)
    let r := pandq_andr.right
    -- proof of P by and elim left applied to (P ∧ Q)
    let p := pandq.left
    -- proof of q by and elim right applied to (P and Q)
    let q := pandq.right
    -- and proof of the top-level conjecture by and intro applied two
    -- Lean know you see an "and" proof so it knows ⟨ _, _ ⟩ notation means And.intro
    ⟨ p, ⟨ q, r ⟩ ⟩
  )
  -- backward: from P ∧ (Q ∧ R) show (P ∧ Q) ∧ R, in top-down proof style
  (fun (pand_qandr : P ∧ (Q ∧ R)) =>
    And.intro                     -- construct proof for top-level and in (P ∧ Q) ∧ R
      (And.intro                    -- from a proof of (P ∧ Q)
        (pand_qandr.left)             -- from a proof of p
        (pand_qandr.right.left)       -- and a proof of q (study this Lean expression)
      )
      (pand_qandr.right.right)      -- and a proof of R
  )


-- #11
def distribAndOr    : (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) :=
Iff.intro

  -- forward
  -- from P ∧ (Q ∨ R) show (P ∧ Q) ∨ (P ∧ R) via case analysis of Q ∨ R
  (fun (pand_qorr : (P ∧ (Q ∨ R))) =>
    let p := pand_qorr.left
    let qorr := pand_qorr.right
    match qorr with                   -- or elim by cases
      | Or.inl q => Or.inl ⟨ p, q ⟩
      | Or.inr r => Or.inr ⟨ p, r ⟩
  )

  -- backward
  -- from a proof of (P ∧ Q) ∨ (P ∧ R)  construct a proof of P ∧ (Q ∨ R)
  -- proof is by or elimination on the premise
  (fun pandq_or_pandr =>
    (Or.elim pandq_or_pandr
      (fun pandq => And.intro pandq.left (Or.inl pandq.right))
      (fun pandr => And.intro pandr.left (Or.inr pandr.right))
    )
  )


-- #12
def distribOrAnd    : (P ∨ (Q ∧ R)) ↔ ((P ∨ Q) ∧ (P ∨ R)) :=
Iff.intro

  -- forward
  (fun (por_qandr : (P ∨ (Q ∧ R))) =>
    (Or.elim por_qandr
      (fun (p : P) => And.intro (Or.inl p) (Or.inl p))
      (fun qandr =>
        let q := qandr.left
        let r := qandr.right
        And.intro (Or.inr q) (Or.inr r)
      )
    )
  )

  -- backward
  (fun porq_and_porr : ((P ∨ Q) ∧ (P ∨ R)) =>
    (
      let porq := porq_and_porr.left
      let porr := porq_and_porr.right
      Or.elim porq
        (fun p => Or.inl p)
        (fun q => _)          -- we are stuck!
    )
  )

  -- let's try classical logic

example : (P ∨ (Q ∧ R)) ↔ ((P ∨ Q) ∧ (P ∨ R)) :=
-- for fun, let's do a bottom up proof, first building forward and backwards

    let (forward : (P ∨ (Q ∧ R)) → (P ∨ Q) ∧ (P ∨ R)) :=
      fun (por_qandr : (P ∨ (Q ∧ R))) =>   -- assume (P ∨ (Q ∧ R))
        (Or.elim                            -- show (P ∨ Q) ∧ (P ∨ R)
          por_qandr                         -- by case analysis with cases P, Q ∧ R
          -- in the case where P is true, prove (P ∨ Q) ∧ (P ∨ R) by and intro
          (fun (p : P) =>                     -- assume P
            let porq : P ∨ Q := (Or.inl p)    -- prove P ∨ Q by or intro right with p
            let porr : (P ∨ R):= (Or.inl p)   -- prove P ∨ R by or intro left with p
            And.intro porq porr               -- prove (P ∨ Q) ∧ (P ∨ R) by and intro
          )
          -- in the case where (Q ∧ R) is true, prove (P ∨ Q) ∧ (P ∨ R) with p
          (fun qandr =>
            let q := qandr.left
            let r := qandr.right
            let (porq : P ∨ Q):= Or.inr q
            let (porr : P ∨ R) := Or.inr r
            And.intro porq porr
          )
        )

  -- backward: from ((P ∨ Q) ∧ (P ∨ R)) show P ∨ (Q ∧ R)
  let (backward : (P ∨ Q) ∧ (P ∨ R) → (P ∨ (Q ∧ R))) :=
  fun porq_and_porr : ((P ∨ Q) ∧ (P ∨ R)) =>
    (
      /-
        Force P to be binary: either true with (p : P) or false with (np : ¬P).
        Do this by obtaining a proof (for free) of P ∨ ¬P, then reason through
        each case separately: one where P is true and one where ¬P is true
      -/
      match (Classical.em P : P ∨ ¬P) with

      -- case 1 (P is true with (p : P): with p deduce P ∨ Q ∧ R, by or intro left p
      | Or.inl p => Or.inl p

      -- case 2 (¬P is true): from ¬P show P ∨ Q ∧ R
      | Or.inr np => Or.inr   -- we an only try to prove Q ∧ R
      -- since P is false can only do this by proving Q ∧ R
        (And.intro            -- proof of Q ∧ R is by and intro
          (                   -- first need a proof of Q
            -- proof of Q: from combination of given ¬P and case analysis of (P ∨ Q)
            match porq_and_porr.left with -- by case analysis of (P ∨ Q)
            | Or.inl p => nomatch (np p)  -- P can't happen as that would contradict ¬P
            | Or.inr q => q               -- Q is the only other possibility, so  Q
          )
          (
            --  proof of R: from combination of ¬P and (P ∨ R) by exactly the same strategy
            match porq_and_porr.right with   -- by case analysis of P ∨ R
            | Or.inl p => nomatch (np p)  -- case P: P contradicts ¬P, can't happen
            | Or.inr r => r               -- R is the only other possibility, so R
          )
        )
    )
  -- The main "theorem" is now proved by applying iff intro to forward and backward
  Iff.intro forward backward



/- NOTE

Note a repeated form of reasoning here: (P ∨ Q) ¬P → Q. That is, if P ∨ Q is true
the one of P or Q is true, but if we also know that P is false, that leaves only Q
as true, so it is.

This inference rule is sometimes called "disjunctive syllogism". Let's state and prove
it as a general theorem.
-/

def disjunctiveSyllogism (P Q : Prop) : (P ∨ Q) → ¬P → Q
| porq, np  =>
    match porq with
    | Or.inl p => False.elim (np p)     -- P and ¬P is a contradiction (can't happen)
    | Or.inr q => q                     -- the only remaining possibility is Q, so Q


-- #12
def equivalence : (P ↔ Q) ↔ ((P → Q) ∧ (Q → P)) :=
let forward : (P ↔ Q) → ((P → Q) ∧ (Q → P)) :=
  fun (h : (P ↔ Q)) => And.intro (h.mp) (h.mpr)
let backward : ((P → Q) ∧ (Q → P)) → (P ↔ Q) :=
  fun (h:  (P → Q) ∧ (Q → P)) => Iff.intro h.left h.right
Iff.intro forward backward


-- #13
def implication : (P → Q) ↔ (¬P ∨ Q) :=
Iff.intro
  -- forward
  (fun (h : P → Q) =>
    (match (Classical.em P) with
    | Or.inl p => Or.inr (h p)
    | Or.inr np => match (Classical.em Q) with
                    | Or.inl q => Or.inr q
                    | Or.inr _ => Or.inl np
    )
  )
  -- backward
  (fun (h : (¬P ∨ Q)) =>
    (fun (p : P) =>
      Or.elim
      h
      (fun (k : ¬P) => False.elim (k p))
      (fun q => q)
    )
  )


-- #14
def exportation  : ((P ∧ Q) → R) ↔ (P → Q → R) :=
let forward : ((P ∧ Q) → R) → (P → Q → R) :=
  fun h => fun (p : P) => fun (q : Q) => h ⟨ p, q ⟩
let backward : ((P → Q → R)) →  ((P ∧ Q) → R) :=
  fun h => fun pandq => h pandq.left pandq.right
Iff.intro forward backward


-- #15
def absurdity       : (P → Q) ∧ (P → ¬Q) → ¬P :=
  fun (h : (P → Q) ∧ (P → ¬Q)) =>
    let pimpq := h.left
    let pimpnq:= h.right
    -- function from assumption of P to False is proof of ¬P
    fun (p : P) => (pimpnq p) (pimpq p)


-- #16
def distribNotAnd   : ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) :=
  let pornp := Classical.em P
  let qornq := Classical.em Q

  let forward : ¬(P ∧ Q) → (¬P ∨ ¬Q) :=
  fun h =>
    match pornp with
    | Or.inl p => match qornq with
      | Or.inl q =>
        let pandq := And.intro p q
        nomatch h pandq
      | Or.inr q => Or.inr q
    | Or.inr np => Or.inl np

  let backward : (¬P ∨ ¬Q) → ¬(P ∧ Q) :=
    fun h =>
      match h with
      | Or.inl np => match qornq with
        | Or.inl _ => fun pandq => nomatch (np pandq.left)
        | Or.inr _ => fun pandq => nomatch (np pandq.left)
      | Or.inr nq => fun pandq => nomatch (nq pandq.right)

  Iff.intro forward backward



-- #17
def distribNotOr    : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) :=
  Iff.intro

    -- forward: from ¬(P ∨ Q) show (¬P ∧ ¬Q)
    (fun n_pandq : ¬(P ∨ Q) =>
      let (np : ¬P) := fun (p : P) => n_pandq (Or.inl p)
      let (nq : ¬Q) := fun (q : Q) => n_pandq (Or.inr q)
      And.intro np nq
    )

-- backward: from (¬P ∧ ¬Q) show ¬(P ∨ Q)
    (fun npandnq : (¬P ∧ ¬Q) =>
      (
        fun porq : P ∨ Q => match porq with
        | Or.inl p => npandnq.left p
        | Or.inr q => npandnq.right q
      )
    )


/-!
EXTRA CREDIT: apply the axiom of the excluded middle
to give a classical proof of the propositions (corrected
from one proposition) that you identified as having no
constructive proof.

The axiom is  Classical.em (p : Prop) : p ∨ ¬p.
-/

#check Classical.em
-- Classical.em (p : Prop) : p ∨ ¬p
-- Given any proposition p, you can have a proof of p ∨ ¬p
-- You then have two cases: one with a proof of p, one with ¬p
example (P : Prop) := Classical.em P -- a proof of P ∨ ¬P


/-!
Given nothing but a proposition, P, excluded middle gives
you a proof of P ∨ ¬P 'for free". By "free" we mean that
you can have a proof of AP∨ ¬P without providing a proof
of either P or of ¬P. We call such a proof of (P ∨ ¬P) as
its not constructed by Or.intro left or right, applied to
either a proof of P or to a proof of ¬P. We can say that
a constructive proof is *informative*, in that it not only
profs (P or ¬P) but carries an explanation for *why* it's
true, in the form of either a proof of P or a proof of ¬P.
A non-constructive proof of P ∨ ¬P, provided by em, gives
no information at all about why it's true. That said, the
Or.elim rule applied to such a case will still give you
two cases to consider, one with an assumed proof of P and
the other with an assumed proof of ¬P.
-/

#check P                -- reminder: P is a proposition
#check Classical.em P   -- em gives you a proof of P ∨ ¬P for free

-- And here's a partial proof showing exactly how to use em
example : P → Q :=
  match (Classical.em P) with
  | Or.inl p =>  _      -- from (p : P) show Q
  | Or.inr np => _      -- from (np : ¬P) show Q


/-!
The axiom of the excluded middle forces every proposition
to be either true or false, with no indeterminate "middle"
state where you don't have a proof either way.

Excluded middle is one of several non-constructive
axioms that can be added to Lean simply by stating that they
are axioms. Negation elimination (¬¬A → A), also called proof
by contradiction, is equivalent to excluded middle (can you
prove it?), so if you adopt one you get the other as well.
-/

/-!
Optional reading.

Other axioms from mathematics and logic that you might need
to add to Lean's logic  include the following:

- functional extensionality: with functions f and g, (∀ a, f a = g a) → f = g
- propositional extensionality, (P ↔ Q) ↔ (P = Q)
- choice: Nonempty A → A (fron a proof A is nonempty you can get value of type A)
-/

#check Nonempty P

#check funext
#check propext
#check Classical.choice

/-!
The first axiom let's you conclude (and have a proof) that two
functions are equal if they return the same results on all of
their inputs. The second let's you replace bi-implication with
equality of propositions, and vice versal.

The third? It requires an understanding that when you construct
a proof of ∃ x, P x, E.g., (Exists.intro 4 (Ev 4)) the value you
provided (here 4) is forgotten. You can never get a specific value
back out of a proof of ∃. This fact mirrors the idea that all that
a proof of an existential proposition tells you is that there is
*some* value out there in the universe that satisifes the given
predicate, but not what it is. What this axiom says is that if
you can provide there's some "witness/value", then you can get
an actual value. To prove some theorems in mathematics, you need
this. The tradeoff is that Lean marks the value as non-computable,
which means you can't actually compute anything with it.

If you're interested in learning more, you might want to read
https://lean-lang.org/theorem_proving_in_lean4/axioms_and_computation.html
-/
