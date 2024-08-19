/-
PROPOSITIONS

A logical proposition asserts that some state of affairs
holds, is some domain of interest. To illustrate this point,
*suppose* we have three propositions that assertion states
of affairs in a domain about water, weather, and wetness.

We introduce these propositions as *axioms*. In logic, an
axiom is a judgment that is assumed to be true without any
further proof. Here we're assuming that each named object
is a proposition.
-/
axiom ItsRaining : Prop
axiom SprinklerRunning : Prop
axiom StreetsAreWet : Prop


/-
Now using the *syntax* rules of our logic, we can form an
infinitude of more complex propositions. These propositions
then assert that more complex states of affairs hold.
-/

-- It's raining and the sprinkler is running (both)
def rainAndSprink := ItsRaining ∧ SprinklerRunning

-- It's raining or the sprinkler is running (at least one)
def rainOrSprink := ItsRaining ∨ SprinklerRunning

-- If it's raining or sprinking then the streets are wet
def ifEitherThenStreetsAreWet := (ItsRaining ∨ SprinklerRunning) → StreetsAreWet

/-
PROOFS

In the logic of modern proof assistants, *propositions* are
formalized as *types*, the *values* of which are its proofs
(if there are any).
-/

/-
So now let's suppose (accept as axioms) that we're given the
following proofs of the following propositions. Each line is
a simple *type* judgment, asserting, for example, that *pfRain*
is a *value* (proof!) of the following *type* (proposition!).
-/
 axiom pfRain : ItsRaining
 axiom pfSprink : SprinklerRunning
 axiom pfRainWet : ItsRaining → StreetsAreWet
 axiom pfSprinkWet : SprinklerRunning → StreetsAreWet

/-
Now let's construct some proofs
-/

/-
First we present a top-down, type-guided, structured
development of a proof of a simnple conjunction. Here
we write the proof as a *value* (or *term*) in Lean.
-/
theorem rs : ItsRaining ∧ SprinklerRunning :=
  -- Use the inference rule called and introduction applied to proofs of P and Q
  And.intro pfRain pfSprink

/-
There's a second way to construct proofs in Lean: using
its libraries of proof building *tactics*. Tactics are
proof building scripts that can  building of more complex
proofs.
-/
theorem rs' : ItsRaining ∧ SprinklerRunning := by
  apply And.intro pfRain pfSprink

/-
Lean beautiful overloaded mathematical notations.
The example keyword lets you give and check a proof
without giving it a name. Notice again that we are
using a method of *top-down, structured, type-guided*
proof construction
-/
example : ItsRaining ∧ SprinklerRunning :=
  ⟨ _, _ ⟩



/-
Let's look at a more interesting example: a proof of
a proposition having the form of an implication. A good
way to think about what we need is a function that, if
given any proof of ItsRaining ∧ SprinklerRunning returns
a proof of ItsRaining. Assumptions are just *arguments*
to such functions. Students in this class become very
familiar with function-defining (lambda) expressions.
-/
theorem ifRainAndSprinkThenRain :
  ItsRaining ∧ SprinklerRunning → ItsRaining :=
    _


-- The same proof but now using tactic library
theorem ifRainAndSprinkThenRain' :
  ItsRaining ∧ SprinklerRunning → ItsRaining := by
    intro h         -- If we assume proof/truth of premise,
    exact h.left    -- we can construct proof of conclusion.
                    -- That proves the implication. QED.



/-
Next, let's see some proofs of logical disjunctions (or).
How many different proofs are there of this proposition?
This example illustrates proof by application of the rules
for *or introduction*
-/
example: ItsRaining ∨ SprinkerIsRunning :=
_


/-
Here's a more interesting example. It's a proof
using case analysis to derive a conclusion from a
disjunction. The intuition is that the conclusion
holds in *either case* so it thus follows from the
disjunction. This illustrates reasoning using the
*or elimination* inference rule.
-/
example : (ItsRaining ∨ SprinkerIsRunning → StreetsAreWet) :=
  λ hor =>          -- assume premise (with hor as proof of it)
    Or.elim hor     -- prove by or intro (case analysis)
      (_)           -- conclusion holds in first case
      (_)           -- conclusion holds in second case
                    -- conclusion holds in either case
                    -- implication holds in either case QED

/-
The higher-order logic of Lean is super-expressive. For
example, because we can now quantify over *propositions*,
we can formalize and then *apply* general rules of logic!
-/

theorem and_commutes : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P :=
by
  -- assume P and Q are arbitrary propositions
  intro P Q
  -- prove bi-implication from proofs in each direction
  apply Iff.intro
    -- proof of forward implication
    (by
      intro h
      exact ⟨ h.right, h.left ⟩)
    -- proof of reverse implication
    (by
      intro h
      exact ⟨ h.right, h.left ⟩)


/- And now the operation of universal instantiation.
In other words, we can *apply* a genereal theorem to
a *special case* to get a *proof for that particular
case*.

Exercise: Prove *ItsRaining ∧ SprinklerRunning ↔
SprinklerRunning ∧ ItsRaining*. Proof is by the
application of our already proved general theorem!
-/

#check and_commutes ItsRaining SprinklerRunning

/-
The "theorem application" term, *(and_commutes ItsRaining
SprinklerRunning)* is accepted as a proof of the special case,
ItsRaining ∧ SprinklerRunning ↔ SprinklerRunning ∧ ItsRaining.
The *universal generalization* (a function!) is reduced to a
proof of a specific case by application to specific arguments,
here the specific propositions, ItsRaining and SprinklerRunning.
-/

/-
A look ahead: induction rules of inference for Nat and List α.

Natural Numbers:
{motive : Nat → Prop} →                   -- if motive is any property of nats
motive Nat.zero →                         -- and if you have a proof of it for zero
((n : Nat) → motive n → motive n.succ) →  -- and if you have a proof of the ind step
(t : Nat) →                               -- then given *any* natural number, t
motive t                                  -- t has that property, so it holds ∀ t

Induction over Lists is nearly identical:
{α : Type} →
{motive : List α → Prop} →
motive [] →
((head : α) → (tail : List α) → motive tail → motive (head :: tail)) →
(t : List α) →
motive t

Indeed, *every* inductively defined datatype comes
with its own induction axiom, derived from the very
structure (often recursive) of the datatype. In my
field of software engineering and languages, it is
commonplace to do induction program syntax trees in
the course of defining and verifying properties of
programming languages. It completely generalizes.
-/

#check @Nat.rec
#check @List.rec

inductive MyTree where
| node (val : Nat)
| tree  (val: Nat) (left right : MyTree)

#check MyTree.rec

/-
Whoa: an induction principle for values of our own MyTree data type!

{motive : MyTree → Sort u}                        -- if motive is a property of trees
(node : (val : Nat) → motive (MyTree.node val))   -- and property holds for any singleton tree
(tree :                                           -- and if property holds when tree is buit from any value and any subtrees already having the property
  (val : Nat) →
  (left right : MyTree) →
  motive left →
  motive right →
  motive (MyTree.tree val left right))
(t : MyTree) : motive t                           -- then any tree t has is, so it holds ∀ trees
-/


/- EXTRA MATERIAL
Going deeper, ∧ is notation for the polymorphic inductive
proposition builder, And : Prop → Prop → Prop. The single
*value/proof* constructor for this data type ("And.intro")
stipulates: if (p : P) -- p is a proof of P -- and (q :Q).
then the term, (And.intro p q), often notated as ⟨ p, q ⟩
type checks as a proof of P ∧ Q. I.e., ⟨ p, q ⟩ : P ∧ Q.

Hover over #check to see the type of *And*. Hover over
*And* for documentation on this type/proposition builder.
In addition to the "introduction" rule that we just saw,
it also explains the two (left and right) "elimination"
inference rules for *And*: from a proof of P ∧ Q (just)
a pair of proofs!) you can derive a proof, (p : P), and
you can also derive a proof (q : Q). I.e., P ∧ Q → P and
P ∧ Q → Q.
-/

example : ∀ (P Q : Prop), P ∧ Q → P := fun P Q hpq => hpq.left
example : ∀ (P Q : Prop), P ∧ Q → Q := fun _ _ hpq => hpq.right

/-
Here are the actual inductive type definitions of And and Or.
The "structure" keyword is a special case of inductive for types
with just one constructor (here called "intro"). There's only one
way to prove a conjunction, but there are two disjoint ways to
prove a disjunction: with a proof of the left, or a proof of the
right, disjunct.

structure And (a b : Prop) : Prop where
  intro ::  -- name of constructor
  left : a  -- takes a proof, left, of a
  right : b -- and a proof, right, of b

inductive Or (a b : Prop) : Prop where
  -- proved with *either* a proof of a
  | inl (h : a) : Or a b
  -- of proved with a proof of b
  | inr (h : b) : Or a b
-/

/-
A proposition is judged to be true once any
proof of it is constructed. A proposition is
judged false one a proof is given that the
existence of a such proof leads to a contradiction
(proof by negation). Finally, a proposition for
which neither a positive or a negative proof has
been given cannot be judged to be either true or
false. This is the famous *middle* truth value,
excluded from consideration in classical logic.
If you want to do classical reasoning in the
more general logic of Lean, you can just accept
excluded middle as an axiom and be on your way!
-/

axiom excluded_middle : ∀ (P : Prop), P ∨ ¬P

/-
In other words, excluded middle is essential
a function. You give it *any* proposition, P,
and for *free* it returns a value (proof!) of
type (P ∨ ¬P).
-/

#check (excluded_middle ItsRaining)
-- excluded_middle ItsRaining : ItsRaining ∨ ¬ItsRaining

/-
The standard move in proof construction using exc_mid
is to get such a proof of a true-or-false disjunction,
do *case analysis* on it, and prove each case separately.
-/

example (P Q : Prop): P → Q :=
by
  -- assume P is a proposition (∀ introduction)
  intro hP
  -- use excluded_middle to get proof of P ∨ ¬P
  let disj := (excluded_middle P)
  -- now just do case analysis on the *two* cases
  cases disj
  -- case where disjuction true because P is true
  sorry   -- stub out sub-proof (accept as axiom for now)
  -- case where disjunction is true because ¬P is true
  sorry   -- stub out sub-proof (accept as axiom for now)
