import Mathlib.Data.Rel
import Mathlib.Data.Set.Basic
import Cs2120f24.Library.setTheory.«03_properties_of_relations»
/-
Homework #8 Properties of Relations

You must be able to do this homework on your own.
If getting to that point requires collaboration, you
may collaborate with up to two other people. In this
case, you are to hand in one assignment with the names
and email addresses of all the collaborators. Each
collaborator must work with every other one on this
assignment. You may not just split the problems one
or two for each person.
-/

/-!
We've importd all of the definitions of properties of relations
from 03_properties_of_relations so you can use them here with no
problem. Use View > Editor Layout > Split Down to have two panes
open, one looking at the property definitions file and one open
on this one.

PREREQUISITE: Thoroughly study lecture 7, files 1, 2, and 3, on
sets, relations, and properties of relations. Remember, you cannot
learn to construct proofs by just reading Lean proof terms. You
really have to construct them on your own. So where we give you
proofs, *copy them into a comment, then delete them, then build
them back, cheating by looking at the saved comment if you must*.
-/

/-
PROBLEM #1 [25 points]. We've see that, in Lean, every function
of type α → β is total. Any such function in Lean must be defined
*for all* values of the intput type, α. If you fail to provide an
output value for every input, Lean will tell you you're "missing
cases." It's super-important in constructive logic that functions
are total because we use them to prove universal generalizations!
To prove ∀ (x : α), P x, we define a function from (x : α) to P x.
The reason a function proves a universal proposition is that every
function in constructive logic is required to be total.

We can turn any function, f, in Lean into a binary relation by
specifying the relations' membership predicate to be nothing
other than (fun a b => b = f a). This says that a pair, (a, b)
is in this relation for a function f exactly when b = f a.

Here's a function, funToRel, that takes any function from any type,
α to any type β, and that returns the corresponding binary relation
with this membership predicate. To be absolutely clear, funToRel takes
two types, α and β (implicitly), and any function, f : α → β, and it
returns a binary relation from α to β, specified by its membership
predicate, as stated.
-/

def funToRel { α β : Type} : (f : α → β) → Rel α β :=
  fun f => fun a b => f a = b

/-!
Now we can propose, and you are to complete the proof,
that every relation obtained from any function (using
funToRel) has the property of being total, as defined
by our isTotal predicate on binary relations. We give a
good amount of the proof in English, and a little bit
of it in Lean. You finish the missing formal parts.
-/
example {α β : Type} (f : α → β) : isTotalRel (funToRel f) :=
/-
by the definition of total, what is to be proved is that
∀ (x : α), ∃ (y : β), r x y. We first assume an arbitrary
input value a, then we show there exists a corresponding
output value such that the pair is in the relation. Just
a little thought produces (f a) as the witness, as it is
exactly the value that corresponds to the input, a. Then
we need to prove ((funToRel f) a (f a)). By the definition
of funToRel we need to show that (a, (f a)) is in the
relation but that requires exactly that the output, f a,
is equal to f applied to the input, a, i.e., f a = f a.
-/
fun a =>
  Exists.intro
  (_)
  (_)


/-!d
PROBLEM #2 [25 points]

We repeat here the definition of the bank account
number relation from the relations.lean file. Here
you are to state and prove the proposition that this
relation is not single-valued.
-/

def acctsOf : Rel String Nat := fun s n =>
  s = "Mary" ∧ n = 1 ∨
  s = "Mary" ∧ n = 2 ∨
  s = "Lu"   ∧ n = 3


example : ¬isSingleValuedRel acctsOf :=
-- assume acctsOf is single valued:
fun (h : isSingleValuedRel acctsOf) =>
-- show that that implies 1 = 2
-- as that's absurd, conclude ¬isSingleValued acctsOf
(
  -- ∀ x y z, r x y → r x z → y = z

  -- First get proofs that ("Mary",1) and ("Mary", 2) are in acctsOf
  let a1 : acctsOf "Mary" 1 := Or.inl ⟨ rfl, rfl ⟩
  let a2 : acctsOf "Mary" 2 := Or.inr (Or.inl ⟨ rfl, rfl ⟩)

  -- You should see that that contradicts h
  -- Now use h to derive an evident contradiction
  let contra := h _ _ _ _ _
  -- And show that that can't possibly be
  -- Allowing you to conclude that h can't be true so ¬h must be
  _
)

/-!
PROBLEM #3 [25 points]

State formally and prove the proposition that the
successor relation on natural numbers (Nat.succ) is
an injective function. You can use funToRel applied
to Nat.succ to define that relation if you want.
-/

def succRel := funToRel Nat.succ

#reduce (types:=true) succRel 1 2
-- reduces to the proposition Nat.succ 1 + = 2, i.e., 2 = 2

example : succRel 1 2 := rfl

-- HERE
example : isInjective succRel :=
And.intro
  -- succRel is a singleValued relation (a function)
  (fun a b c hab hac =>
    -- note that hab and hac are proofs of Nat.succ a = b and Nat.succ a = c
    -- rewrite goal from b = c to a.succ = b.succ hab and hac (right to left)
    -- that leaves a.succ = a.succ, which rw proves by the reflexivity of =
    by rw [←hab, ←hac]    -- the ← means rewrite right hand in goal with left
  )
  -- succRel is an injective relation
  (_)   -- ok, you have to prove the rest


/-!
PROBLEM #4 [25 points]

A. Given (non-zero) natural numbers a, b, and n, we
say that a is congruent to b mod n if a mod n = b mod n.
Complete the following definition of the binary relation,
congruence mod n.
-/

def congruentModN (n : Nat) : Rel Nat Nat := fun a b => _

-- Test cases will succeed when you give the right definition
example : congruentModN 4 8 12 := rfl
example : congruentModN 5 25 50 := rfl
example : ¬congruentModN 4 4 9 := fun h => nomatch h


/-!
Now prove the proposition that congruence mod n is an equivalence relation
-/
example (n : Nat) : @isEquivalence Nat Nat (congruentModN n) :=
/-
By the definition of equivalence, what we need to show is that the
relation is reflexive, symmetric, and transitive.
-/

And.intro
  -- It's reflexive
  (
    _
  )

  (
    And.intro
    -- It's symmetric
    (_)

    -- It's transitive
    (_)
  )

/-
B. Formally state and prove that congruenceModN for any
given n
We define congruence mod n as a binary relation
on the natural numbers  m and n are congruent mod k

Formally state and prove the proposition that

-/
