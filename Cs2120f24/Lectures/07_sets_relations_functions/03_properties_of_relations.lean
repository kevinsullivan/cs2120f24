import Mathlib.Data.Rel
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Real.Basic

/-!
This file builds on relations defined in 02_relations.lean.
We replicate the definitions here, as importing the earlier
file will cause other problems. We add a third relation, from
persons (by String name) to their ages in years. Tom and Jill
are both 19, and Hec is 20.
-/

def completeStrNat: Rel String Nat := fun _ _ => True
def emptyStrNat   : Rel String Nat := fun _ _ => False
def strlen        : Rel String Nat := fun s n => n = s.length
def strlen3       : Rel String Nat := fun s n => (s = "Hello" ∧ n = 5) ∨ (s = "Lean" ∧ n = 4) ∨ (s = "!" ∧ n = 1)
def acctsOf       : Rel String Nat := fun s n => (s = "Mary" ∧ n = 1) ∨ (s = "Mary" ∧ n = 2) ∨ (s = "Lu" ∧ n = 3)
def ageOf         : Rel String Nat := fun p a => (p = "Tom" ∧ a = 19) ∨ (p = "Jill" ∧ a = 19) ∨ (p = "Hec" ∧ a = 20)

/-!
## Overview: Properties of Relations

There are many important properties of relations. In this
section we'll define the follwoing properties of a relation:

For any binary relation from α to β
- empty: there are no pairs in the relation
- complete: every input in the domain of definition has some output
- single-valued (functional): no input has more than one outpu
- injective (one-to-one): no output has more than one input
- surjective (onto): every output value in the codomain has some input
- bijective: one-to-one and onto

For any binary relation from α to α ("on α")
- reflexive: *every value in the domain of definition* is related to itself
- symmetric: if any value a is related to some value b, then b is also related to a
- transitive: for any a, b, c, if a is related to b, and b to c, then a is related to c
-/

/-!
### The Property of Being Empty

Being empty is a general property that any given relation might
or might not have. We specify this property as a *predicate on
relations*: that is, as a function that takes a relation as an
argument and that returns the proposition that that relation is
empty, which is to that that there cannot be (does not exist) a
pari, (x, y), that is in that relation.
-/

def isEmpty {α β : Type} : Rel α β → Prop :=
  fun r => ¬∃ x y, r x y

/-!
With this definition, let's claim and prove that emptyStrNat is
empty. You'll notice that this reduce command doesn't tell you
the actual definition of isEmpty. However, Lean suggests that
we turn on the (types := true) option. That gives us what we
want.
-/
#reduce (types := true) isEmpty emptyStrNat



example : isEmpty emptyStrNat :=
-- by the definition of isEmpty we are to prove (∃ x y, emptyStrNat x y) → False
-- by negation: assume there is a pair in emptyStrNat (∃ x y, emptyStrNat x y) ...
fun (h : ∃ x, ∃ y, emptyStrNat x y) =>
  (
    -- ... then show a contradiction, and finally conclude False
    -- clearly we have to *use* our assumption that (∃ x y, emptyStrNat x y)
    -- so the rest of the proof is thus by exists elimination
    Exists.elim h
      -- First we eliminate ∃ x, allowing us to assume some x and proof of (∃ y, emptyStrNat x y)
      fun x => fun pfx =>
        (
          -- next we use/eliminate this second proof
          Exists.elim pfx
          -- which allows us assume some y and a proof of (emptyStrNat x y)
          fun y pfxy =>
            (
              -- our assumptions have thus given us a proof that (x, y) is in emptyStrNat!
              -- but the predicate for being in that relation is False, a contradiction
              -- remember that (emptyStrNat x y) reduces to the proposition, False
              -- which makes pfxy a proof of false
              nomatch pfxy
            )
        )
  )
  /-
    Having shown that any assumption that some pair (x, y) is in
    emptyStrNat produces a contradiction, proving by negation that
    there can be no pair of values that are in emptyStrNat which is
    what the isEmpty property means, as we've defined it. Therefore
    (isEmpty emptyStrNat) is proved: The emptyStrNat relation really
    is empty.
  -/

/-
### The Property of Being Single-Valued

THE REST OF THIS FILE IS UNDER CONSTRUCTION

Our acctsOf relation is not single-valued, as there are two
outputs for the single input, "Mary". On the other hand, our
strlen3 relation is single valued. For any given string in
the domain of the relation, {"Hello", "Lean", "!"}, there is
exactly one output, namely its natural number length.

A very important principle in mathematics then is that it's
the property of a relation, r, being "single-valued" that
distinguishes it as a *function*, and not just any relation.

So how can we define this property of being single-valued in
a mathematically precise manner? Let's start with acctsOf as
a counter-example. It's not single valued. To see that, all
we need are two pairs in acctsOf with the same first element
and different second elements: ("Mary", 1), ("Mary",2). In
other words, for a given input, x (here "Mary"), to acctsOf,
we have outputs, y=1 and z=2, where y ≠ z! If acctsOf were
a single-valued relation and both (x, y) and (x, z) were in
the relation it would simple have to be the case that y=z.
You can't get different outputs for a single input from a
single-valued relation.

We are led to the general definition of the property of a
relation being single valued. We define a relation r on α
and β as single valued when

  ∀ (a : α) (b c : β), r a b ∧ r a c → b = c.

This says that a relation is single valued if for any a in
its domain and and b and c in its codomain, the only way you
can have both (a, b) and (a, c) in the relation is if b = c.

Proof. The relation contains only the pairs, ("Hello", 5),
("Lean", 4), ("!", 1). For each of the three strings in the
domain, it's clearly the case that there is only one related
output value. QED.

To formalize this notion takes us to a very cool place where
we're talking about predicates on (properties of) relations!
-/

/-
NB: old version from class

def singleValued {α β : Type} : Rel α β → Prop :=
  fun r : Rel α β =>
    ∀ (a : α) (b c : β), r a b → r a c → b = c

Corrected version here
-/

def singleValued {α β : Type} (r : Rel α β) : Prop :=
    ∀ (a : α) (b c : β), r a b → r a c → b = c

/-!
This is a precise and general mathematical definition what
it means to be a single-valued relation. For any two types,
α and β (possibly the same), and any binary relation, r, on
α and β, the expression *singleValued r* means just this:
∀ (a : α) (b c : β), r a b → r a c → b = c.

This is the logical proposition you have to prove if you
are claiming to show that r is singleValued. Let's take a
quick look at how we'd formalize the problem to be solved:
to prove (singleValued strlen3).
-/

theorem strlen3IsSV : singleValued strlen3 :=
  -- Prove: ∀ (a : α) (b c : β), r a b → r a c → b = c
  -- By: assume values, a b c, and proofs of r a b and r a c
  fun a b c hab hac =>
  /-
  In this context, show prove b = c. That's what the proof state
  reported by Lean tells us.

  a : String          - a, to name an arbitrary string input
  b c : ℕ             - b and c, to name corresponding outputs
  hab : strlen3 a b   - hab, a proof showing (a, b) is in strlen3
  hac : strlen3 a c   - hac, a proof showing that (a, c) is in the relation
  ⊢ b = c

  Above or to the left of the turnstile are the values we have
  assumed we have. Elimination rules are applied to these things.
  After the turnstile is the type of proof we have to construct
  from whatever we have to use.

  Ok, so enough bureaucracy. How do we prove b = c is true for
  all* values a : α, for all values, (b c : Nat), restricted to
  values that satisfy strlen3 a b and strlen3 a c? It might not
  jump right out.

  But look at the sequent (proof state). What do you have to
  work with? The fact that a is some arbitrary string isn't any
  help. Nor is knowing that b and c are natural numbers. All of
  the really useful information is locked up in these proofs.
  You know who to call: Our only hope is Elimination Dog! He
  picks the right elimination rules and uses them to squeeze
  all kinds of information out of the proofs it's locked up in.

  How does he know which elimination rule to apply to a given
  value or proof? By it's form. If it's a proof of a disjunction,
  only Or.elim will do. If it's a proof of an implication, only
  → elimination will do (apply the function to an argument to
  get something else that might be useful).

  Focus on what you have to work with and really hard about
  what each element means and how you can *use* it by applying
  eloimination rules.

  For example, what exactly is (hab : strlen3 a b). The crucial
  idea forever after right this moment is that when proving some
  complicating thing, you will have to say, "by the definition of"
  whatever, it will suffice to prove whatever else. So what is the
  definition of strlen3 a b? Go look at the definition of strlen3!
  Here it is for you.

  def strlen3 : Rel String Nat := fun s n =>
  s = "Hello" ∧ n = 5 ∨
  s = "Lean" ∧ n = 4 ∨
  s = "!" ∧ n = 1

  It's a predicate, if applied to argument a (a string) and b (a
  natural number) it reduces to a proposition. That proposition is
  obtained by replacing each s in the parameterized proposition with
  a, and each instances of n in the parameterized proposition with b.

  What hab is then is a proof of this proposition. It states that
  there are only three ways that a String/Nat pair, (a, b) can be
  in this relation: It's ("Hello", 5) or it's ("Lean", 4) or it's
  ("!", 1). That's it.

  But that's also a lot. What we can do with such a proof is a case
  analysis. We want to show b = c. The only thing we can do with
  hab, or with hac, is case analysis. The big idea, though, is that
  if we can show that the conclusion, b = c, holds in all cases,
  then it is true *in all cases* under the prevailing assumptions.

  It's still not entirely clear how to proceed, so let's see what
  we find if within each case for hab we also apply a case analysis
  to hac? We basically have a 3 X 3 grid of cases to consider. The
  remaining challenge is to show that *in each case* we can show
  that b = c.

  Let's look at the first case for hab along with the first and second
  cases for hac.

  The first case for hab is where the strlen3 predicate is
  satisfied by the pair, (a = "Hello", b = 5), and this is
  also the first case for hac, with (a = "Hello", c = 5). Do
  note that hac speaks about a value called c. Do you see it?
  In this case, b = c.

  Now consider the first case for hab, (a = "Hello", b = 5),
  along with the second case for hac, (a = "Lean", b = 4). In
  this second of our nine case, we've assumed (a = "Hello" and
  a = "Lean". From these assumptions it's easy to conclude that
  "Hello" = "Lean" but there's no way even have a proof of that
  so this is a case that doesn't satisfy the conditions for the
  definition of singleValued to hold. We'll find three cases of
  nine where the a-values are the same, and in each case, there
  is no possibility of different values of b and of c.

  Now if we were to add, say, ("Hello", 6) to the relation, the
  relation, would no longer be single valued. That would show up
  in one of the cases, e.g., (a = "Hello", b = 5) from hab paired
  with the case, (a = "Hello", bc = 6) from hac. In this pair of
  cases, it's definitely not true that b = c. The extended relation
  is thus not singleValued. In fact, if you are clever, you could
  prove, formally, here, that it's not singleValued.

  The case analysis is Lean is more tedious. You do case analysis
  on hab, breaking it into a first dijunct and all the rest. So
  getting to the three cases for hab involves extra work. Then
  within each of those cases, you have to do the same thing to
  perform a case analysis of hac. There's yet more detail inside
  each case.

  The good news is that Lean is a programming language and so you
  can define programs, generally called tactics, in Lean, that can
  do things like iterate through nested cases, applying the same
  logic to each. Here that'd be to see if the a values match and
  if the do to see that b = c; and if the a values don't match,
  that mismatch is a contradiction, which you can eventually just
  dismiss, whether by False elimination or more generally by case
  analysis on a proof or value to show that no constructor could
  have produced that putative proof. That's what (nomatch h) does.
  -/

  -- case analysis of hab (3 cases total)
  match hab with

  --  CASE #1 of hab: (a = "Hello" ∧ b = 5)
  | Or.inl ahb5 =>

    /- NESTED ANALYSIS OF hac
    It's here that you do a nest case analysis
    of hac, in exactly the same style. We'll go
    two levels down, at which point we will have
    seen the two different kinds of cases.
    -/
      match hac with

      -- Case #1 of hac: (a = "Hello" ∧ c = 5)
      | Or.inl ahc5 =>
        /-
        At this point, but for one detail, we can
        see we're about done. ahb5.right proves b = 5
        while ahc5 proves c = 5. From these two proofs
        of equalities, we can deduce b = 5, and that's
        what we want to prove is true *in every case*.
        Technically we use the elimination axiom, which
        lets us rewrite b in the goal as 5 (using our
        proof of b = 5) and c in the goal as 5 (using
        proof of c = 5) at which point all we need is
        a proof of 5 = 5 to be done this with case.
        And as we know (Eq.refl 5) constructs a proof
        of 5 = 5 (the shorthand, rfl, works here, too.)
        -/
        -- proof of b = c in this case
        by  -- technically jumps us in to tactic mode
          rewrite [ahb5.right]
          rewrite [ahc5.right]
          rfl

      -- Analysis of the next two cases for hac
      | Or.inr rest =>
          match rest with

          -- Case #2 for hac: (a = "Lean" ∧ c = 4)
          | Or.inl alc4 =>
            (
              -- Dismiss this case for having different a values
              let ah := ahb5.left
              let al := alc4.left
              (by
                rw [ah] at al
                -- use ah : a = Hello to rewrite a in al
                -- making al a proof of "Hello" = "Lean"
                -- nomatch will confirm that's impossible
                nomatch al
              )
            )
          -- Case #3 hac, still in case #1 for hab: (a = "!" ∧ c = 1)
          -- This case will be handled just like the last one
          | Or.inr aec1 => _

  -- case #1A: analyze  (a = "Lean" ∧ b = 4) ∨ (a = "!" ∧ b = 1)
  | Or.inr rest =>
    match rest with

    -- Case #2 of hab: (a = "Lean" ∧ b = 4)
    | Or.inl alb4 => _
    /-
    This second case of hab will match up with the
    second case in a nested analysis of hac, with b = c
    in that case, and the first and third cases being
    irrelevant for not satisfying the condition that
    the input be the same to get both b and c.
    -/

    -- Case #3 of hab: (a = "!" ∧ b = 1)
    | Or.inr aeb1 => _
    /-
    Finally, here's the third case for hab. A nested
    analysis of hac will be handled just the same but
    not it'll be the first two pairs of cases for hab
    and hac will be irrelevant, while the third will
    have matching inputs and again equal outputs.

    So in all cases, b = c. That proves the conjecture.
    QED.
    -/


/-!
Okay, we have now (1) specified a relation, with three pairs,
on String × Nat; (2) specified with it means for *any* binary
relation to be singleValued; and (3) proved that our strlen3
relation is single value. That means that it is a function, in
particular.

Two questions might arise here. First, how does this notion
of a function, defined using logic, relate to a function in
Lean defined as a λ/fun expression. The answer is that every
function defined as a program (using fun/λ explicitly or not)
must be *total*. That means it has to produce a result for any
value of the input type. But some functions are partial. We
can see that strlen3 is, insofar as it represent a way to get
from one of only three strings out of the infinitude of all
stringst. We'd say strlen3 is a *partial* function, with its
domain a proper subset of its domain of definition, String.

Second question. What good are these ideas? One answer is
thta they give you a beautiful language for thinking about
and specifying precisely what you want in a software system.

Suppose you have the great pleasure of having to rebuild
America's Social Security Number Assignment System. Its
job is to maintain a relation between people and their
social security numbers. Should this relation be a function
in particular? What desirable property of social security
number assignment does that assure? Yes: that no person
shall ever have more than one SSN.

Is that a strong enough condition on the SNN-assignment
relation? No. What other malfunction is not yet ruled out?

Right! We also don't want two different people ever to
be assigned the same SSN. This is a different property,
in addition to single-valuedness. The latter means no one
input has more than one output. The former means that no
one output has more than two source inputs.

The property of a binary relation, that no two distinct
domain elements go to the same element in the co-domain.
For example, no two people have the same SNN. Not only is
the person-to-SSN relation a function (so no person has
more than one SSN) but beyond that it is injective (so
no two people have the same SSN).
-/
