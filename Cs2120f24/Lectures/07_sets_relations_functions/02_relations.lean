import Mathlib.Data.Rel
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Real.Basic


/-!
# Relations

Intuitively, a set is a collection of objects. A homogenous set
is a collection of objects all of the same type. So we can talk
about a set of people, a set of numbers, a set of functions, etc.

In type theory we represent a set as its membership predicate. In
other words, a set, (s : Set α), is represented as a one-argument
predicate, s : α → Prop.

Abstract operations on sets, such as union (∪) and intersection
(∩) are then defined as logical operations on such predicates.
For example, if s and t are sets (of α values), represented as
predicates, s : α → Prop and t : α → Prop, then s ∩ t is also a
set, and it is represented by the predicate fun a => s a ∧ t a.

Similarly a *binary relation* on two sets (or types) α and β, is
understood as a *set of ordered α-β pairs*. And, in type theory,
just as with sets, we represent such a relation as a *two-place*
predicate: one that is satisfied by all and only those pairs of
values that are in the relation.

## Binary Relations

In the abstract, a binary relation, r, on sets α and β (or from
α to β), is understood as a *set* of ordered pairs, (a, b), where
(a : α) and (b : β). In Lean, such a relation is an object of the
type, Rel α β, which is turn is defined as a two-place predicate,
r : α → β → Prop. To show that r relates some value (a : α) to
some value, (b : β), i.e., to show that some pair (a, b) is "in"
r, give a proof of the proposition (r a b).
-/

/-!
To illustate, we'll assume for the rest of this file that α
and β are the domain of definition and codomain of some
relation, r, from α to β. In Lean4, the polynorphic type,
Rel α β, is the type of any binary relation from α to β.
-/

axiom α : Type
axiom β : Type
axiom r : Rel α β

/-!
Let's see how to set up to prove that some pair of values,
(a, b), is "in" (related by) r. We'll first assume we've
got values, (a : α) and (b : β), respectively in the domain
of definition (α) and codomain (β) of r.
-/

axiom a : α
axiom b : β

/-
This is now how you would claim that r relates a to b.
Clearly we don't have enough information here to prove
is, so we'll just put sorry (telling Lean to accept the
fact without proof, as a new axiom,, without a proof).
-/

example : r a b := _

/-!
You will sometimes see an infix operator symbol defined
to mean r, so that instead of writing (r a b) one can
write, e.g., a ≺ b. Don't make the mistake of reading
the symbol as "less than." Rather, read this string as
"a is related to b (by r)."
-/

/-!
Here's a typical concrete notation definition. There's
nothing special about our choice of notation here. You
can choose another infix symbol as you might choose.
-/

infix:50 " ≺ " => r

/-!
Now you can write (r a b) like this, and read the expression
as "a is related to b by (or under) r."
-/

example : a ≺ b := _

/-!
## Representing Binary Relations as Two-Place Predicates

Just as we've specified and represents sets of objects of some
type α as one-argument predicates, now here we will specify and
represent binary relations from one type, α, to another (possibly
the same) type, β, as a two place predicate. A set membership
predicate indicates whether a given value is in the set or not:
if the value satisfies the predicate, it's in, otherwise it's
not. Similarly, we'll use a two-argument predicate to specify
what ordered pairs, (a : α, b : β), are "in" a binary relation.

The polymorphic type, Rel α β, in Lean is thus defined to be
exactly the type α → β → Prop: a predicate that takes one value
of type α and one value of type β and that yields a proposition
that is true (and in Lean that means for which there is a proof)
if and only if that pair, (a, b), is in the relation. You could
also say if and only if that pair satisfies the predicate (or "is
a model for it", if you want to be really clever).
-/

#reduce Rel
-- fun α β => α → β → Prop
-- the right side is the type of a predicate on α and β


/-!
## Running Examples

Let' see these ideas in play.

### The Complete String-Nat Relation

Our first examples is of a relation, call it fullStringNat,
that relates every String to every Nat (natural number). This
relation imposes no conditions on which String-Nat pairs are in
the relation, so they all are.

The predicate defining this relation has to be true for *all*
pairs of values. The solution is for the predicate to yield the
proposition, True, for which there is always a proof, for *any*
pair of String and Nat values. In paper and pencil set theoretic
mathematics we could define fullStringNat as { (s,n ) | True }.
In the type theory of Lean, we'll specify the relation using
its predicate represented as a function, as usual.
-/

def completeStrNat : Rel String Nat :=
  fun s n => True

/-
Given this definition we can show that any pair of values is in
the relation, or related to each other through or by it. As one
example, let's show that the pair of values, "Hello" and 7, is in
this relation. Remeber, the relation is not just specified here by
a predicate but also represented by one; and a predicate in turn
takes two arguments (is applied to two arguments) to produce the
proposition that that pair of values satisfies the predicate.
-/

example : completeStrNat "Hello" 7 :=
  _

/-
Hovering over the _ prompts Lean to show you what is to be proved:
(fullStringNat "Hello" 7). But you already knew that. A really key
idea in proof development is that sometimes, to get to a proof, you
have to "unfold" definitions to see, in lower-level detail, what it
is that you really have to prove.

In this case, unfold (apply) the definition of fullStringNat to
its two arguments. Go look at the definition of fullStringNat to
see, on the right hand side, what it returns as a proposition to
prove. It's just True. *That* is what you have to prove here, and
that's no effort at all, as True is always true, with True.intro
as its proof.
-/

example : completeStrNat "Hello" 7 := True.intro


/-!
### The Empty Binary Relation (From String To Nat)

Not every element in either α or β needs to be related by a
given relation, r. In the extreme case where r is the *empty*
relation from α to β, r does not relate any pairs. The domain
of definition is still the set of all values of type α. The
co-domain is still the set of all β values. But the set of
pairs in r is empty. The predicate on pairs that no pair can
satisfy is (fun s n => False). It ignores it arguments and
returns False, which cannnot be true for any pair, (s, n).
-/

def emptyStrNat : Rel String Nat := fun s n => False

/-!
We can of course prove that no pair of values can satisfy this
relation.
-/

example : ∀ s n, ¬emptyStrNat s n :=
-- by ∀ intro: assume s and n are arbitrary values ...
fun s n =>
  --  then show ¬empty s n; the proof is by negation
  -- first assume that (empty s n) is true, with h as a proof of it ...
  fun h =>
  -- .. then show False
  -- by the definition of empty, h is a proof of False
    h

/-
### The String-Length Relation

A complete binary relation is usually not interesting. A
smaller relation on the other hand can be very interesting
and usefiul. Here we will consider the "subrelation" of our
full relation, restricted to contain only (and all) of the
String-Nat pairs, (s, n), where n is the String length of s.
Again we specify the relation by its membership predicate:
n = the length of s.
-/

def strlen : Rel String Nat :=
  fun s n => n = s.length

/-
While we were able to prove that ("Hello", 7) is in the full
relation, we will not be able to show that it's in this more
restrictive relation, because the length of "Hello" (which is
defined separately and computed by the String.length function
in Lean), is 5, and 7 is not equal to 5.
-/

example : strlen "Hello" 7 :=
-- What we need to prove is 7 = "Hello".length, i.e., 7 = 5.
  _     -- We're stuck, as there can be no proof of that.

/-!
We weren't able to show that the length of "Hello" is 7, but
that's not yet a proof that that's not true. Let's now try to
prove that ("Hello", 7) is *not* in the strlen relation.
-/

example : ¬strlen "Hello" 7 :=
/-
The proof is constructed by negation. Assume strlen "Hello" 7;
show that leads to a contradiction; conclude ¬strlen "Hello" 7.
You must know this concept, be able to state it clearly, be able
to see when you need it; and be able to use in to construct proofs
whether formal or informal. So here we go. (1) By the definition
of ¬, what we are really to prove is (strlen "Hello" 7) → False.
This is an implication. To prove it we will assume the premise is
true and that we have a proof of it (h : strlen "Hello" 7), and
we will then show that that can't happen (as revealed by the fact
that we'll have created a contradiction, showing that the initial
assumption was wrong).
-/
fun (h : strlen "Hello" 7) =>
/-
Now that we have our assumed proof of (strlen "Hello" 7) we have
to show that there's a contraction from which we can derive a
proof of False. The only information we have is the proof, h.
But how can we use it? The answer, for you, is that you again
want to see the need to expand a definition, here of the term,
(strlen "Hello" 7). What does that mean? *Go back and study the
definition of strlen!* It means (7 = "Hello".length), which is
to say, it means (7 = 5), as Lean will "run" the length function
to reduce "Hello".length to the result, 5. There can be no proof
of 7 = 5, because the only constructor of equality proofs, Eq.refl,
can only construct proofs that objects are equal to themselves.

Another way to say this is that we'll show that we can have a
proof of false for every possible proof, h, of 7 = 5; but there
are no, so showing that False is true in all cases is trivial,
as there is no case that can possibly account for h.
-/
  nomatch h

/-!
As a final example, we can prove that the pair, ("Hello",5), is
in strlen. In English, all we'd have to say is that this pair
satisfies the membership predicate because 5 = "Hello".length
(assuming we've properly defined "length,." which Lean has. )
-/

example : strlen "Hello" 5 :=
/-
By the definition of strlen, we must prove 5 = "Hello".length.
By the computation/reduction of "Hello".length this means 5 = 5.
And that is true by the reflecxivity of equality, as for any
value, k, whatsoever, we can have a proof of k = k by the rule
of equality introduction, Eq.refl k. The "rfl" construct we've
used in the past is just a shorthand for that, defined to infer
the value of k from context. And Lean takes care of reducing the
length function for us. We could write rfl here, but let's use
(Eq.refl 5) to get a better visual of the idea that what we're
producing here is a proof of 5 = 5.
-/
Eq.refl 5


/-
### A Finite String-Nat Relation

As our next example, suppose we want an even more restrictive
relation, one that could even be represented in the memory of
a very small computer. It'll be a small subrelation of strlen
that we'll call strlen3 with only three of the pairs in strlen.
In particular, we'll define strlen3 to be the relationing with
the set of pairs, { ("Hello", 5), ("Lean", 4), ("!", 1) }.

To specify this relation formally in Lean all we have to do
is to figure out how to write the membership predicate. In
this example, we'll do it as a three-clause disjunction, on
clause for each pair.
-/

def strlen3 : Rel String Nat :=
  fun s n =>
    (s = "Hello" ∧ n = 5) ∨
    (s = "Lean" ∧ n = 4) ∨
    (s = "!" ∧ n = 1)

/-!
We can prove memberships and non-membership of pairs in this
relation in the usual way: by proving the proposition that is
the result of applying the membership predicate to any pair of
values. But now that proposition will be a disjunction!
-/

example : strlen3 "Hello" 5 :=
  -- what we have to prove is the result of applying strlen3 to "Hello" and 5:
  -- ("Hello" = "Hello" ∧ 5 = 5) ∨ ("Hello" = "Lean" ∧ 5 = 4) ∨ ("Hello" = "!" ∧ 5 = 1)
  -- It's clear we can prove (and can only prove) the left disjunct; then it's two equalities
  Or.inl    -- prove the left disjunct ("Hello" = "Hello" ∧ 5 = 5), by left or introduction
    (
      And.intro   -- proof by and introduction
      rfl         -- "Hello" = "Hello"
      rfl         -- 5 = 5
    )

/-
We can also prove that ("Hello", 4) is not in the relation.
The proof is by negation: assume (strlen3 "Hello" 4), show that
that can't be, and conclude ¬(strlen3 "Hello" 4).
-/

example : ¬strlen3 "Hello" 4 := fun h =>
-- proof by case analysis on assumed proof h : (strlen3 "Hello" 4),
-- which is to say h is a proof of ("Hello" = "Hello" ∧ 4 = 5) ∨ ...
match h with
  -- Is ("Hello", 4) the first allow pair, ("Hello", 5)?
  | Or.inl (p1 : "Hello" = "Hello" ∧ 4 = 5) =>
      let f : 4 = 5 := p1.right
      nomatch f       -- nope, can't have a proof of 4 = 5
  -- case analysis on right side of disjunction
  | Or.inr (rest : "Hello" = "Lean" ∧ 4 = 4 ∨ "Hello" = "!" ∧ 4 = 1) =>
      match rest with
      -- Is ("Hello", 4) the second allowed pair, ("Lean", 4)?
      | Or.inl p2 =>
        let f : "Hello" = "Lean" := p2.left
        nomatch f       -- nope, can't have proof of "Hello" = "Lean"
        -- Is ("Hello", 4) the third and last allowed pair, ("!", 1)
      | Or.inr p3 =>
        let f : "Hello" = "!" := p3.left
        nomatch f         -- nope, can't haver a proof of "Hello" = "!"
/-
Having shown there can be no proof of strlen3 "Hello" 4,
we conclude ¬strlen3 "Hello" 4. QED.
-/


-- Lean's smart enough to do all that work for us
example : ¬strlen "Hello" 4 := fun h => nomatch h


/-!
## Fundamental Definitions

In this section, we define important terms and underlying
concepts in the theory of relations. To illustrate the ideas,
we'll refer back to our running examples.
-/

/-!
### The Domain of Definition and Co-Domain of a Binary Relation

Given any relation on sets (types) α and β, we will refer to
α as the *domain of definition*, and β as the *co-domain* of
the relation. The domain of definition is the set of possible
inputs and the co-domain is the set of all possible outputs.
For each the relations we've considered as examples so far
(completeStrNat, strlen, and strlen3) are the sets of *all*
the values of the types, String and Nat, respectively.

The domain of definition and the codomain of each of the relations
we've specified as examples are all values of type α = String and
all values of type β = Nat, respectively.


### The Domain of a Binary Relation

The set of values, (a : α), that r *does* relate to β values,
i.e., the set of values that do appear in the first position of
any ordered pair, (a : α, b : β) in r, is called the *domain*
of r. The domain of r is the set of values on which r is said
to be *defined*. It's the set of *input* values, (a : α), for
which r specifies at least one output value, (b : β).

More formally, given a relation, r : Rel α β, the domain of r is
defined to be the set { x : α | ∃ y : β, r x y }. Another way to
say this is that the domain of r is the set of α values specified
by the predicate, fun x => ∃ y, r x y. In other words, x : α is
in  the domain of r if any only if there's some y : β such that
the pair of values, x, y, satisfies the two-place predicate r.

In Lean, if r is a binary relation (Rel.dom r) is its domain set.
-/

#reduce Rel.dom r
-- fun x => ∃ y, x ≺ y (where ≺ is simply infix notation for r)

/-!
The domain of the completeStrNat relation is all of α. It's the
same for strlen. The domain of strlen3 is just the set of the
three strings in its definition: { "Hello", "Lean", "!"}. The
domain of the empty relation is ∅, the empty set.
-/

#reduce Rel.dom strlen
-- fun x => ∃ y, strlen x y
-- the set of x values for which there's some y value in strlen

#reduce Rel.dom emptyStrNat
-- fun x => ∃ y, emptyStrNat x y
-- equivalent to { x | ∃ y, emptyStrNat x y }
-- but ∃ y, emptyStrNat x y reduces to False
-- this can also be written as { x | ∃ y, False}
-- no x values satisfy False, so this set is empty

/-!
We can now prove, for example, that "Hello" ∈ strlen3.dom.
By the definition of the domain of a relation, we need to
show (∃ y, strlen3 "Hello" y). As a witness for y, 5 will do.
-/

example : "Hello" ∈ strlen3.dom :=
  -- Prove there is (exist) some y such that ("Hello", y) is in strlen3.
  -- A constructive proof requires a witness for y. Clearly y = 5 will work
  Exists.intro                    -- Apply the inference rule
    5                             -- to y = 5 as a witness
    (Or.inl (And.intro rfl rfl))  -- with a proof that ("Hello", y=5) in is strlen3




/-
### The Range of a Binary Relation
The range is similarly defined but for output
values. The range of a relation, r, is the set
of all values, (b : β), for which there's some
(a : α) that r relates to b. As an example, not
every possible social security number is assigned
to a person. The set of numbers that are assigned
by the *ssna* relation is the *range* of this
relation.

Sadly, the Lean library currently refers to the
range of a relation as its codomain. In reality,
these terms are used somewhat inconsistently. So
let's look at the definition of the *range* of r,
referred to as (Rel.codom r) or (r.codom) in Lean.
-/

#reduce Rel.codom r
-- Rel.codom r can also be written as r.codom
-- fun y => ∃ x, x ≺ y
-- equivalent to { (y : β) | ∃ (x : α), r x y }
-- y's in range if there's x in domain with r x y

#reduce strlen3.codom
-- fun y => ∃ x, strlen3 x y

-- Example: prove that 5 is in the codomain of strlen3
example : 5 ∈ strlen3.codom :=
-- what we need to prove is that ∃ x, strlen3 x 5
-- the proof is by exists introduction ...
Exists.intro
  -- ... with  "Hello" as a witness
  "Hello"
  -- ... and a proof that ("Hello", 5) is in strlen3
  (Or.inl (And.intro rfl rfl))

-- Exercise: Prove 6 is not in the codomain of strlen3

/-!
### The Inverse of a Binary Relation on Types/Sets α and β

The inverse of a relation, r, on α and β, is a relation on
β and α, comprising all the pair from r but with the first
and second element values swapped. Sometimes you'll see the
inverse of a binary relation, r, written as r⁻¹.

Lean can heal you learn these ideas. Let's ask it how it
defines the inverse of a an arbitrary binary relation, r.
Remeber we assumed above that r is some binary relation
from α to β.

Hover over the #reduce and see that the inverse of r is
the binary relation specified the two-argument predicate
fun b a => a ≺ b. This predicate is satisfied for (b, a)
exactly when (a, b) satisfies r (is in r). If it helps to
drop the concrete notation, it's fun b a => r a b. The two
notations mean the same thing.
-/

#reduce Rel.inv r
-- is defined to mean:      fun b a => r a b
-- is means the same thing: fun b a => a ≺ b
-- (b, a) satisfies r.inv when (a, b) satisfies r

/-
Example: What is the inverse of strlen3? In Lean it's writen
either (Rel.inv strlen3) or just strlen.inv. Remeber, This is
a predicate being used to represent a relation. The inverse
of r is a new predicate. If r takes areguments, a of types α,
and then b of type β, then r.inv takes as arguments some
(b : β) and (a : α) and returns the proposition that (a, b)
is in r. If there's a proof of that, then (b, a) is specified
to be in r.inv. To so prove that some (b, a) is in r⁻¹, you
just show that (a, b) ∈ r.
-/

/-!
Conjecture: (5, "Hello") is in the inverse of strlen3.
Proof: it suffices to prove ("Hello", 5) is in r. But
we've already done that once and don need to do it again
here! Oh, well, ok.
-/

example : strlen3.inv 5 "Hello"
  :=
  /-
    By the definition of the inverse of a relation,
    the proposition, (strlen3.inv 5 "Hello"), which
    we are to prove, reduces to (strlen3 "Hello" 5).
    By the definition of strlen3, this proposition
    tne reduces to ("Hello" = "Hello" ∧ 5 = 5) ∨ ...
    This proposition is now proved by or introduction
    on the left.
  -/
  Or.inl ⟨ rfl, rfl⟩
-- Remember ⟨ _, _ ⟩ here is shorthand for And.intro

/-!
We can actually now state and prove more general theorems
showing that the inverse operation has the property that
appying it twice is equivalent to doing nothing at all.
Think about it: if (a, b) is in r, then (b, a) is in the
inverse of r, but now (a, b) must be in the inverse  of
this inverse of r. Going the other way, if (a, b) is in
the inverse of the inverse of r, then (b, a) must be in
the inverse of r, in whcih case (a, b) must be in r. In
other words, (a, b) is in r if and only if (a, b) is in
the inverse of the inverse of r. We want to know that this
statement is true for *any* values of a and b (of their
respective types).
-/

theorem inverseInverseIsId: ∀ a b, r a b ↔ r.inv.inv a b :=
-- assume a and b are arbitrary values (by ∀ introduction)
fun a b =>
-- prove r a b ↔ r.inv.inv a b
-- by iff intro on proofs of the two implications
Iff.intro
  -- prove r a b → r.inv.inv a b
  (
    -- assume h : r a b
    -- show r.inv.inv a b
    -- but h already proves it
    -- because r.inv.inv is r
    fun h : r a b => h
  )
  (
    -- assume h : r.inv.inv a b
    -- show r a b
    -- but h already proves it
    -- because r is r.inv.inv
    fun h : r a b => h
  )

/-!
### The Image of a Set Under a Binary Relation

Suppose we have a binary relation, (r : Rel α β),
and a set of α values, (s : Set α). The image of s
under r is the set of values that, in a sense, you
get by iterating over all the elements of s, getting
one element, e, at a time, then finding all the the
"output" values in r for that one "input" value and
finally combinining all of these output into  output
set. We don't write that as a program, though, but
as a mathematical specification.
-/

#reduce Rel.image
-- fun r s y => ∃ x ∈ s, r x y
/-!
This predicate specifies what is meant by the inverse
of a binary relation. In particular, given a relation,
r, a set of input values, s, and an output value, y,
y is specified to be in the image of r when there is
some input value, x, in s, that r relates to y as an
output. In other words, the image of s under r is the
set of all output values for any and all ainput values
in s.  This makes r like some kind of super-function.
You apply it to multiple arguments at once (the values
in s) and you back the set all output values that r
relates to any value, x, in s.
-/

#reduce Rel.image
-- fun r s y => ∃ x ∈ s, r x y
/-!
Given any relation, r, and any set of input values,
s, an output value y is (defined to be) in "the image
of s under r" exactly when y is the output of r for
at least one (some) value x in the set s. The image
operator on a relation acts like it's applying the
whole relation to a whole set of values and getting
back all values related to any value in the argument
set.
-/

/-
#### Example: What's in strlen3.image { "Hello", "!"}

In this example we'll consider the image of the set
{ "Hello", "!"} under the strlen3 relation. You can
see intuitively that it's the set {5, 1}, insofar as
strlen3 relates "Hello" to (only) 5, and "!" to only
1, so those are *all of the possible output values of
strlen3 for any input value in { "Hello", "!". Let's
start by reducing
-/

#reduce Rel.image strlen3 { "Hello", "!"}
-- Here's an easier way to write the same thing
#reduce strlen3.image {"Hello", "!"}
-- fun y => ∃ x ∈ {"Hello", "!"}, strlen3 x y

/-!
Look at that specification: The image of this set under
strlen3 is the set, specified by this *single-argument*
predicate, of all output (β) values, y, such that, for
any given y there is some x in s that r relates to y.
-/

/-!
Given this definition and our understanding, we see that
it should be possible to show that, say, 1, is in the
image of { "Hello", "!"} under strlen3, because there is
a string in the set,  { "Hello", "!"}, namely "!", that
r relates to 1 (for which (strlen3 "!" 1) is true).
-/

example : 1 ∈ strlen3.image { "Hello", "!"} :=
/-
By the definition of Rel.image we need to prove
is that there is some string, x, in the set, call
it s, of strings, that satisfies strlen3 s 1. This
string, in s, will of course be "!", so that will
be our witness. The proof is by exits introduction
with "!" as the witness.
-/
Exists.intro "!"
(
  -- what remains to be proved is "!" ∈ {"Hello", "!"} ∧ strlen3 "!" 1
  -- the proof is by and introduction
  And.intro

     -- prove: "!" ∈ {"Hello", "!"}
     -- this is obvious but, sorry, maybe I'll prove it later
    (sorry)

    -- prove: strlen3 "!" 1
    -- this is obvious but, sorry, maybe I'll prove it later
    (sorry)
)

/-
We should also be able to show that 4 is not in the image of
s under strlen3. The proof is by negation. We'll assume that
4 is in the image, but we have already figured out that the
only elements in there are 5 and 1 (from "Hello" and "!"). The
problem will be that assuming 4 is in the set isto assume that
4 = 5 ∨ 4 = 1. That's a contraction as each case leads to an
impossibiility. Thus 4 ∉ strlen3.image { "Hello", "!"}. QED,
-/

example : 4 ∉ strlen3.image { "Hello", "!"}  :=
-- assume, h, that 4 is in this set
fun h =>
  -- From 4 ∈ strlen3.image {"Hello", "!"}, prove False
  -- By the definition of image, h proves ∃ s, strlen3 s 4
  -- The only information we have to work with is h
  -- And the only thing we can do with it is elimination
  Exists.elim
    h
    -- ∀ (a : String), a ∈ {"Hello", "!"} ∧ strlen3 a 4 → False
    -- we assumed r relates some string in s to 4 call it w
    (
      fun w =>
        (
          -- prove: w ∈ {"Hello", "!"} ∧ strlen3 w 4 → False
          -- assume premise : w ∈ {"Hello", "!"} ∧ strlen3 w 4
          fun p =>
          (
            let l := p.left
            let r := p.right

            -- recognize that w proves a disjunction
            -- eliminate using Or.elim via pattern matching
            -- case analysis
            match l with
            -- left case, with "hello" a proof of w = "Hello" (in this case)
            -- we also have r, a proof of (strlen3 w 4)
            -- we can use "hello" to rewrite (strlen3 w 4) to (strlen3 "Hello" 4)
            -- by the definition of strlen3 this is a disjuncion that is false
            -- using
            | Or.inl hello =>
              /-
                We haven't talked about "tactic mode" in Lean. Without getting
                into details, we're arging that because "hello" proves w = "Hello",
                we can replace w in r, which proves strlen3 w 4, to get a proof
                of strlen3 "Hello" 4. But the pair, ("Hello", 4), is not in the
                strlen3 relation, as that pair of arguments doesn't satisfy the
                constraint it imposes on membership. The nomatch construct does
                a case analysis on this rewritten version of r and finding that
                there are no ways it could be true, dismisses this overall case.
              -/
              (
                by
                  rw [hello] at r
                  nomatch r
              )

            -- the second case, w ∈ { "!" } requires deducing from that that w = "!"
            -- that then allows us to rewrite (strlen3 w 4) to (strlen3 "!" 4)
            -- by the definition of strlen3, that'd mean, inter alia, that 1 = 4
            | Or.inr excl  =>
              (
                have wexcl : w = "!" := excl
                (
                  by
                    rw [wexcl] at r
                    nomatch r
                )
              )
          )
        )
    )
/-!
In each case, where s = "Hello" or where s = "!", we have a
contradiction: that s.length (either 5 or 1) is equal to 4.
In each case we're able to derive a contradiction, showing
that the assumption that 4 ∈ strlen3.image {"Hello", "!"} is
wrong, therefore ¬4 ∈ strlen3.image {"Hello", "!"} is true.
QED.
-/

/-
#### Example: What Are Mary's Bank Account Numbers?

Let's make up a new example. We want to create
a little "relational database" with one relation,
a binary relation, that associates each person
(ok their name as a string) with his or her bank
account numbers.

There's no limit on the number of bank accounts
any single person can have. To be concrete, let's
assume there are three people, "Mary," "Lu," and
"Bob", that Mary has accounts #1 and #2, that Lu
has account #3, and that Bob has no bank account.

We can think of the relation (call it acctsOf) as
the set of pairs, { Mary, 1), (Mary, 2), (Lu, 3) }.
The thing to see here is that the image of { Mary }
under acctsOf is not a single value but a set of
values: {1, 2}.
-/

def acctsOf : Rel String Nat := fun s n =>
s = "Mary" ∧ n = 1 ∨
s = "Mary" ∧ n = 2 ∨
s = "Lu"   ∧ n = 3

/-!
Let's remind ourselves how the image of the set,
{ "Mary" } under the acctsOf relation is defined.
As usual, hover over "#reduce" to see its output.
-/
#reduce acctsOf.image { "Mary" }

/-!
acctsOf.image {"Mary"} is the set specified by this
predicate: fun y => ∃ x ∈ {"Mary"}, acctsOf x y. In
English, y is in the image if there's some x in the
set of inputs ({ "Mary" }), such that (acctsOf x y)
is satisfied.
-/

-- Proof that 1 is in acctsOf.image { "Mary" }
example : 1 ∈ acctsOf.image { "Mary" } :=
/-
By the definition of image, we need to prove
∃ x ∈ {"Mary"}, acctsOf x y. At this point, we
have to find/pick a witness---here an input value
in the set, { "Mary"} )--- for which 1 is among
the outputs. Then we just prove that that pair
is in fact in the relation.

The proof is by exists introduction. We show
that there is some x in { "Mary" } *and* for
that x, (x, 1) is in acctsOf. The only possible
x to choose in this case is "Mary".
-/

  -- Pick "Mary" as the witness
  (Exists.intro "Mary"
    -- now prove "Mary" ∈ { "Mary" } ∧ acctsOf "Mary" 1
    -- the proof if of course by and introduction
    (And.intro
      -- Exercise: prove "Mary" ∈ { "Mary" }
      (_)
      -- Exercise: prove (acctsOf "Mary" 1)
      (_)
    )
  )

-- Exercise: Prove that 2 is also in the image of { "Mary"}
example : 2 ∈ acctsOf.image { "Mary" } := _

-- Exercise: Prove that 3 is not one of Mary's bank accounts
-- HERE:

/-!
#### Example: The Unit Circle is a Multi-Valued Relation

What we see in this example is that, in general, a relation,
unlike a function, does not have to be "single-valued". Many
important relations are not single-valued. For example, take
the binary relation on ℝ (the real numbers), x² + y² = 1. It
is multi-valued, with several output values for at least some
of its inputs.

This is the relation satisfied by all real number pairs that
fall on the unit circle centered on the Cartesian plane. By
basic algebra, you can also write it as y² = 1 - x². In any

In any case, if you pick an x value, such as 0, there are two
corresponding y values that satisfy the relation. Plugging in
0 for x, we have y² = 1 - 0 = 1. And there are values of y
that satisfy this predicate: y = -1, and y = 1. We can thus
claim that the image of { 0 } under y² = 1 - x² (which you
can now think of as a predicate satisfied only by certain
x-y pairs) is the set, { -1, 1 }. For at least some values
of x, this relation thus has multiple (two) output values.
-/

def unitCircle : Rel ℝ ℝ := fun x y => x^2 + y^2 = 1

/-!
We might expect unitCircle 0 (-1) to reduce to
0^2 + (-1)^ = 1, but it doesn't. The problem is
that there is no *computable function* that can
decide whether or not two real numbers are equal!
In fact, in general, one can't compute with real
numbers at all.
-/
#reduce unitCircle 0 (-1)
--

/-
For the same reason you can't use Eq.refl (rfl).
There is even in theory no computable function that
can decide whether two real numbers are equal.
-/
example : unitCircle 0 (-1) := rfl

/-!
But we know it's true so there must be a way to
prove it! You have to use additional definitions,
axioms, and so on. The actual proof construction
is beyond the scope of this course. *Fortunately*
Lean comes with a tactic (one of many) called
simp that, given a set of definitions, will to try
to *simplify* (and if it can, prove) a goal, all
without you having to lift a finger.

A tactic is not "Lean code" per se, but a program,
written in Lean, that automates finding and applying
a set of definitions to simplify a goal so that you
don't have to do it all yourself.

Here then is a demonstration that there is a formal
proof that (0, -1) is on the unit circle. You must
understand that simp (and tactics more generally)
automatically write proof code for you. You don't see
the actual "proof object" here, but you can see that
the Lean prover has accepted it, so you can rest easy
knowing that the proposition that (0, -1) is on the
unit circle.
-/
example : unitCircle 0 (-1) :=
  by
    simp [unitCircle]

/-!
The translation of this tactic-built proof into
English then is easy. We say, *by the definition of
unitCircle*, the proposition to be proved is that
0^2 + (-1)^2 = 1], which is clearly true (and to
remove all doubt, Lean's simp tactic proved it).
-/

/-!
For those interested in futher study, Lean has a
ton of options you can set to have it tell you more
or less information as it goes. The following option
tells Lean to tell you what facts the simp tactic, in
particular, used in trying to produce a proof for you.
Don't worry about the details, just be happy you did
not have to assemble that proof on your own!
-/
set_option tactic.simp.trace true in
-- hover over simp to see all the definitions it used
example : unitCircle 0 (-1) :=
  by
    simp [unitCircle]


/-!
Now that we have the tools we need to prove propositions
about membership in the unitCircle relation, we should be
all set to prove propositions about membership in the image
of a given set of input values under the unitCircle relation.

We can see that if the input values are {x = 0, x = 1} that
the corresponding set of output values should be {-1, 1, 0}.
If you don't see that, you need to review basic algebra and
confirm that (0, -1), (0, 1), and (1, 0) are points on the
unit circle.

Here's the expression for the image set (of output values)
for the set of input values, { 0, 1}. Hovering over #reduce
gives you the predicate that defines the output/image set.
-/
#reduce unitCircle.image { 0, 1 }
-- fun y => ∃ x ∈ {0, 1}, unitCircle x y


/-!
So now we're set: Let's prove that -1 is in the image
of { 0, 1 } under the unitCircle relation. Here's the
claim/proposition, followed by the proof. As usual, you
cannot just read this proof. Use Lean to interact with
it, to understand the reasoning at each step, what is
left to prove after each step, and how the whole thing
really does (firmly in your mind) prove that one of the
outputs given inputs 0 and 1 is in fact -1.
-/

example : -1 ∈ unitCircle.image { 0, 1 } :=
/-
By the definition of image, what we have to show is
that ∃ x ∈ { 0, 1 } such that (x, -1) is in the image.
The proof is thus by exists introduction, and we have
to pick a witness that will make the remaining proof
go through. The only value that x/input value in that
set that will work is 0.
-/
Exists.intro
  -- witness
  0
  -- proof
  ( -- need to prove (0 ∈ {0, 1}) ∧ (unitCircle 0 (-1))

    -- by and introduction
    And.intro
    -- prove: (0 ∈ {0, 1})
    -- { 0, 1 } is represented by the predicate fun n => n = 0 ∨ n = 1
    -- applying fun n => n = 0 ∨ n = 1 to n = 0 is 0 = 0 ∨ 0 = 1
    -- the proof is by left introduction of a proof of 0 = 0
    (
      Or.inl rfl
    )
    -- now what remains to be proved is that
    (
    -- prove: unitCircle 0 (-1)
    -- i.e., 0^2 + (-1)^1 = 1
    -- Eq.refl/rfl will *not* work; we can't compute with reals
    -- rather we'll ask Lean to help simplify the goal
    -- which it does, to the point that there's nothing left to prove
        by simp [unitCircle]
    )
  )
