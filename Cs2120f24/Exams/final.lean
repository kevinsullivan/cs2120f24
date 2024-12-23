-- import Mathlib.Data.Set.Basic
--import Mathlib.Logic.Relation
-- import Mathlib.Data.Rel

/-
*************************
#1. [30 points] Induction
**************************

The notion of a *sequence* of values is fundamental
in mathematics as well as in computer science. This
question tests your ability to use the ideas you've
learned in this class, particular about induction on
natural numbers, to understand and work with an idea
you haven't yet seen explicitly: using the induction
axiom not for Nat values but for Lists to construct
functions that can take any list and return the right
result.

Throughout the presentation of this question we will
remind you, and ask you to solve, a few problem like
the ones you've already seen for Nat-valued arguments.
We'll then intersperse questions about applying nearly
the same ideas but when the input values are lists. So
let's get started with some reminders about lists and
the construction of functions on lists *by induction*.

Here's the definition of the Nat type:

inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat
-/

#check Nat

/-
Now here's the definition of the polymorphic List
type in Lean. You haven't studied it yet but you
should be able to see that it's very similar to Nat.


inductive List (α : Type u) where
  | nil : List α
  | cons (head : α) (tail : List α) : List α

Like the Nat type, it has two constructors. The
first, nil, defines the least value, here for the
empty list. It is directly analogous to Nat.zero.
The second constructor cons, takes both a value,
h, of the list element type and an existing list,
t, and returns a new list starting with h and then
continuing with t as the rest of the new list.

There are of coures differences between Nat and
List. First, List takes a type argument, making
List a polymorphic type builder. This argument
specifies the type of elements in a list of the
given List kind. So, for example, (List Nat) is
the type of lists of Nat values; List Bool, the
type of lists of Boolean values; etc.

Second, whereas the Nat.succ constructor takes
just a smaller Nat, call it n', as an argument,
and returns (Nat.succ n'), thus representing the
natural number (n' + 1), by contrast, the cons
contructor takes two arguments, a value (h : α),
and a smaller list, t, and returns the list,
l = (List.cons h t), representing the one-larger
list with (a : α) as the first value in the new
list, followed by t as the rest of the new list.

Finally, Lean provides concrete notions to make
it nicer to work with lists. `[]` represents the
empty list. Second, if `h : α` and `t : List α`,
then `h :: t` desugars to `List.cons h t`. Be
sure you see that h is of type α and t is of type
List α.

Here are some examples of lists constructed with
these notations.
-/

-- empty list of Nat
#check (List.nil : List Nat)
#check ([] : List Nat)

-- A list of Nat containing just one element, 3.
#check 3::List.nil
#check 3::[]

-- A list of Nat containing elements 0, 1, 2, 3
#check 0::1::2::3::List.nil

/-
The third concrete syntax notation Lean provides
is the usual one for lists. The empty list is [],
the singleton list is [3], and the four-element
with natural number elements from 1 to 4 is written
as [1, 2, 3, 4].
-/

#check [1, 2, 3, 4]

/-!
Now suppose one wants to be able to use *any* list,
value, given as an argument to a function, to compute
some desired result (maybe whether the list is empty
or not, or its length, or the sum of the numbers in
it, or whatever).

As we've seen, the trick is to define a computation
that returns the right answer for each possible form
of the argument list. For List values, that means you
need to provide one solution for List.nil and for the
inductive case, where the input list is of the form,
(List.cons h t). Here are examples of a simple function
that takes and list and returns true if it's empty and
false otherwise (corresponding to the construct that
was used to produce the input list value).
-/

def isNil {α : Type} : List α → Bool
| List.nil => true
| List.cons a l' => false

#eval isNil ([] : List Nat)
#eval isNil [1,2,3]

/-
In this case the output value depends only on the
List constructor, and not the actual values of the
arguments to cons. We can thus elide their names.
-/

example {α : Type} : List α → Bool
| List.nil => true
| List.cons _ _ => false


/-
# A [5 points]

Define a function, count, using this same notation,
that takes as an argument, (l : List Nat), and returns
a count (Nat) of the number of elements in the list.
-/



/-
# B [5 points (2 extra credit points possible)]

Define a function, prod, using this same notation, that
takes, as an argument, a list, (l : List Nat), and returns
the product (times) of all of the elements in the list. For
this problem you must provide test cases for both empty and
non-empty lists of natural numbers. You can use #reduce and
add a comment documenting the expected answer, or (for two
extra credit points), use example and Eq.refl.
-/



/-
# C [10 points]

Underlying these kinds of function definition
are induction axioms, one for each inductively
defined type.

You've already seen how to use the induction axiom
for Nat (Nat.rec). Now you're asked to apply use this
knowledge to define a function, sumSquares, that given
*any* list of natural numbers computes the sum of the
squares of the numbers in the list. Here, however, you
must define your function *by induction*, that is, by
applying the Nat.rec induction axiom to definitions of
answers for the base (n = Nat.zero) and inductive
(n = n' + 1) cases.
-/


#check Nat.rec

/-
Nat.rec.{u}
  {motive : Nat → Sort u}
  (zero : motive Nat.zero)
  (succ :
    (n : Nat) →
    motive n →
    motive n.succ
  )
  (t : Nat) : motive t
-/

-- You fill in both definitions here
def prodBase : Nat := _
def stepBase (n' ansn') := _

/-
This term defines the desired function (will you've done
your work). Note: we do give the ordinarily implicit first
argument explicitly (by name). Lean needs to be told what
is the type of the function being constructed.
-/

#check (Nat.rec (motive := (λ (_ : Nat) => Nat)) prodBase stepBase)

-- this term applies it to 5 and is expected to reduces to 55
#eval (Nat.rec (motive := (λ (_ : Nat) => Nat)) prodBase stepBase) 5



/-
# D [10 points]

The final part of this question asks you to apply
the principles you've learned to define two total
functions on lists by applying the List induction
axiom. It's related to but different than Nat.rec.
-/

/-
First, define a function that takes any list and
returns the count of its elements *by induction*,
which is to say, by application of the induction
axiom, List.rec, for Lists instead of Nats. We'll
give you help around Lean syntax. You just fill in
the critical bits, as above.
-/

#check List.rec

/-
List.rec.{u_1, u}
  {α : Type u}
  {motive : List α → Sort u_1}
  (nil : motive [])
  (cons :
    (head : α) →
    (tail : List α) →
    motive tail →
    motive (head :: tail))
  (t : List α) : motive t

-/


-- YOU FILL IN YOUR PARTS HERE

-- num elements in []
def listCountBase : Nat := _

-- num elements in h::t given t and num elements in t
def listCountStep (a : α) (t : List α) (anst : Nat) : Nat := _

-- Check that the type of the total function is correct
#check List.rec (motive := (λ (_ : List _) => Nat)) listCountBase listCountStep

-- Test the resulting total function
#reduce (List.rec (motive := (λ (_ : List _) => Nat)) listCountBase listCountStep) [1,2,3,4,5]
-- Expect 5. It will work when you've got your parts right


/-
E. is for Extra Credit [5 points].

The List.append function takes two List α arguments,
let's call them l1 and l2. It returns the new list with
the elements of l1 followed by the elements of l2. You
can find its definition in the Library by right click
then go to definition. Lean provides the notation ++
for List.append. Here's its definition is for reference.
-/

#check List.append
/-
def append : (xs ys : List α) → List α
  | [],    bs => bs
  | a::as, bs => a :: List.append as bs

protected def append : (xs ys : List α) → List α
  | [],    bs => bs
  | a::as, bs => a :: List.append as bs
-/

-- examples
#reduce List.append [0,1,2] [3,4,5]
#reduce [0,1,2] ++ [3,4,5]

/-
For credit on this question you must define your
own implementation of list append by applyging the
induction principle, List.rec, for Lists to base and
inductive case arguments: the answer when l1 is nil
is just l2; and the answer when l1 = h::t, given the
assumptions you're allowed to make in this inductive
case is up to you to specify. So, define a symbol,
appBase, giving the answer for the base case, then
define appStep giving the step function need to make
the inductive definition work as required.
-/




/-
*******************
#2 [30 points] Sets
*******************
-/


/-
2A. [10 points] Set operators

We first define a few sets to use in this problem.
-/

def a : Set Nat := { n : Nat | n = 1 ∨ n = 2 ∨ n = 3 }
def b : Set Nat := { n : Nat | n%2 = 0}
def c : Set Nat := { 0, 1 }

/-
Fill in the sets needed to answer the questions
as posed *using display notation*. That means you
have to explicitly list the values in the set, as
specified in the precending comments. Replace the
empty set answers, {}, with the right answers. Be
clear that Lean is just checking your syntax, not
whether your answer is right. There are no proofs
involved here.

[Corrections: Replace the given answers with your own.
You need not list more than eight elements of any set.]
-/

-- a ∩ b
def interab : Set Nat := {1}

-- a \ b
def diffab : Set Nat := {1}

-- a × c
def prodac : Set (Nat × Nat) := {(3,1)}

-- 𝒫 c
def powc : Set (Set Nat) := {{},{1},{2},{1,2}}

-- 𝒫 (a × c)

def powac : Set (Set (Nat × Nat)) :=
  {
  }


/-
2B. [10 points] Relational operators on sets
-/

/-!
Answer these question in plain precise English.
Each question assumes you have two sets, call them
s1 and s2, each having elements of some type, α.

First, in plain English, express the precise logical
condition must be satisfied to conclude that (a ⊊ b),
i.e., that a is a proper subset of b. Emphasis here
is on *proper* subset.

HERE:

Next give a formal specification in Lean of the
predicate that defines the subset relation. You
are just writing the formal specification of what
it means for s1 to be a proper subset of s2. You
are not asked to prove anything for this question.
-/

def mySubsetNotEq (α : Type) (s1 s2 : Set α) : Prop :=
  _


/-
2C. [5 points].

Give a formal proof of the proposition that c ⊆ a (subset,
not proper subset). Use "example" so that we don't have to
bind a name to the proof. If you're unable to prove it in
Lean, for partial credit, give an English proof, but be sure
it includes all of the reasoning you'd have in a formal proof.
-/

example : c ⊆ a := _


/-
2D. [5 points]

Formally prove the propositions that 2 ∉ c. If you can't
do it in Lean, give the proof in English. The same rules
for partial credit applies here as in the previous problen.
-/

example : 2 ∉ c :=
  (
    _
  )



/-
*******************************
#3 [30 points] Binary Relations
*******************************


A. [10 points]

There are just four functions from Nat → Nat. You can
think of each one as a binary relation. For example, the
not relation takes any Bool and returns the other Bool;
so the relation can be understood as the set of pairs,
{ (true, false), (false, true) }. We can give names to
each relation:

idf := { (true, true), (false, false) }
fls := { (true, false), (false, false) }
tru := { (true, true), (false, true) }
not := { (true, false), (false, true)}

Which of these functions has whcih of the following
properties? List the answers after the colons. To get
credit for each part you must list all and only those
functions with the specified properties.

- injective: _

- surjective: _

- bijective: _

-/

/-
Define a binary relation from Bool to Bool that
is not a function. Give the set of pairs that are
in the relation by filling in the pairs between
the \{ and the \} as follows:

Here: notFun := { ... }.
-/



/-
B. [15 points] Formal proof of single valuedness.

We say that a function is singleValued if no single input
has more than one output. Here's a formal definition.
-/

def isSingleValued {α : Type} : (Rel α α) → Prop :=
fun (r : Rel α α) => ∀ (a b c: α), r a b → r a c → b = c

/-
Now here's a definition of not as a relation.
-/

def neg : Rel Bool Bool := fun x y =>
  (x = true ∧ y = false) ∨ (x = false ∧ y = true)

/-
Your job is to prove that neg is singleValued.
An English proof would typically start with "By the
definition of single valued it will suffice to prove,"
and then you'd state the *logical* proposition that
has to be proved. Provide a proof of that proposition
to fill in the blank. If you can't do it in Lean, give
a detailed proof in English for partial credit. Hint:
Proof by nested case analysis on disjunctions. Next
hint: Some cases are impossible, so look to dismiss
them based on contradictions. If you can get much
of the way through a formal proof but aren't sure
quite how to finish it off, use sorry and add a
text comment below explaining the rest of that
part of the proof informally.

Important hint here: Use CMD/CTRL-SHIFT-ENTER to
open Lean's InfoView panel. Then you can click at
various points in the proof construction to see the
proof state at each point in its develoment.
-/

example : isSingleValued neg :=
-- assume the premises are true and we have proofs
(fun a b c hab hac =>

  -- now it's nested case analysis on the disjunctions
  match hab with

  -- first outer case: a = true ∧ b = false
  | Or.inl atbf =>

    -- first nested case: a = true ∧ c = false
    match hac with
    | Or.inl atcf =>
        let bf := atbf.right
        let cf := atcf.right
        by
          _
    -- second next case: a = false ∧ c = true
    | Or.inr afct =>
      let bt := atbf.left
      let af := afct.left
      by
        rw [bt] at af
        _

  -- second outer case: a = false ∧ b = true
  | Or.inr afbt =>
    -- first inner case: a = true ∧ c = false
    match hac with
    | Or.inl atcf =>
      let xa := afbt.left
      _

    -- second inner case: a = false ∧ c = true
    | Or.inr afct =>
       _
)

/-
C. [5 points]

Given a concise English language proof of the
preceding proposition: that the Boolean negation
function is injective. Model it on the proof you
gave for the preceding problem. It could start
with "By the definition of ..." and then "There
are 4 cases to consider ..." then go through each
case. You do not need to be verbose. Just give a
mathenatucally precise argument mirroring that in
the formal proof. For full credit you do have to
explain the reasoning in each case correctly.
-/



/-
*********************************
#4. [10 points] Proof by negation
*********************************

Two reasoning principles are often confused:
proof by negation, and proof by contradiction.

Proof by negation is used to prove a proposition
of the form, ¬P. By the definition of ¬P as P → False,
you do that by assuming that P is true (and in Lean that
means you have a proof of it, (h : P)), and by showing
that that assumption leads to a contradiction. The
axiom of negation introduction then allows you to
conclude ¬P.

Formally, a proof of ¬P, then, is a function
that that takes an assumed a proof (h : P) as
an argument, and, in that context, derives a
contradiction.

Give a formal proof of the proposition that
0 ≠ 1. Hint: remember that that means ¬0=1;
and what does that mean?
-/

def not0eq1 : 0 ≠ 1 :=
(
  _
)

/-/
Now if you're given a proof of a negation,
such as a proof, (h : ¬P), what can you
do with it? Show that you know what to do
with such a proof by proving the follwing
proposition.
-/

example (P : Prop): P → ¬P → False :=
_


/-
EXTRA CREDIT [5 points]:

Let P be the proposition that there is no smallest
real number. Give an English language proof *by
contradiction* of this proposition. That means you
must assume ¬P, derive a contradiction, conlude P.

Step 1 is to assumpe ¬P. Give an English-language
expression of the proposition, ¬P.

Here:


Step 2 is to derive a contradiction enabling
you to conclude that P is true. Explain how
you will arrive at a contradiction.
-/
