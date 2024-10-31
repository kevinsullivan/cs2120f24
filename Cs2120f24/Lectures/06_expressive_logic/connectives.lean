/-!
# Logical Connectives

In the last two classes, we've seen that we can
represent:

- propositions as types
- proofs as values of such as types
- the ∧, ∨, ↔ (and later ∃) connectives as parameterized (polymorphic) types
- the introduction rules for ∧, ∨, ↔ (and later ∃) as the constructors of such types
- the introduction rule for → (and later ∀) as function definition
- elimination rules as functions that use proof arguments to construct new proofs

We've already seen all of this in our extended case study of "And". Given two
types, P and Q, representing propositions, (And P Q) is a new type representing
the propositions P ∧ Q. The and_intro inference rule is represented as the single
contructor, And.intro, of this new type. It requires both a proof (p : P) and a
proof (q : Q) as its arguments. In other words, we define the constructor to
precisely mirror the inference rule/axiom, P → Q → P ∧ Q. The key idea now is
that have (or assume you will be given) a proof (p : P) and a proof (q : Q) then
you can construct a proof of P ∧ Q, as (And.intro p q). Note that this term can
be written using the concrete notation, ⟨ p, q ⟩. This notation makes it clear
that a proof of a conjunction is essentially a pair of proofs, here p and q.

Now suppose you have or assume a proof of P ∧ Q, call it h = ⟨ p, q ⟩. Now the
elimination rules for And (P ∧ Q → P, and P ∧ Q → Q) are simply the "projection"
("getter") functions that return the first and second proofs enclosed in in h.
Notations include h.1 or h.left, for P ∧ Q → P, and h.2 or h.right for P ∧ Q → Q.

With all that as background, our purpose now is to use these ideas to "map" all
of the axioms of propositional logic into the framework of propositions as types.
We've already done this for the three axioms for and, as just described. Now we
turn to mapping the rest of our axioms into the "type theory" of Lean in the same
way.

So as to be able to illustrate, let's assume (using Lean's "axiom" keyword) that
we already have two propositions, P and Q; that we have proofs of each of them,
(p : P) and (q : Q); and that we have a third proposition, R, defined explicitly
here as having no proofs at all.
-/

-- Propositions
axiom P : Prop              -- assume P is some proposition
axiom Q : Prop              -- assume Q is some proposition
inductive R : Prop where    -- define R as a proposition with no proofs

-- Proofs
axiom p : P                 -- assume p is proof of P
axiom q : Q                 -- assume q is a proof of Q

/-!
## And
-/

/-!
### ∧ Is Represented as a Polymorphic Proposition (Type) Builder

Here are the axioms for ∧ from our work on PL:

- and_intro := R ⇒ Q ⇒ R ∧ Q
- and_elim_left := R ∧ Q ⇒ R
- and_elim_right := R ∧ Q ⇒ Q

The mapping of these axioms into Lean is as follows:

- The ∧ connective maps to a polymorphic type, And α β
- the intro rule maps to the intro constructor of this type
- the elimination rules map to getter/projection function

We'll now take each of these aspects in turn.
-/


/-!
#### The Syntactic ∧ Connective is Represented as a Polymorphic Type Builder

The ∧ connective is represented in the type theory of Lean
as a polmorphic type builder: And, with two two propositions
(types) as arguments. Applying And to two propositions, P, Q,
thus yields another proposition, namely P ∧ Q. The type of And
is thus Prop → Prop → Prop.
-/
#check (And)
#check (And P Q)

/-!
### The "Intro" Axiom is Represented as a Constructor

And now for the inference rules. The constructor, And.intro, has
the type, ∀ {a b : Prop}, a → b → a ∧ b. The additional arguments
(a, b) compared with the rule in propositional logic, says, "given
any two types, a and b, representing propositions, And.intro applied
to a proof, (p : a), and a proof, (q : b), yields a proof of a ∧ b.
-/

#check (@And.intro)
#check (And.intro p q)


/-!
### The "Elimination" Rules are Represented as Getter Functions
-/

#check (@And.left)
#check (@And.right)
#check (And.intro p q).left
#check (And.intro p q).right



/-!
## Or

Here are the axioms for Or from our study of PL.

- or_intro_left := R ⇒ R ∨ Q
- or_intro_right :=  Q ⇒ R ∨ Q
- or_elim := Q ∨ R ⇒ (Q ⇒ P) ⇒ (R ⇒ P) ⇒ P

And here's how Lean defines Or

inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b


### The Syntactic Or Connective is Represented as a Polymorphic Type Builder

Exactly the same narrative as for And applies to the Or connective.
First, it's represented as a polymorphic proposition/type builder.
Second, the introduction rules are represented as the constructors of such a type.
Finally, the elimination rule is represented by a function.
-/

-- The type of the Or proposition builder
#check (Or)
#check (Or P Q)

/-!
### The "Intro" Axioms are Represented as Constructor-/

#check (@Or.inl)
#check (@Or.inr)
#check (Or.inl p : P ∨ Q)
#check (Or.inr q : P ∨ Q)

/-!
### The Or Elimination Rule
-/

#check (@Or.elim)

/-!
"If we know that at least one of a and b is true, and if we know that
whenever a is true so is c, and if we know that whenever b is true then
so is c, then we can conclude that c must be true."

"If we have a proof of a ∨ b, and if we also have a proof of a → c, and
if in addition to that we have a proof that b → c, then we an construct
a proof of c."

Note: The curly braces in the type of Or tell Lean to figure out the
values of the two type arguments from the remaining arguments, so that
you as the "programmer" don't have to provide them explicitly. Lean is
said to do "type inference" in this case.
-/
#check (@Or.elim)

/-!
## Equivalence

The ↔ connective is also defined analogously in Lean. Recall that in
plain English, if you have a proof of P → Q, and you also have a proof
of Q → P, then you can deduce P ↔ Q. And if you have a proof of P ↔ Q,
then from it you can derive proofs of, respectively, P → Q and Q → P.
We see that ↔ is defined almost identically to ∧, except now the two
smaller proofs that are needed are specifically proofs of implications,
namely of P → Q and Q → P.

structure Iff (a b : Prop) : Prop where
  intro ::
  mp : a → b
  mpr : b → a
-/

/-!
### The Polynorphic ↔ Proposition/Type Builder

The Iff proposition/type (builder), with two proposition arguments
-/
#check (@Iff)

/-!
### The ↔ Intro Inference Rule
-/
#check (@Iff.intro)

/-!
### The ↔ Elim Rules

The elimination rules are just the two "projection" (getter) functions.
Their names are abbreviations for "modus ponens (for Iff)" and "modus
ponens reversed (for Iff)." The name "modus ponens" comes from Aristotle!
-/
#check (@Iff.mp)    -- if we know a ↔ b and we know a then we know b
#check (@Iff.mpr)   -- if we know a ↔ b and we know b then we know a


/-!
### ⊤

The "always true" proposition, ⊤, in PL is realized in type theory as
the propositional type called *True* This type has one constructor that
takes no arguments at all. So there is always a proof of True, making
it unconditionally true.
-/

/-!
### The Proposition, True

True is a proposition that always has a proof and so is
always true.

inductive True : Prop where
  | intro : True
-/

#check True

/-!
### The Introduction Rules

True.intro is the name of the single proof of True in Lean, If ever
you need a proof of true, just write True.intro. It is rare, almost
never, that you actually need to have a proof of true. Nothing can
be deduced from it, so it's not much use. It's trivial.
-/

#check True.intro

/-
### The Elimination Rule

Because nothing else can be derived from a proof of True, there is
no useful elimination rule for this proposition.
-/

/-!
## False

In Type theory (in Lean), ⊥ (the proposition that is simply false)
is represented by the type called False. If this type had any values,
each would serve as a proof, showing False to be true. To make False
represent logical falsehood, it's defined as a type with no values at
all, thus no constructors.

inductive False : Prop

That's it!
-/

#check False

/-!
### Introduction Rule

As just explained, False is defined as a type with no constructors at
all, making it a proposition that *has no proofs at all*. There is no
introduction rule for False, either in propositional logic or in type
theory.
-/

/-!
### Elimination Rule for False

Please take a moment to revisit our axioms for propositional logic.
The rule can be read as asserting that if false is true then anything
is true (⊥ → P). Once again, this already familiar rule maps directly
into type theory.
-/

#check (@False.elim)

/-!
Let's look at this rule, in Lean, in more detail.

{C : Sort u_1} → False → C

In English it says that "if C is any type (whether a computational
type in Type or a propositional type in Prop -- that's what Sort u_1
basically means), and then if you have a proof of False, then you can
promise to return a value/proof of C. Why? Because you can never have
a proof of False, so you'll never get to the point where you actually
have to construct a value/proof of C.

Here's another way to look at it. To define a function from False to
C, we need to define how to construct a result of type C for each and
every possible proof of False; but there are none, so we don't have
to define any conversions from False to C at all. With no cases to
consider, we can say that False implies C *in all cases, of which
there are none to consider!

All  this gets back to the basic idea that "False implies anything."
One will also heard it said that "from False anything follows." Or,
if you really want to be cool, say it in Latin: Ex falso quodlibet.

In Lean, the term "nomatch f" is used to express the idea that there
are no cases to consider, so all cases have already been considered
(all zero of them, that is), so the definition is finished.

Let's first see this notion working to prove at from a proof of
false we can derive a value of a computational type, such as Nat.
-/

def false_imp_nat : False → Nat
| f => nomatch f

/-!
Not that we didn't have to return any Nat all all. We're required
to return a Nat value for each case of f, but there are no cases,
so we're done. Exactly the same idea applies when the conclusion is
a proposition (represented as a type in Prop.)
-/

def false_imp_any_prop : False → P
| f => nomatch f

/-!
### Connecting Back to Propositional Logic
And now to fully explain the correspondence between what we saw in
propositional logic, let's see in type theory (in Lean) how we get
the same facts for implications involving True and False.
-/

-- True → True is valid
example : True → True
| t => t                  --given a proof of true, we can have a proof of true

-- True → False is not valid
example : True → False
| t => _                  -- there is simply no proof of False to return

-- False → True is valid
example : False → True
| _ => True.intro         -- We can just ignore a proof of false and return a proof of True

-- Another proof of False → True is valid
example : False → True
| f => nomatch f          -- Or we can do a case analysis on f and with no cases be done

-- Finally False → False is valid
example : False → False
| f => f                  -- If we assume we're given a proof of False we can just return it


/-!
Note that each of the preceding cases is a proof of an implication.
Just be sure to recall that it type theory we give such a proof as
a function, taking a value/proof of the "antecedent" type (left of
the →) and returning a proof/value of the "conclusion" type (right).
We thus just proved four implications in type theory that we already
know and love from propositional logic.
-/


/-!
## Implication

In type theory, we don't give a proof of an implication as a data
structure (that is, as a value of an inductive type); rather a proof
of a logical implication, P → Q, as a function, imp : P → Q. You see
here as clearly as could be the correspondence between logical types
and computational types, but now they are function, not data, types.
-/

/-!
### Introduction Rule

As stated, a proof of P → Q is given as a function. In English, we'd
say, "If whenever we have a proof of P we can derive a proof of Q then
we can conclude that P → Q." That's all there is to it. Another way to
say this is that if we have a function that when given any proof of P
can construct and return a proof of Q, that shows that if P is true
(as demonstrated by having a proof of it) then Q must be true (because
from that proof of P we can derive a proof of Q).
-/

/-!
### Elimination Rule

The elimination rule is what Aristotle called modus ponens. If we
have a value/proof (pf : P → Q, where pf is now a function that takes
any P value/proof and returns a Q value/proof), and if we also have a
of proof P, then a proof of Q can be constructed, showing Q to be true.
That proves P → Q. Note that it is not always possible to define a
function that *can* construct a proof of Q from a proof of P. Where
it's not possible, we'd judge P → Q to be false.

Now recall from above that we've assumed we have propositions P and Q.
Let's in addition now assume that we have a proof, (pimpq : P → Q). It
is a function. The elimination rule is *function application*. Given
this proof, and given that we already assumed a proof of P, (p : P),
all we have to do is apply pimpq to p to get a proof of Q.
-/

axiom pimpq : P → Q   -- Suppose we have a proof of P → Q
#check (pimpq p)      -- We can *apply* it to (p : Q) to get a proof of Q

/-!
### Summary

To construct a proof of an implication, P → Q, show (by constructing one
and having Lean accept it as correct) that there's a proof of P → Q. In
other words, show that there's *some* value (a function implementation, as
it were) of the type, P → Q. If there's demonstrably no function/proof of
P → Q, then P → Q is false. And to *use* a proof of P → Q, just apply it
to a proof/value of (type) P to derive/return a proof/value of (type) Q.
Yay!
-/

/-!
## Not

Now please remind yourselves of our PL axioms for negation (¬). In PL the
introduction rule states (P → ⊥) → ¬P. We saw in PL that if P → ⊥ is true
then P *must be* false, as that's the only value of P that makes (P → ⊥)
true; and in this case ¬P, where P is false, ¬P must be true. The definition
of Not (¬) in Lean is analogous: the proposition, ¬P, is simply defined to
be the proposition, (P → False).
-/

/-
### Introduction Rule for Not (¬)
Given all that, we can see that to prove ¬P one simply proves P → False, an
implication. And you already know how to prove implications. As an example,
consider our proposition, R. We defined it as having no proofs at all. With
no proofs at all, it's false. As R is false, we'd expect ¬P to be true, which
is to say, we'd expect there to be a proof of ¬P. That in turn would be a
proof of P → False, as we just explained.

The key idea is that ¬R is true, which is to say that R → False is true, if
and only if there are no proofs of R. To prove the implication we have to
define a function from R to False. To do that we need to return a value of
false for each possible case/form of R. But if there are no values of R at
all, then doing nothing proves them all, in which case R → False is proved.
On the other hand, if R has one or more proofs, then there can be no function
from R to False, since given such a value/proof of R, a function proving
R → False would have to return a value of False *for that value of R*, and
that's not possible. The upshot is that R → False if and only if, like the
False proposition itself, R has no proof values.
-/

def pfNotR : R → False
| r => nomatch r      -- nomatch says there are no cases of r to consider

/-!
So from now on if you're asked to prove ¬R, just assume that what you're
being asked to prove is R → False.
-/

def pfNotR2 : ¬R      -- understand that ¬R is *defined* to be R → False.
| r => nomatch r      -- there can be no proof/value of R: no cases to consider; done


/-!
### Elimination Rule for ¬

So now we've seen that a proof, (pfNotR : ¬R) is really just a proof of R → False;
that is an implication; so a proof of ¬R will be proof of this implication; and that
in turn will be in the form of a function from R to False (of type R → False). The
elimination rule is thus exactly the same as for any proof of an implication: just
*apply* it to the right arguments to get a desired result.
-/

#check pfNotR

/-!
Let's see the elimination rule in action. We'll define a function that will *assume*
it's given a proof (r : R) as an argument and that promises to return a proof of false
for each possible form/case of r. Of course there are none, so once again we can just
dismiss the whole exercise using nomatch.
-/

def badfun' : R → False
| r => nomatch r

def badfun : ¬R
| r => nomatch r

/-!
Yay. Given that we defined R to be an uninhabited propositional type, we know there
can be no proofs of R. So if we assume we're given one, there are not cases to deal
with. That makes it very easy to return a proof of false *in each case*, since there
are none. So there's nothing left to do, and the function definition is accepted. It
is the existence of function from R to False that proves that R is false (because it
has no proofs). On the other hand, we've assumed we have a proof of P, so we could
never hope to prove ¬P. What happens if we try?
-/

def notPFalse' : ¬P           -- we will attempt to prove ¬P (but P has a proof)
| pfP => _                    -- We cannot possibly return a proof of false here

def notPFalse : P → False     -- again, just expanding the definition of ¬P
| pfP => nomatch pf           -- nomatch doesn't work because P is not empty!



-- We see yet again that a true proposition can never imply a false one

/-!
## Examples

### And (∧)
-/

/-!
#### Introduction
-/

/-!
Here we apply And.intro to construct proofs of P ∧ Q.
In each case it's by applying the proof/value constructor,
And.intro to arguments, p and q, of types P and Q, respectively.
The first example binds a name to the resulting proof so we can
use it later. The second example checks the proof but doesn't
give it a name. The third example presents concrete notation,
defined in Lean's libraries, for And.intro _ _
-/
def pandq : P ∧ Q := And.intro p q
example   : P ∧ Q := And.intro p q
example   : P ∧ Q := ⟨ p, q ⟩


/-!
#### Elimination

From a proof, pandq, of P ∧ Q, we can derive proofs of P and
of Q, respectively. We do this by destructuring a given proof,
such as pandq. There's only one constructor, but destructuring
let's us get at the two smaller proofs from which any such term
must have been constructed. It's especially easy to apply the
elimination rules because (1) there's one constructor, And.intro,
(2) the type is defined using the "structure" keywords, and (3)
as a result of that, we can use the names of the fields, given
in the definition of And, to retrieve that arguments that were
given to And.intro when the value was constructed.
-/
example : P := pandq.left
example : Q := pandq.right
example : P := pandq.1
example : Q := pandq.2




/-!
### Or (∨)

#### Introduction

A proof of P ∨ Q can be constructed from a proof (p : P) or
from a proof (q : Q), for which we have the two constructors,
Or.inl and Or.inr.
-/

def porqFromP : P ∨ Q := Or.inl p
def porqFromQ : P ∨ Q := Or.inr q

/-!
Elimination
-/

#check (@Or.elim)

/-
The check shows the type of Or.elim.  It's a function of this type:
∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c. It says that if a,
b, and c are any propositions, then if you have a proof, (h : a ∨ b),
then if we also have proofs, (ac : a → c), and (bc : b → c), then in
either case of h (one carryiny a proof of a, and the other a proof of
b) we can construct a proof of c, by applying either ac or bc to the
proof of a in the first case and b in the second case. This will show
that if you have *any* proof of a ∨ b along with proofs of ac and bc,
then you can derive a proof of c.

To see this rule in actions, let's just assume, without being specific,
that we do have have proofs of ac : a → c and bc : b → c. They will be
in the form of functions, as we've seen several times now. Because we've
already defined R to be an empty type, we'll introduce one more type, S,
to illustrate these ideas.
-/

axiom S : Prop
axiom ps : P → S
axiom qs : Q → S


#check (Or.elim porqFromP ps qs)
-- This term, (Or.elim porqFromP ps qs), serves as a proof of S!



/-!
### Implication in Lean (→)

#### Introduction

As we've explained, to prove the proposition, P → Q, in
type theory, one must show that there is (one must define)
a total function from P to Q. Such a function will take any
proof of P and convert it into and return a proof of Q. In
other words, if from any proof, (p : P), one can construct
a proof (q : Q), then one can conclude P → Q, and a function
of type P → Q will be the proof of it.

To make things a little more interesting, let's re-introduce
our natural number evenness predicate.
-/

inductive Ev : Nat → Prop
| ev0 : Ev 0                -- ev0 serves as aproof that zero is even
| evFromEv : (n : Nat) → (evn : Ev n) → (Ev (n + 2))

open Ev

def evZero  : Ev 0 := ev0
def evTwo   : Ev 2 := evFromEv 0 evZero
def evFour  : Ev 4 := evFromEv 2 evTwo

/-!
The first asserts that if any natural number, n, is even
then n+2 is even. The first argument to the function that
will prove this proposition is n. The second is a proof
that n is even. And in each case the return value is a
proof that, respectively, n+2, and n+4, are both even. A
cool observation is that you can't even apply evFromEv if
n isn't even because you'll never be able to construct a
value needed as the second argument (a proof n is even).
-/

def IfEvNThenEvNPlus2 : (n : Nat) → Ev n → Ev (n + 2)
| n, evn => evFromEv n evn

/-!
Learn to pronounce propositions and proofs in English.
Here, the proposition, (n : Nat) → Ev n → Ev (n + 2),
asserts that if n is any natural number, then if you
also have a proof that *that particular n* is even, then
(n+2) must be even. The next proposition just replaces 2
with 4. In both cases you must use evFromEv to construct
the desired proof from the given proof. In the first case
one application will do. In the second case, you have to
apply it once to get a proof that n+2 is even, then apply
it again using (that) proof as an argument to get a proof
that n+4 is even. That's the following example.
-/

def IfEvNThenEvNPlus4 : (n : Nat) → Ev n → Ev (n + 4)
| n, evn => evFromEv (n+2) (evFromEv n evn)

/-!
The bottom line is that you prove an implication, such as
P → Q, by showing, in the form of a function of type P → Q,
that there is a way to derive a proof of Q from any proof
of P.

#### Elimination

So how do you use a proof of P → Q, which in Lean is again
in the form of a function from P → Q? You just *apply* it
to a specific proof of P to a proof of Q. As an example, if
we apply IfEvNThenEvNPlus4 to, say, n = 4 and a proof that
that this n is even, it should construct and return a proof
that 8 is even.  Check it out!
-/

#check IfEvNThenEvNPlus4 4 evFour
-- This term is of type (is a proof of) Ev (4 + 4).


/-!
### Negation (¬)

Recall that at the top of this file we defined R to be a
proposition (type) with no proofs at all (no constructors
means no proofs, as the only proofs of a type are those that
can be constructed using one of the provided constructors).

#### Introduction

Given that R is a proposition with no proofs, we interpret
it as false, and should thus be able to prove that ¬R is true:
that there's a proof of it. Recall that ¬R is defined to be
the proposition R → False, where False is the standard empty
propositional type in Lean. Again the trick in proving ¬R is
to remember that it means R → False. That's an implication.
To prove it, we have to give a function showing that any proof
of R (recall there aren't any) can be turned into a proof of
False. In particular, all we need is one conversion rule for
each possible case of a proof of R. But there are zero cases,
so we don't have to do any more to have a proof of R → False,
which is to say, to have a proof of ¬R. Here we give such a
function using "fun" -- taking an argument *assumed* to be of
type R, with an *empty* set of cases, returning a proof of
false in each such case, of which there are none.
-/

def notR : ¬R := (fun (r : R) => nomatch r)

/-!
#### Elimination

Given that a proof of ¬R is in the form of a function from any
proof of R to a proof of False, we can derive a proof of False
(which is absurd) if we *assume* we're given a proof of R (also
absurd), because we then then apply our function from R to false
to that proof of R to get a proof of False.
-/

def noContra' : (notR : ¬R) → (r : R) → False
| nr, r => nr r

/-!
Another way to write the proposition that there can be no
contradiction is to state that P ∧ ¬P can never be true, so
it must be false, which is to say, ¬(P and ¬P). We leave the
proof as an exercise!
-/

example : ∀ (W : Prop), ¬(W ∧ ¬W) := _

/-!
It's very important that you understand this function. Given a
proof, nr, of ¬R, and a proof, r, of R, one can derive a proof
of False. That is of course absurd so it simply cannot be the
case that you can have both a proof of ¬R and a proof of R in
the same world. That'd be a contradiction within the logic and
that can't be allowed. The axioms of the logic are constructed
to assure that contractions cannot arise. If a contradiction
were possible, then there'd be a proof of False, False would
be proven to be true, and the entire logic would fall apart.
In technical terms, we'd say it'd be *inconsistent*.
-/
