/-! # Homework #5: Propositions as Types

In the last two classes, you've learned that we can represent
propositions as types, with any value of such a type, if there
is one, serving as a proof of the validity of the proposition.
-/

/-!
Using this idea requires nothing new in Lean that we haven't
been seeing for two months now. We will have to do two basic
things: (1) define types that we will think of as propositions,
(2) define functions that take values of these types, that we
will think of as proofs of their propositions, and that return
desired results, usually using the given proof as a value that
is destructured/eliminated to access its parts: the arguments
that were provided to the constructor that produced it.

The first challenge will test your readiness to define types
and functions in Lean without necessarily having anything to
do with logic.
-/

/-!
## #1 [40 points] Types and Functions (in Lean)

### A. [10 points]

Define a type called Kloo with constructors called Marv, Wond,
and Fab. A Kloo is a day on the planet Chkl. However, a week
on Chkl is only three days long. The constructor names of the
Kloo type are the names of these three days: Marv, Wond, Fabl.
Define this type in Lean.
-/

-- You solution here


/-!
### B. [10 points] A Unary Predicate Function

Now define a "predicate" function, isFabl, that takes a
Kloo value as an actual parameter and that returns a Boolean
value. In particular, it returns true if the value satisfies
the predicate, k = Fabl. In detail, (isFabl Marv) = false;
(isFabl Wond) = false; and (isFable Fabl) = true. That's all
you need. Define it The function now. The test cases below
will all pass when you've got it right.
-/

open Kloo

-- answer


/-!
Here (following) an "exhaustive" set of test cases,
"covering" all possible inputs. Try introducing a bug
into your function definition to see how these test
cases catch such bugs.
-/

example : isFabl Marv = false := rfl
example : isFabl Wond = false := rfl
example : isFabl Fabl = true := rfl

/-!
Each test cases uses Lean's "example" keyword. It's like
def but does not bind a name to a value. It's used to type
check a term (here "rfl") against its declared type. It's
a good choice when all you want to do is to test whether a
term is of its declared type, e.g., if a proof is correct.
Of course it can be used to check whether any value is of
a declared type.
-/

example : Nat := 1                  -- value typechecks
example : Nat := "Hello, Lean!"     -- does not typecheck

/-!
### A Note on Equality as a Binary Predicate
Here, each type is an equality proposition. Consider the
first example: isFabl Marv = false. On the left we have a
function application, returning a Bool. On the right is a
Bool. The equality symbol constructs a *proposition* that
asserts that the values on each side are equal. Finally,
"rfl" is an operation (we'll explain it in more details
later) that returns a proof of an equality proposition if
in fact the two sides are equal.

One upshot is that if you write your test cases like this,
rather than using #eval/#reduce, *you* don't have to decide
whether the actual returned value equals the expected one,
because Lean will tell you whether the proof attempt is
correct or not. Looking ahead, we'll see that Eq _ _ is a
two-place predicate, taking two arguments of the same type,
with a proof of the values are "definitionally equal" or
not. The = sign is just infix notation for Eq! The terms
being compared don't have to be exactly the same but they
do have to reduce to equal values. Thus "Eq (1 + 1) = 2"
has a proof (and so is valid), as (1 + 1) reduces to 2 and
then the terms on both sides of the = are in fact identical.
-/

example : 1 + 1 = 2 := rfl
example : "Hello, " ++ "Logic!" = "Hello, Logic!" := rfl

/-!
### C. [20 points] A Binary Function From Kloo to Kloo

Your final task on this problem is to define and test a
function, nextKloo, that takes a value of type Kloo and
uses it to compute and return the next Kloo. Remember, a
Kloo is like a day on Earth, so this function will take
a Kloo as an argument and return the next Kloo (like the
next day after the given one). The order like this: the
Kloo after Marv is Wond; the Kloo after Wond is Fabl; and
the Kloo after Fable is (back to) Marv.

First write the test cases, one for each Kloo value. Then,
in the space before the test cases, write the function so
that all the test cases pass. Note: a failure to pass could
be a bug in either the function definition or in the test
case itself. You must always keep this fact in mind when a
software test fails -- or we could say whever it *succeeds*
in revealing a bug. (The job of the developer is to get it
right; the job of the tester is to show that it's wrong.)
-/

-- function definition here

-- test cases here (write these first!)


/-!
## #2: Required Learning: Prop is the Type of Propositions

Over the last two classes, we've seen that we can represent
propositions as types, proofs as values of such types, and
logical connectives as "parametrically polymorphic" types,
where the type arguments are themselves types representing
smaller propositions.

### IsFromCville Example Continued

As a running example, we defined two propositions as types
(KIFC and CIFC), then defined *MyAnd* as a type builder (a
polymorphic type), with two propositions/types as arguments.
The constructors of such a type builder are shared by all
types defined by applying such a type builder to arguments.

We saw how the MyAnd.intro value/proof constructor of the
MyAnd type builder basically implements the and_intro axiom
from our earlier studies. To construct a proof/value of,
say, MyAnd P Q, you'd use MyAnd.intro p q, where (p : P)
and (q : Q).

Next we defined two *functions* to serve as implementations
of and_elim_left and and_elim_right. Each takes a value of
a (MyAnd P Q) type, destructures it using pattern matching,
and returns either the constituent proof of P or the proof
of Q.

Finally we defined a function, the existence of which we
views as a proof that (MyAnd KIFC CIFC) → (MyAnd CIFC KIFC).
In other words, we proved the implication that *if you have
or assume you have a proof of KIFC ∧ CIFC, then from it you
can derive a proof of CIFC ∧ KIFC (using ∧ as infix notation
for MyAnd).

In a nutshell, given that we have and_intro, and_elim_left,
and and_elim_right as *axioms*, we can use them to *prove*
that P ∧ Q → Q ∧ P, which is the forward direction of the
*identity* we saw in our study of propositional logic. To
prove this (or any) implication, we assume we have a proof,
let's call it pq, of P ∧ Q. We then applied left and right
elimination to obtain separate proofs, (p : P) and (q :Q).
Finally, we returned (and_intro q p) to these proofs, in
the reverse (q then p) order, to construct a proof (a value)
of the proposition (type), Q ∧ P, proving P ∧ Q → Q ∧ P.

If you're not yet confident you understand what we did in
this regard, please go back and read through all the notes,
and don't hesitate to experiment using Lean to see how it
all works.

### A Slightly Deeper Look at Types in Type Theory

Our next task is to show you the right way to represent
propositions as types in Lean. Before we get there, though,
we need to say a little more about types. Here's the idea.

Every term in Lean has a type. Types are terms, too. So even
types have types! You've already seen this. What is the type
of Nat? It's "Type". What is the type of Bool? It's "Type."
What is the type of "String"
-/

#check Nat
#check Bool
#check String
#check Empty

/-!
At this point, then we have a three-level hierarchy, with
data values at the bottom, being of data types in the middle,
and those all being of type, Type, at the top.
-/

--                         Type
--
--    Nat          Bool           String         Empty
--
--  0, 1, 2     true false      "Hi" "Bye"     [no values]


/-!
A critical aspect of *data* types, as we see them here,
is that we generally care (a lot!) about which values of
these types we are using and getting back from functions.
It's not equally good for the factorial function to return
or 120 or 122 as the value of (fac 10), for example.
-/

/-!
### Introducing Propositional/Logical Types

On the other hand, two different proofs of a proposition
are equally good at showing that it's valid. For purposes
of logical reasoning, we care only whether there is or is
not a proof, and *any* proof will serve equally well for
this purpose.

Furthermore, as we consider all proofs to be equally good
for showing validity, we really don't want the choice of a
proof to influence computations involving *data*. To this
end Lean gives us a second type universe, in addition to
Type, called Prop. From now on we'll use Prop as the type
of any type meant to represent a logical proposition. (You
may need to read that again.)
-/

/-!
Here's our Person *computational/data* type.
-/
inductive Person : Type
| Kevin
| Carter
| Muriel

open Person

/-!
One of the fundamental property of types "in" Type is that
values created by different constructors, and valued created
by a given constructor applied to different arguments, are
always unequal. The error message here says that the second
argument is expect to be equal to Kevin, but it's not, so a
proof of equality cannot be constructed.
-/

example : Kevin = Carter := rfl


/-
Here's our slightly modified new version of the isFromCville
predicate. Rather than taking a person as an argument and
yielding a computational type, in Type, it takes a person
as an argument and yields a logical/propositional, type, in
Prop. Otherwise the definition is exactly as we saw it before.
-/
inductive isFromCville : Person → Prop where    -- note "Prop"
| license (p : Person) : isFromCville p
| bill (p : Person) : isFromCville p
| birthcert (p : Person) : isFromCville p


/-!
Recall that a predicate is a proposition with parameters.
It's essentialy a function that you apply to arguments to
get a proposition. Here we apply our new predicate to the
arguments, Kevin, and Carter, resepectively, to derive two
different propositions. We did this in the previous example,
as well.
-/
def KIFC := isFromCville Kevin
def CIFC := isFromCville Carter

/-!
Whereas in the earlier presentation, we represented
these propositions as types in in the type universe, Type,
here we're represented them as propositions (types) in the
type universe, Prop. This is the conventional way to represent
propositions as types in type theory. They're types but not
they're not computational types. They are instead logical,
or propositional, types
-/
#check KIFC     -- the KIFC type has type Prop, not Type
#check CIFC     -- same goes for CIFC

/-!
The idea that proofs of propositions are represented as
values of types that represent them remains unchanged.
Compare these "proofs" with what we did before.
-/

def pfKIFC1 : KIFC := isFromCville.license Kevin
def pfKIFC2 : KIFC := isFromCville.birthcert Kevin
def pfCIFC : CIFC := isFromCville.license Carter

/-!
We have two "different" proofs that Kevin is from
CVille, and one proof that Carter is from Cville. We can
now confirm that different proofs of the same proposition
are not only "equally good" but, if represented as types
in Prop, are actually considered to be equal!
-/

example : pfKIFC1 = pfKIFC2 := rfl

/-
Such a check for equality would never work with two *data*
(as opposed to logical proof) values produced by different
constructors. For example, Bool.true and Bool.false are not
equal, and it'd be a logical catastrophe if they were!

Also note that we get a *type error* if we even try to write
the proposition that a proof that Kevin is from Cville is
equal to a proof that Carter is from Cville.
-/

example : pfKIFC1 = pfCIFC := rfl

/-!
Such proofs are of different types. They're proofs of different
*propositions*. And the Eq (=) predicate expects that the type of
its second argument will be the same as the type of the first.
Hover over the error and read and understand the error message.
-/

/-!
### Connectives for Propositions Represented as Types in Prop

Now we turn to the matter of logical connectives. We represented
MyAnd as a "polymorphic" type builder (taking two types in *Type*
as arguments). Review that development if you don't clearly recall
what we did. The great news is that Lean provides a full suite of
logical connectives *and standard concrete notations* for use in
writing propositions in Prop.

An ungraded task is that you must now compare Lean's definition
of the *And* (∧) connective with what we wrote in our warm-up to
these ideas (MyAnd). You'll find that they're basically identical
but for the fact that Lean's "And" expects two propositions as
arguments represented as types in Prop, not in Type. That's it.
-/

#print And

/-
If you right click on "And" and go it its definition, you will see
that it's essentially identical to our MyAnd type builder except that
is expects the two propositions to which it's applied to be represented
by types in Prop, not in Type.

The definition uses the "structure" keyword rather than inductive,
as there's only one constructor (intro) for And. And, as a new fact
for you, Lean automatically generates the elim functions for you, by
using the names of the fields (here "left" and "right") as the names
of functions that return the component proofs of a proof of (And P Q),
where, of course, P and Q are now propositions represented as types
in Prop, rather than in Type.
-/

/-!
With that, we can now re-prove our theorem asserting that
KIFC ∧ CIFC → CIFC ∧ KIFC. The logic is exactly as before.
We prove this implication by showing that there is a function
that takes any proof of KIFC ∧ CIFC and uses it to construct
a proof of CIFC ∧ KIFC.

Oh, and now that we're "in Prop", we can use all of the usual
logical notations we've learned for propositional logic. They
are just concrete notations for "abstract" syntax. Instead of
writing (And KIFC CIFC), for example, we'll write KIFC ∧ CIFC.
Furthermore, when we're asserting that there's a logical value
(a proof) of a given proposition, we can use "theorem" instead
of "def" to declare a name for the proof.
-/

theorem and_commutes : KIFC ∧ CIFC → CIFC ∧ KIFC
| And.intro k c => And.intro c k

/-!
That's it. The and_commutes function assumes that it's given a
proof of KIFC ∧ CIFC as an argument. It destructures it using
pattern matching to get its component values, namely a proof
of KIFC, k, and a proof of CIFC, c; and it then assembles these
values back into a proof of CIFC ∧ KIFC using And.intro. That
is the end of our introduction of Prop for use in representing
propositions as types.
-/

/-
## #2: Proof of Learning -- Or Is Commutative

This problem starts with a little exercise then asked you to
use the material you've learned to prove that logical "Or" is
commutative. That is, if P and Q are any two propositions, the
you are to prove that P ∨ Q → Q ∨ P.

### A. [20 points] Practice

Your first exercise returns to ordinary data types. Define a
polymorphic type builder, called Product, with two types, call
them α and β, as its arguments, and one constructor taking two
arguments, the first a value of type α and the second a value
of type β. Then define a function, call it swap, that takes a
value of type (Product Bool Nat), and returns a value of type
(Product Nat Bool), namely the *given* Bool-Nat pair but with
the order of the values swapped. Then write a test case using
Eq (=) to assert that the function works as expected on one
example. You can use whatever values of type Bool and Nat you
want in this example.
-/


/-!
### B. [20 points] Prove a Theorem

Finally, use everything you've learned here, using "theorem"
to assert that if you're given any two propositions, P and
Q, then P ∨ Q → Q ∨ P. Here's code to get your started. In
English it says that or_commutes will be a proof that if P
is a proposition (a value of type Prop) and then if Q is a
proposition, then if you have a proofvalue of type (P ∨ Q),
then from it you can derive a value of type (Q ∨ P).

This problem is a little harder than the corresponding proof
of commutative for And (∧), as the intro and elim rules for
∨ are a little trickier than those for and. Here are facts
you need to know. The introduction rules for (Or P Q) in Lean
are called Or.inl and Or.inr. The former takes a proof of the
left proposition (P), and the latter, of the right proposition
(Q). The strategy you should use is to do a case analysis on
the assumed proof of P ∨ Q. It must be either Or.inl applied
to a proof of P, or Or.inr applied to a proof of Q. Write two
cases that use pattern matching to distinguish which case the
argument to or_commutes falls into. Note also that you'll have
to have three arguments on the left of each =>: one for P, one
for Q, and one for the assumed proof of P ∨ Q. The third one is
where you'll distinguish the two different cases. Complete the
proof skeleton we give you here.
-/

theorem or_commutes: (P : Prop) → (Q : Prop) → (P ∨ Q) → (Q ∨ P)
| _, _, _ => _
| _, _, _ => _

/-!
### C. [20 points]

Finally, prove that Or is commutative. Construct two proofs
of KIFC ∨ CIFC, one from a proof of KIFC and one from a
proof of CIFC.. Call them pfL and pfR. Next, *apply* the
"or_commutes" theorem (it's represented as a function!) to
the required three argument values---two propositions (types)
P and Q, and a proof of the proposition, P ∨ Q. What you can
expect back is a proof of Q ∨ P! See the #check commands below
to confirm that the returned proof values are proofs of the
proposition, CIFC ∨ KIFC. What you've show
-/

-- answer: two proofs of KIFC ∨ CIFC
def pfL : _ := _
def pfR : _ := _

-- These check commands should be error-free when you've got it
#check (or_commutes KIFC CIFC pfL : CIFC ∨ KIFC)
#check (or_commutes KIFC CIFC pfR : CIFC ∨ KIFC)
