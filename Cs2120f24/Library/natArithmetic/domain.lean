namespace cs2120f24.arith

/-!
# Domain: natural number arithmetic

Natural number arithmetic is deeply familiar to everyone here.
It comprises:

- the natural numbers (the set of whole numbers from zero up)
- operations taking and returning natural numbers
- certain new axioms, especially *induction*

We'll return to induction in a bit, but for now the plan is as
follows:

- The Nat type has terms/values that correspond to natural numbers
- We define functions that implement standard arithmetic operations
- We get a powerful new tool for building such functions: induction

We'll now address each of these issues in turn.
-/


/-!
## The Nat Type

Here's the entire mathematical definition of the natural numbers in
Lean.

inductive Nat : Type
| zero
| succ (n' : Nat)
-/

#check Nat    -- Nat is a Type
#print Nat    -- Here are its constructors

/-!
## Constructors are for Constructing, for Introducing, Values of a Type

The constructors of a type are its introduction rules. Each provides a way to
construct a new term of the given type by applying the constructor to argument
values of the specified types. Here there are only two constructors, and one of
them (succ) requires another as an argument. The only one we can have at first
then is Nat.zero. Call that 0. The only other thing you can do is apply succ to
that, yielding (succ 0). This term is *also of type Nat* so we can apply succ
again, to construct succ (succ 0); and so on essentially forever.

- with these two constructors one can build succ terms of any length, n; we represent n as the term of that length
- disjointness of constructors: Different constructors yield unequal values. zero is not the successor of any number.
- injectivity of constructors: Different arguments yield unequal values. no number is the success of distinct numbers.

- English: zero is a (term of type) Nat; and if n' is any Nat, then so is (succ n')
- With these two constructors one can build succ terms of any length, n
- we represent the natural number n as the term of type Nat of that length
- zero is not the successor of any number by "disjointness of constructors"
- no number is the successor of two distinct numbers by "injectivity of constructors"
-/

-- See examples in Main.lean
/-!
## Nat Eliminators: Case Analysis by Pattern Matching

The analysis distinguishes between Nat.zero and a term in which Nat.succ
was applied to an argument: in this case a one-smaller term of type Nat.
We could say that the two *cases* for the structure of a Nat supplied as
an argument are Nat.zero and (Nat.succ n'), where n' is name that we bind
temporarily to that one-smaller natural number.
-/

def isZero : Nat → Bool
| 0              => false
| (Nat.succ _)   => true

/-
Pattern matching in Lean let's us bind names to parts of a given term.
For example, is isZero is applied to n = 3, the first pattern match, with
Nat.zero, fails; but the second matches 3 as (Nat.succ 2). This function
requires a case analysis to distinguish zero from positive arguments but
it did not use n' in computing a result, so the name can be and has been
replaced here with an _.

This function can be said to be a predicate function: one that tells you
whether a given object has a given property or not (thus a Boolean result).
Here the function decides whether any given natural number has the property
of being zero or not.
-/

/-
Often it is necessary to bind names to elements within the terms being
analyzed as arguments. These names are like "getters" for fetching values
that have been packaged up by a constructor into a larger term.

The easiest example is the predecessor function. In our definition it
takes any natural number and, it it's zero, returns zero, and if it's
positive (the only other possibility), i.e., of the form (Nat.succ n'),
then return n' -- the natural number to which the Nat.succ constructor
was applied to get the argument term being analyzed.
-/

def pred : Nat → Nat
| 0 => 0        -- Nat.zero
| n' + 1 => n'  -- Nat.succ n'

/-!
But there's more. Pattern matching on constructor expressions
in Lean enables you to drill down into extract parts of complex
terms. You can figure it out. What does this function do/compute?
Describe it in natural language.= It takes a natural number n as
an argument and ...
-/

def poof : Nat → Bool
| 0 => true
| 1 => false
| n'' + 2 => poof n''


/-!
## More Arithmetic Operations

### Unary

With our two Nat constructors (zero and succ n') and the
ability to destructure any given Nat by pattern matching,
we can define a whole zoo of functions taking Nat values
as arguments.
-/

-- identity function, two ways
def id : Nat → Nat
| n => n
def id' (n : Nat) : Nat := n

-- increment (add one) function, two ways
def inc : Nat → Nat
| n => n + 1       -- Nat.succ n
def inc' (n : Nat) := n + 1

/-
The first two unary functions here, id (identity)
and inc (increment) do not need to *analyze* there
argument values. Id just returns the value it was
handed, while inc wraps the given value in another
layer of "succ" nesting. By contrast the predecessor
function, pred, does need to reach inside a non-zero
argument to get and return the argument wrapped up
in the constructor term as the predecessor. Note:
we "cheat" by returning 0 for argument 0, as there
is no actual predecessor of 0.
-/
-- decrement
def dec : Nat → Nat
| 0 => 0
| n' + 1 => n'

/-
In the increment function, n is a name that is
not bound. It matches any argument value, and we
use this identifier to write the expression for
the return value.

Now consider the dec function. In the first pattern
match, the constructor term, 0 matches only Nat.0. If
you think of the function as taking an argument, n,
this you can think of this line as saying "if n = 0
then return 0." The second line however destructures
the argument to dec (call is n) as (succ n'), and the
name, n', being unbound, matches any natural number
after the *succ* at the head of the term representing
the argument, n. The whole function can thus be read
as saying, if n = 0 return 0 else return n-1, which
is n with the leading "succ" removed.
-/

/-!
Now we turn to defining nore interesting and complex
operations involving natural numbers. The first will
be the unary *factorial* operator.

In English one might explain that the factorial of n
is the product of all the natural numbers from 1 to
n. But that leaves out the case where n is 0. It's a
bit of a muddle.

Let's turn around our entire perspective and ask how
would be answer the question, what's the factorial of
n. Instead we'll start by giving a literal answer for
the case where n is 0: namely, 0! = 1.
-/

def fac_base := 1

/-!
Now here comes the cool bit. *Suppose* (assume, dream)
that we know both a natural number value, n', and the
factorial of n'; can we then easily compute the value
of (n' + 1)! In other words, can you implement it?
-/

def fac_step (n' fac_n' : Nat): Nat := fac_n' * (n' + 1)
-- notice c-like notation, named arguments left of :

/-!
Now if we want the answer to the question, what is 5!,
for example, we can build it in steps. First use fac_base
to get 0! = 1, then apply fac_step as many times as needed
to get to n! for whatever n you've got. Each step creates
the result for fact n' that you need to feed to fac n'+ 1.
-/

def fac_0 := fac_base
def fac_1 := fac_step 0 fac_0
def fac_2 := fac_step 1 fac_1
def fac_3 := fac_step 2 fac_2
def fac_4 := fac_step 3 fac_3
def fac_5 := fac_step 4 fac_4
def fac_6 := fac_step 5 fac_5

#eval fac_5   -- expect 120

/-!
In each "step" you can assume you know n' and fac_n' and
are responsible for returning fac_n' * (n' + 1). In other
words, starting from the base and iterating the application
of step n times yields the value of the function for n.

You can see clearly that we can in principle construct the
value of n! for any n no matter how high in exactly the same
way. That said, we wouldn't want to have to write all that
code. We want a *single* function that does the right thing:
for any n, compute and return n!

The almost magical solution is the "induction function" for
natural numbers. In Lean its called Nat.rec. You come up with
the base and step function definitions. It the combines them
into the desired function for computing n! for any n, in effect
by starting with the base value then applying the step function
n times.
-/

def fac' : Nat → Nat :=
  Nat.rec fac_base fac_step


#eval fac' 5   -- whoa!

/-!
Lean provides nice for writing functions
in this way, essentially with a solution
for each "case" of the structure of the
argument *and* with the assumption the
function value for one less tha argument
is already know (or equivalently, and in
practice, it can be computed on demand.
-/
def fac : Nat → Nat
| 0 => 1
| (n' + 1) => (n' + 1) * fac n'


-- It works
#eval fac' 5   -- expect 120


/-!
Addition: by induction on the second argument
-/

def add : Nat → Nat → Nat
| n, 0 => n
| n, (m' + 1) => (add n m') + 1

/-
Detail: we define subtraction of any natural
number from 0 yielding 0. There are no negative
natural numbers. This is one reasonable solution.

Notice that on the first pattern matching line
in the following logic, the "m" is underlined in
yellow. That highlights  that we didn't have to
give that argument a name, as it's not used in
defining the return value for that case. The
warning can be suppressed by replacing the name
with an _.
-/
def sub : Nat → Nat → Nat
| 0, m => 0
| n, 0 => n
| (Nat.succ n'), (Nat.succ m') => sub n' m'

-- multiplication
def mul : Nat → Nat → Nat
| _, 0 => 0
-- n * (m + 1) => n + (n * m)
-- reduce multiplication to addition, already defined
| n, (Nat.succ m') => add n (mul n m')
-- effect is to iterate addition of n to zero m times

/-!
### Binary Relations (as Boolean Predicate Functions)

You're already familiar with binary relations such as
less than or equal to over the natural numbers. No one
will question that 7 ≤ 7
We implement predicate functions that return true
- unary: properties/sets
  - eq_0 n
  - even n
- binary; pairs (triples, etc)
  - eq n m      (true for all and only pairs where m and n are equal )
  - le n m      (true for all and only pairs where n ≤ m)
-/

-- does n have the property of being equal to zero?
def eq_zero : Nat → Bool
| Nat.zero => true
| _ => false

-- are n and m equal?
def eq : Nat → Nat → Bool
| 0, 0 => true
| (Nat.succ _), 0 => false
| 0, (Nat.succ _) => false
| Nat.succ n', Nat.succ m' => eq n' m'

-- is n ≤ m
def le : Nat → Nat → Bool
| 0, _ => true
| n, 0 => false
| (Nat.succ n'), (Nat.succ m') => le n' m'

/-
Now we can express the remaining inequality relations
in terms of the ones we've already got.
-/

def lt : Nat → Nat → Bool
| n, m => le n m && !eq n m

def gt : Nat → Nat → Bool
| n, m => !le n m

def ge : Nat → Nat → Bool
| n, m => gt n m || eq n m

/-!
## The Natural Numbers in Lean4

Lean provides a broad array of functions, standard notation,
and other mathematical-logic content for natural numbers when
they are represented as terns of type Nat.

We could continue to define our own notations and so forth,
but we're far better off just using the Nat type and all of
its associated machinery in Lean4. From now on, you can just
write arithmetic as you usually would and it'll all work as
you expect. Here are some basic expressions, using Lean4 and
its mathlib.
-/

#eval 4 + 5 * 6   -- evaluated as 4 + (5 * 6) due to precedence
#eval 2^10        -- remember this forever: 2^10 is about 1000
#eval 4 ≤ 5
#eval 5 ≤ 5
#eval 6 ≤ 5

/-@
Now that we have the domain of natural number arithmetic set up,
it's time to turn to building a new *expression language* of our
own as a second example of a formal language with a syntax and a
semantics, notions of models and counterexaples, and so on. And in
each of these areas, we'll see the same tricks we used when we
were formalizing propositional logic: variables, interpretations,
a syntax with literal, variable, and operator expressions
-/

end cs2120f24.arith
