namespace cs2120f24.natArithmetic

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
## Constructors are for Constructing/Introducing New Values of a Type

The constructors of a type are its introduction rules. Each one define a set of
terms--those that be formed by applying the constructor to *any* values of its
argument types, that Lean is then instructed to then accept as being terms of
the type that the constructor belongs to.

The Nat type, for example, has two constructors. The first, Nat.zero, takes no
arguments and this defines a single constant term of type Nat. The seccond, the
Nat.succ constructor takes one argument, another terms of type Nat. If we call
that term, n', then the term, (Nat.succ n'), is accepted as also being a term of
type Nat. Note carefully that if a Nat value is not zero then it can only have
been constructed by Nat.succ applied to some smaller Nat.

- with these two constructors one can build Nat terms of any finite length, n
- we can represent any natural numnber n as a term of type nat with n Nat.succ applications to Nat.zero
- The set of terms of the Nat type is the set that can be "*finitely* generated" using these constructors
- Different constructors yield unequal terms (disjointness): zero is not the successor of any number
- Different constructor arguments yield unequal terms (injectivity): no n is the successor of different numbers
- Combined with the fundamental properties of inductive types we have terms that simulate natural numbers
- What we have technically speaking is a representation (Nat) of Peano Arithmetic, named after G. Peano
- As any Nat term is of finite size, recursions on smaller Nat values always terminate in finite "time"
-/

-- See examples in Main.lean
/-!
## How to Use Nats: Elimination by Case Analysis by Pattern Matching

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
## Arithmetic Operations

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

def fac : Nat → Nat
| 0 => 1
| (n' + 1) => (n' + 1) * fac n'


/-!
### Binary Operations
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
### Binary Relations (Boolean Predicate Functions)

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

end cs2120f24.natArithmetic

-- We're back to using Lean's definitions

-- operations
#eval 4 + 5 * 6   -- evaluated as 4 + (5 * 6) due to precedence
#eval 2^10        -- remember this forever: 2^10 is about 1000

-- relations
#eval 4 ≤ 5
#eval 5 ≤ 5
#eval 6 ≤ 5

/-
Now that we have the domain of natural number arithmetic set up,
it's time to turn to building a new *expression language* of our
own as a second example of a formal language with a syntax and an
operational semantics (an expression evaluation function). We'll
borrow hevily from our specification of the syntax and semantics
of propositinal logic. Instead of Boolean variables expressions,
we'll have natural number-valued variable expressions. Instead of
Boolean literals, we'll have Nat literal expressions. Instead of
syntactic expressions with ∧ and ∨ symbols, the operators will be
the likes of +, -, *.
-/
