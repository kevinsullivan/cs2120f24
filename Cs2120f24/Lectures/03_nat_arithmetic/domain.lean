namespace cs2120f24.natArithmetic

/-!
# Domain: natural number arithmetic

## The Nat Type

Everyone's familar with natural number arithmetic in the abstract.

It comprises:

- the set of natural numbers (whole numbers from zero up)
- operations taking and returning natural numbers (such as increment and add)
- predicate functions taking natural numbers and returning Booleans (e.g., "n less than m")
- *induction*: for defining functions that answer correctly for infinities of cases!


Induction emerges as a major theme. How do you define a type with an infinite
number of terms, *which is what's needed if those terms are to represent the
natural numbers (all of them). How do you define a function that can given a
different answer for each of an infinite number of natural number arguments?
The answer in both cases is induction, or inductive definitions: these are
definitions of types of things, where bigger things are derived from smallers
ones of the same type, and where answers for bigger arguments are derived from
answers for smaller arguments.

We use Lean's definition of the Nat type.

Using it, we go on to define a small library of
basic arithmetic operators (addition, subtraction,
etc.) and predicate functions (less than or equal,
isEq0, and so on).

Our dive into natural number arithmetic, and the
language we use to work with it, provides you with
a second major example of a discrete structure: the
natural numbers and its associated operators (both
arithemtic and relational).

The central new idea in this exploration, beyond
what we saw in propositional logic, is a solution
to representing types of objects where there are
infinitely many of them. There is an infinity of
natural numbers (mathematical ideal abstraction).
We thus need a type with an infinity of values to
*represent* and infinity of natural numbers, then
we need a way to *finitely* specify functions that
can provide correct answers for an infinite number
of possible argument values. It cannot be by just
enumerating all the answers. There are too many.


Rather, it's by building answers for larger inputs
from answers from smaller inputs, starting from a
*smallest* (base) value and a given answer for it.
That's induction. It's akin to filling in a table
from previous entries, starting from given initial
ones, until you reach the answer you want. The very
cool thing about induction is that it relies on an
axiom that asserts that its valid to conclude that
you can return an answer for any input if you have
two smaller capabilities: to return an answer for
the base case, and, given any n' and an answer for
n' (from the just previous entry in the table), to
return an answer for n = (n' + 1). The axiom says
that you can jump from these two parts to the whole
function that you need.

It starts with the inductive definition of the set
of Nat terms, which we want to correspond exactly with
the natural numbers. Our representation is basically
*unary:* start with zero then put as many "succ" marks
in front of it as the number you want to represent. So,
for example, Nat.succ (Nat.succ Nat.Zero) represents 2.

inductive Nat : Type
| zero : Nat
| succ (n' : Nat) : Nat
-/

/-!
## Operations

Next we look at unary and binary operations. We represent
the mathematical abstractions as functions in Lean that
both consume (take as argments) and construct and return
values of type Nat.
-/

/-!
### Unary Operations-/

-- identity function; two different ways to write it in Lean
def id : Nat → Nat
| n => n

-- fyi: you can move arguments *before* the : and bind names there
def id' (n : Nat) : Nat := n    -- the name n is bound, so can be used

-- increment (add one) function
def inc : Nat → Nat
| n => n + 1       -- n + 1 is notation that "desugars" to "Nat.succ n"

-- again moving argument before colon; very same function
def inc' (n : Nat) := n + 1

-- predecessor function
-- if argument, call it n, is 0, return 0,
-- otherwise match n as (n' + 1) and return n'
def pred : Nat → Nat
| 0 => 0        -- Nat.zero
| n' + 1 => n'  -- Nat.succ n'

-- decrement (just another name for predcessor)
def dec : Nat → Nat := pred

-- factorial
-- cases define *base* and *step* values; induction takes care of the rest
def fac : Nat → Nat
| 0 => 1
| (n' + 1) => (n' + 1) * fac n'


/-!
### Binary Operations

The preceding operations were unary, each taking one natural
number. The following definitions specify the standar binary
arithmetic operations. Key ideas: (1) in general you need to
pattern match on both arguments to distinguish key subsets of
combinations of values to distinguish.
-/

def add : Nat → Nat → Nat           -- case analysis on m only
| n, 0 => n                         -- m = 0
| n, (m' + 1) => (add n m') + 1     -- m = (m' + 1)


def sub : Nat → Nat → Nat           -- case analysis on n and m
| 0, _ => 0                         -- 0 on left is 0
| n, 0 => n                         -- 0 on right is n
| (n' + 1), (m' + 1) => sub n' m'   -- else return answer for n' m'

def mul : Nat → Nat → Nat           -- case analysis on second arg m
| _, 0 => 0                         -- if it's zero, answer is zero (we want to specify multiplication!)
| n, (m' + 1) => add n (mul n m')   -- otherwise add n to answer for n and m' = m - 1

def exp : Nat → Nat → Nat           -- you figure it out
| _, 0 => 1
| n, (m' + 1) => n * exp n m'

/-!
## Relations via Predicate Functions

### Unary Relations

The idea of a unary relation is a bit odd, but it makes
sense if you think of it as a defined by a function from
*one* value (unary) of a give type to Bool. A function of
this kind could, for example, tell you whether any given
argument is even, or prime, or a perfect square. You can
pick the *property* of natural numbers you want. You can
then often *specify* it as a predicate function, one that
returns a Boolean yes/no answer, just as we're doing here.
-/

-- An interesting unary property is "n is equal to zero."
-- As a predicate function: give it n; it answers yes/no.

def isEq0 : Nat → Bool    -- by case analysis on n
| 0 => true               -- true for 0
| _ => false              -- false otherwise


-- what predicate does this predicate function "decide"?
def poof : Nat → Bool
| 0 => true
| 1 => false
| n'' + 2 => poof n''

-- Haha: is n *even*, does n have the property of being even?
def isEven : Nat → Bool := poof


/-!
### Binary Relations

Carefully study the case analysis and compare it with
that for the equality relation (eq).
-/

def le : Nat → Nat → Bool
| 0, _ => true
| (_ + 1), 0 => false
| (n' + 1), (m' + 1) => le n' m'

def gt : Nat → Nat → Bool
| n, m => !le n m


-- Study the case analysis and compare with le
def eq : Nat → Nat → Bool
| 0, 0 => true
| 0, (_ + 1) => false
| (_ + 1), 0 => false
| (n'+1), (m'+1) => eq n' m'

def lt : Nat → Nat → Bool
| n, m => le n m && !(eq n m)

def ge : Nat → Nat → Bool
| n, m => gt n m || eq n m

end cs2120f24.natArithmetic

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

-- We're back to using Lean's definitions

/-!
Lean provides all of the usual arithmetic operations.
In abstract syntax, they're Nat.add (the add function
defined in the Nat namespace), Nat.mul, Nat.sub, etc.
Lean also provides standard notations for all of the
usual arithmetic operators
-/
#eval 4 + 5 * 6   -- evaluated as 4 + (5 * 6) due to precedence

#check Nat.add 4 5 * 6

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
