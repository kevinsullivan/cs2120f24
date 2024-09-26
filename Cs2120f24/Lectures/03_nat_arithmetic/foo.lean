/-!
### Binary Relations (Boolean Predicate Functions)

It's often useful to think of a unary
relations as specifying properties of values; and so we
have functions that take Nat-valued arguments and tell
you whether or not a given natural number is even ("has
the property of being even", or, equivalently, "is in
the set of the even natural numbers"). What is the magic
ingredient that lets this function to compute the answer
for *any* natural number? Induction, of course.

Here there are *two* starting, or base, constant values,
and one step function that, however, steps up from a given
n'' and answer for n'' and gives you an answer (indeed the
same answer) for n''+2. If you iterate it n times, with 0
as a starting point, you get the answer, true, for n * 2,
again, for any n. If you iterate the step function n times
starting with false as an answer for 1, then you get false
for every number that's of the form 1 + 2*n. This thing
thus answers true for all the even numbers and false for
all the odd ones. A *predicate* asserts that value to be
given as an argument has some property, e.g., of being an
even number. A *predicate function* returns a Boolean value
that *tells you* whether it has such a property or not.




You're already familiar with binary relations such as
less than or equal to over the natural numbers. We will
represent binary relation as predicate functions. These
are functions that take two values (here Nat) and that
return Bool to indicate whether the values are "in the
indicated relation to each other (e.g., less than, equal,
etc).

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

/-!
Ok, so now that we have the semantic domain, what
about our expression language? We'll you write it
almost exactly as for predicate logic, but now the
arguments and operators are arithmetic, which is to
say they yield arithmetic results (natural numbers
in this work).

Just as before we have literals, as before, we'll
have a *literal* (arithmetic) expression for each
Nat; we'll have variables and interpretations that
take variables arguments and return the numerical
values that the particular interpretation assigns
to them.
-/
