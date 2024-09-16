namespace cs2120f24.arith

/-!
# Domain: natural number arithmetic
-/

#check Nat
#print Nat

/-!
## Inductive Definition of Nat

We represent them as terms of type Nat.

inductive Nat : Type
| zero
| succ (n' : Nat)

/-! KEEP?

- with these two constructors one can build succ terms of any length, n; we represent n as the term of that length
- disjointness of constructors: Different constructors yield unequal values. zero is not the successor of any number.
- injectivity of constructors: Different arguments yield unequal values. no number is the success of distinct numbers.
-/


- English: zero is a (term of type) Nat; and if n' is any Nat, then so is (succ n')
- With these two constructors one can build succ terms of any length, n
- we represent the natural number n as the term of type Nat of that length
- zero is not the successor of any number by "disjointness of constructors"
- no number is the successor of two distinct numbers by "injectivity of constructors"
-/

#print Nat

/-!
## Constructors are for Constructing, for Introducing, Values of a Type

The constructors of a type are its introduction rules. Each provides a way to
construct a new term of the given type by applying the constructor to argument
values of the specified types. Here there are only two constructors, and one of
them (succ) requires another as an argument. The only one we can have at first
then is Nat.zero. Call that 0. The only other thing you can do is apply succ to
that, yielding (succ 0). This term is *also of type Nat* so we can apply succ
again, to construct succ (succ 0); and so on essentially forever.
-/

-- See examples in Main.lean
/-!
## Eliminators are for Consuming Values: Case Analysis & Pattern Matching

The analysis distinguishes between Nat.zero and a term in which Nat.succ
was applied to an argument: in this case a one-smaller term of type Nat.
We could say that the two *cases* for the structure of a Nat supplied as
an argument are Nat.zero and (Nat.succ n'), where n' is name that we bind
temporarily to that one-smaller natural number.

Pattern matching in Lean let's us bind names to the presumed arguments to
constructors when doing case analysis. We can then use these names to work
with these values when computing a result to return.

The easy example is the natural number decrement (subtract one) function.
It takes a Nat term as an argument. There are two cases: it's either zero,
in which we we return 0, or it's (succ n') where n' was the argument that
must have been provided when the tern was built. Binding of names to these
argument "fields" basically gives us "getter functions" for retrieving the
argument values incorporated into a term of the given type.

Nat.zero has no arguments. It's a constant constructor. Nat.succ has one:
the natural number to represent the successor of. If the argument, n, to
the decrement function is not zero, then it must be (Nat.succ n') where n'
is some other term of type Nat. Given n, pattern matching uses x-ray vision
to see that it's actually (Nat.succ _), then binds the name n' to it, so
that it can be used to derive the final return value.
-/

def pred : Nat → Nat
| Nat.zero => 0
| Nat.succ n' => n'

/-!
Pattern matching on constructor expressions let's you drill
down into and around complex incoming parameter values. What
does this function do/compute? Describe it in natural language.
It takes a natural number n as an argument and ...
-/

def poof : Nat → Bool
| Nat.zero => true
| Nat.succ Nat.zero => false
| Nat.succ (Nat.succ n'') => poof n''


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
| n => Nat.succ n
def inc' (n : Nat) := Nat.succ n

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
| (Nat.succ n') => n'

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
### Binary Operations

Now we turn to defining the usual binary operations
of arithmetic for Nat-type arguments. We also see a
next level of pattern matching, where we now match
on both arguments to add. Moreover, we *analyze*
just the second argument and consider the two cases,
that m = 0 and that m = (succ m') for some m'. The
definition then says this:

- adding n and 0 returns n
- adding n and (m' + 1) returns 1 + (adding n m')
-/
def add : Nat → Nat → Nat
| n, 0 => n
| n, (Nat.succ m') => Nat.succ (add n m')

/-
Detail: we define subtraction of any natural
number from 0 yielding 0. There are no negative
natural numbers, so this is the best we can do.
Notice that on the first pattern matching line,
the "m" is underlined in yellow. That reminds
us that we don't use it in defining the return
value. We can get rid of the yellow warning by
using an "_" (underscore) in place of m. An
underscore matches any value.
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
