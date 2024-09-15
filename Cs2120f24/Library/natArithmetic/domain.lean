namespace cs2120f24

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

- English: zero is a (term of type) Nat; and if n' is any Nat, then so is (succ n')
- With these two constructors one can build succ terms of any length, n
- we represent the natural number n as the term of type Nat of that length
- zero is not the successor of any number by "disjointness of constructors"
- no number is the successor of two distinct numbers by "injectivity of constructors"
-/

#print Nat

/-!
### Constructors are "Introduction Rules"

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
### Elimination (Use, Consumption) is by Case Analysis

The analysis distinguishes between Nat.zero and a term in which Nat.succ
was applied to an argument: in this case a one-smaller term of type Nat.
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

-- identity
def id : Nat → Nat
| n => n

-- that can also be written like this, by the way.
def id' (n : Nat) : Nat := n

-- increment, also in this alternative Lean syntax
def inc (n : Nat) := Nat.succ n


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
### Boolean (→ Bool, from Nat)

- eq_0 n
- eq n m
- le n m
- even n
- odd n
-/

-- does n equal zero?
def eq_zero : Nat → Bool
| Nat.zero => true
| _ => false


-- are n and m equal?
def eq : Nat → Nat → Bool
| 0, 0 => true
| (Nat.succ n'), 0 => false
| 0, (Nat.succ n') => false
| Nat.succ n', Nat.succ m' => eq n' m'

-- is n ≤ m
def le : Nat → Nat → Bool
| 0, _ => true
| n, 0 => false
| (Nat.succ n'), (Nat.succ m') => le n' m'

/-
NOW YOU! EXERCISES: Complete the definitions of
the following binary relations. You may uses Lean's
built-in Boolean operators, &&, ||, and ! as needed.

- less than (lt)
- greater than or equal
- greater than
-/

def lt : Nat → Nat → Bool
| n, m => le n m && !eq n m

def gt : Nat → Nat → Bool
| n, m => !le n m

def ge : Nat → Nat → Bool
| n, m => gt n m || eq n m

/-!
Concrete notations for arithmmetic.

We could define our own. Better yet would be to use
the well designed collection of notations provided by
the Lean library, including sensible precedence levels
and associativity properties.

- inc, ++
- dec, --
- add, +
- mul, *
- sub, -
etc.
-/

end cs2120f24
