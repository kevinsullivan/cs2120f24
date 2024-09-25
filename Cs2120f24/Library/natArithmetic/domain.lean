namespace cs2120f24.natArithmetic

/-!
# Domain: natural number arithmetic

## The Nat Type

We use Lean's definition of the Nat type.

inductive Nat : Type
| zero : Nat
| succ (n' : Nat) : Nat
-/

/-!
## Operations
-/

/-!
### Unary Operations-/

-- identity function, two ways
def id : Nat → Nat
| n => n

-- fyi: you can move arguments before the : and name them there
def id' (n : Nat) : Nat := n

-- increment (add one) function
def inc : Nat → Nat
| n => n + 1       -- Nat.succ n

-- just moving argument before colon, very same function
def inc' (n : Nat) := n + 1

-- predecessor function
def pred : Nat → Nat
| 0 => 0        -- Nat.zero
| n' + 1 => n'  -- Nat.succ n'

-- decrement (just another name for predcessor)
def dec : Nat → Nat := pred

-- factorial
def fac : Nat → Nat
| 0 => 1
| (n' + 1) => (n' + 1) * fac n'


/-!
### Binary Operations
-/

def add : Nat → Nat → Nat
| n, 0 => n
| n, (m' + 1) => (add n m') + 1

def sub : Nat → Nat → Nat
| 0, m => 0
| n, 0 => n
| (n' + 1), (m' + 1) => sub n' m'

def mul : Nat → Nat → Nat
| _, 0 => 0
| n, (m' + 1) => add n (mul n m')

def exp : Nat → Nat → Nat
| n, 0 => 1
| n, (m' + 1) => n * exp n m'

/-!
## Relations

### Unary Relations
-/

-- is n equal to zero? does n have the property of being zero?
def isEq0 : Nat → Bool
| 0 => true
| _ => false

-- what predicate does this predicate function "decide"?
-- we do see that it's a unary relation / predicate (a property of a natural number)
def poof : Nat → Bool
| 0 => true
| 1 => false
| n'' + 2 => poof n''

-- haha: is n *even*, does n have the property of being even?
def isEven : Nat → Bool := poof


/-!
### Binary Relations
-/

def le : Nat → Nat → Bool
| 0, m => true
| (n' + 1), 0 => false
| (n' + 1), (m' + 1) => le n' m'

def gt : Nat → Nat → Bool
| n, m => ¬ le n m

#eval le 5 3
#eval gt 5 3

def eq : Nat → Nat → Bool
| 0, 0 => true
| 0, (m' + 1) => false
| (n'+1), 0 => false
| (n'+1), (m'+1) => eq n' m'

def lt : Nat → Nat → Bool
| n, m => le n m && !(eq n m)

#eval lt 1 0

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
