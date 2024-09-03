namespace cs2120f24


/-!
#### Domnain: Constructing Natural Numbers from Parts

We represent them as terms of type Nat.

inductive Nat : Type
| zero
| succ (n' : nat)
-/

#check Nat  -- come back after Right click Nat; Go to Definition


/-!
#### Destructuring and Using Natural Numbers in Computations

Crucial point: we have to define a function with a specific
return value for every possible value of the argument type,
Nat. We break the infinity of Nat values into two classes:
there is Nat.zero; and then every other Nat value has to be
the successor (Nat.succ) of some smaller natural numnber.
We call it n'.
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
The main point here is that constructor expression-based
pattern-matching can be used to access sub- and sub-sub-
parts of incoming values.
-/

/-!
#### Operations

##### Arithmetic (→ Nat)

With our two Nat constructors (zero and succ n') and the
ability to destructure any given Nat by pattern matching,
we can define a whole zoo of functions taking Nat values
as arguments.
-/

-- increment
def inc : Nat → Nat
| n => Nat.succ n

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
##### Boolean (→ Bool, from Nat)

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

namespace cs2120f24

/-
But even better than that, let's from now on just
use Lean's definition of Nat, along with all kinds
of machinery, including all standard math functions,
notations with the right precedence and associativity,
properties, lots of facts (theorems) about natural
numbers, etc.

Note that we are back in Lean's global namespace,
not within the cs212024 namespace, within which we
defined our own versions of the standard elements,
just to see how to write them. You can right click
on any of the function names below to see how the
operations are defined in the
-/

-- type
#check Nat

-- constructors
#check Nat.zero
#check Nat.succ

-- functions
#check Nat.pred
#check Nat.add
#check Nat.mul
#check Nat.sub
#check Nat.div
-- etc

-- arithmetic operator expressions
-- define in Lean's libraries
-- the type of each term here is Nat
#check Nat.pred 3
#check Nat.add 2 3
#check Nat.mul 2 3
#check Nat.sub 3 2
#check Nat.div 5 2
#check Nat.mod 5 2

-- evaluation is as we defined it
#eval Nat.pred 3
#eval Nat.add 2 3
#eval Nat.mul 2 3
#eval Nat.sub 3 2
#eval Nat.div 5 2
#eval Nat.mod 3 2
-- concrete syntax
-- nothing for pred
#eval 2 + 3
#eval 2 * 3
#eval 3 - 2
#eval 3 / 2
#eval 5 / 2
#eval 5 % 2
