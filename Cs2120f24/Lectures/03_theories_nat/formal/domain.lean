namespace cs2120f24


/-!
#### Domnain: Constructing Natural Numbers from Parts

We represent them as terms of type Nat.

inductive Nat : Type
| zero
| succ (n' : nat)
-/

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
The point here is that you can do complex constructor
expression pattern-matching to access sub- and sub-sub-
parts of incoming values. Answering the quiz question is
extra worthiness points.
-/

/-!
#### Operations

##### Arithmetic (→ Nat)
-/

/-!
Unary:
- succ :    Nat → Nat
- pred :    Nat → Nat
- double :  Nat → Nat
- square :  Nat → Nat
-/


/-!
Binary:
- add n m : Nat → Nat → Nat
- sub n m : Nat → Nat → Nat
- mul n m : Nat → Nat → Nat
- exp n m : Nat → Nat → Nat
-/


/-!
##### Boolean (→ Bool, from Nat)

- eq_0 n
- eq n m
- le n m
- even n
- odd n
-/

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
- div, /
etc.

But even better than that,, let's from now on just
use Lean's definition of Nat, along with all kinds
of machinery, including all standard math notations
with the right properties to be useful.
-/

/-!
Ok, so now that we have the semantic domain, what
about our expression language? We'll you write it
almost exactly as for predicate logic, but now the
arguments and operators are arithmetic, which is to
say they yield arithmetic results (natural numbers
in our case here).

Just as before we have literals, as before, we'll
have a *literal* (arithmetic) expression for each
Nat; we'll have variables and interpretations that
take variables arguments and return the numerical
values that the particular interpretation assigns
to them.
-/

namespace cs2120f24
