import Cs2120f24.Library.natArithmetic.domain
import Cs2120f24.Library.natArithmetic.syntax

namespace cs2120f24.arith

-- DOMAIN : Theory of Natural Number Arithmetic

/-!
Nat is a type, terms of which are taken to represent
elements from the mathematical set of natural numbers:
the whole numbers from 0 on up: 0, 1, 2, ....
-/

#check Nat

-- summary
#print Nat

-- constructors
#check Nat.zero
#check Nat.succ

/-!
Suggestive names bound here to a few small terms of type Nat.
Note that we're actually using Lean to assign names to these
terms, and to unfold these names to the terms to which they're
bound, as the case may be. Unfolding names to the meanings to
which they;re bound is called δ-reduction ("delta reduction").
I guess that means that the act of binding a name to a term
should be called δ-abstraction. By automated δ reductions we
can use names and the terms they designate interchangeably in
expressions. And not only there, but in our minds, where we can
thereafter chunk up a complex representation of some possibly
complex thing under the banner of a single, simple name.
-/

/-!
Binding and using δ abstractions
-/

-- bind abstract name/identitifer, zero, to concrete term, Nat.zero
def zero : Nat  := Nat.zero

-- same idea, of δ abstraction, in this example
def one : Nat   := Nat.succ Nat.zero

-- δ abstraction involving δ *reduction* (of "one"), in this example
def two : Nat   := Nat.succ one

-- similar case here
def three       := Nat.succ two

---- δ abstraction from a δ-reduced term, this one representing 4 : ℕ.
def four        := Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))

/-!
The constructors of a type *introduce* new instances/values of that type
into the discussion. These are akin to the introduction and elimination
inference rules discussion elsewhere in this class.
-/


/-!
As a particularly special case,, Lean provides extensive support for our
usual base-10 notation for natural numbers. If Lean sees numerals using
the base-10 digits, it generally assumes it means that number as a value
of the natural number type: as opposed to, say, the rational or real type.
-/

#check 0
#check 1
#check 2
#check 3
#eval four  -- Lean uses notations when it reports back to you (here "4")

/-!
OPERATORS
-/
-- unary operators (functions)
#check (Nat.pred : Nat → Nat)
#check (Nat.add: Nat → Nat → Nat )
#check (Nat.mul: Nat → Nat → Nat )
#check (Nat.sub: Nat → Nat → Nat )
#check (Nat.div: Nat → Nat → Nat )
-- the natural numbers are "closed" under these operations

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

-- concrete syntax (it's just arithmetic)


-- nothing for pred
#eval 2 + 3
#eval 2 * 3
#eval 3 - 2
#eval 3 / 2
#eval 5 / 2
#eval 5 % 2


-- evaluate some application expressions using pred and poof
#eval pred zero
#eval pred one
#eval pred two

-- We can use nice notation for natural numbers
#eval pred 2
#eval pred 3
#eval pred 4

-- inc (short for increment) is just another name for succ
#eval inc 0   -- expect 1
#eval inc 1   -- expect 2

-- dec (short for decrement) is defined the same as pred
#eval dec 5

-- add
#eval add 0 5
#eval add 5 0
#eval add 3 7

-- mul
#eval mul 5 0
#eval mul 0 5
#eval mul 5 3

-- eq_zero
#eval eq_zero 0
#eval eq_zero 1
#eval eq_zero 10

-- eq
#eval eq 0 0
#eval eq 0 1
#eval eq 1 0
#eval eq 1 1
#eval eq 3 2
#eval eq 2 3
#eval eq 10 10

-- le (≤)
#eval le 0 0
#eval le 0 2
#eval le 1 0
#eval le 2 0
#eval le 3 3
#eval le 3 4
#eval le 4 3

/-!
## Our Own Arithmetic Expression Language and Evaluator
-/
open arithExpr

-- variable expressions
def K : arithExpr := {⟨0⟩}
def M : arithExpr := {⟨1⟩}
def N : arithExpr := {⟨2⟩}


end cs2120f24.arith
