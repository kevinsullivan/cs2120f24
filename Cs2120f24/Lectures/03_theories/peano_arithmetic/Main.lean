import Cs2120f24.Lectures.«03_theories».peano_arithmetic.domain
import Cs2120f24.Lectures.«03_theories».peano_arithmetic.peano

namespace cs2120f24

-- DOMAIN


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

-- summary
#print Nat

-- constructors
#check Nat.zero
#check Nat.succ

-- A few constructibleble terms
def zero : Nat  := Nat.zero
def one : Nat   := Nat.succ Nat.zero
def two : Nat   := Nat.succ one
def three       := Nat.succ two   -- Lean infers ": Nat" type declaration so we can omit it
def four        := Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))

/-!
As a special case, Lean provides ordinary base-10 notation for natural numbers.
-/

#check 0
#check 1
#check 2
#check 3
#eval four  -- Lean uses notations when it reports back to you (here "4")


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


--

end cs2120f24
