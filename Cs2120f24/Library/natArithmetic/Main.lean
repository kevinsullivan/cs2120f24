import Cs2120f24.Library.natArithmetic.domain
import Cs2120f24.Library.natArithmetic.syntax

namespace cs2120f24.arith

/-!
# Domain: Natural Number Arithmetic

/-!
As we saw in our investigation into propositional logic,
the semantic domain for proposition logic comprises not
just the Boolean type, supplying the two basic truth values
of Boolean algebra, but also the full range of oeprations
that consume Boolean values and return other Boolean values.
Examples are typically denoted as && (Boolean and), || (or),
! (not). So now when we talk about Boolean *algebra* we mean
the type of Boolean values along with all of the operations
(unary, binary, ternary, etc.), their properties, and so on.

With the *domain* of Boolean algebra in hand,  we were then
able to specify our own syntax for *propositional logic* *and*
a set of semantic mappings (functions!) from syntactic terms
in propositional logic to their corresponding Boolean algebra
meanings, both values *and functions*.

In this chapter, we do the same thing but for the domain of
natural number arithmetic. This is just the arithmetic of the
whole numbers from zero on up. Along the way we'll meet the
Lean type *Nat* (also written ℕ), the terms of which we use
to represent natural numbers; how to construct arbitrarily
large values of this type; and how to use values of this type
through *case analysis*, *pattern matching*, and *recursion*.
-/
-/


/-!
## The Nat Type and its Value Constructors

Nat is a type, the terms of which have been designed for the
express purpose of representing natural numbers, the infinite
set of whole numbers from zero on up by ones.
-/


/-!
Here is the intended correspondence:

0   Nat.zero
1   Nat.succ Nat.zero
2   Nat.succ (Nat.succ Nat.zero)
3   Nat.succ (Nat.succ (Nat.succ Nat.zero))
etc

The *constant* term, Nat.zero, is taken to represent the natural
number, 0. Lean provides the notation, 0, for Nat.zero, and it is
important to use 0 instead of Nat.zero to take advantage of some
Lean capabilities when we get further into proofs.

The second, one-argument constructor, Nat.succ : Nat → Nat, takes
any natural number, let's call it n', as an argument, and yields the
term, (Nat.succ n'), which we will take to represent one more than n'.
We will call one more than n'the *successor* of n'

When writing Lean definitions it's best to write n' + 1 rather
than (Nat.succ n') to take advantage of certain automations later
on. Using the notations 0 and _ + 1 also makes definitions easier
to read for most people.
-/

#check Nat  -- Nat is a type. What's it's type? It's Type.

#print Nat  -- Here are it's constructors. Go to its definition!


-- constructors
#check Nat.zero       -- constant
#check (Nat.succ)     -- function: takes term of type Nat, returns another
#check Nat.succ       -- alternative way to write the same function type

-- using constructors
#check Nat.zero       -- term has type Nat
#check 0              -- preferred notation for same value
#check Nat.succ 0     -- given Nat, construct next larger Nat
#reduce Nat.succ 0    -- reduce prints it in standard notation
#reduce 0 + 1         -- preferred notation for successor (here, of 0)
#reduce (0 + 1) + 1   -- Nat.succ (Nat.succ Nat.zero), i.e., 2
#reduce ((0 + 1) + 1) + 1   -- this term represents 3, etc., ad infinitum

/-!
This representation of natural numbers is what we'd call a "unary"
notation. You've used it since grade school, where, for example,
you could represent three as ///; four, ////; five, /////, etc.
-/

def zero'  : Nat   := Nat.zero
def one'   : Nat   := Nat.succ Nat.zero
def two'   : Nat   := Nat.succ one'
def three'         := Nat.succ two'
def four'          := Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))

/-!
Better to use everyday arithmetic Notation. Lean provides special
support for natural numbers as they're so widely used.
-/

def zero  : Nat   := 0
def one   : Nat   := 1
def two   : Nat   := 2
def three := 3    -- Lean knows 3's a Nat; you don't have to say so
def four  := 4


/-!
## Elimination (Use) of Nats: Case Analysis and Pattern Matching

How can a function use some arbitrarilty selected value/term of
type Nat?

### No elimination

One possibility is to incorporate it into a larger structure
without ever looking into its details to make a decision. The
Nat.succ constructor does just that. As an example, we here's
a function, inc, that takes a (any) Nat value, let's call it
n, as an argument and that returns ("reduces to") Nat.succ n.
You can right-click on inc and open a new window on the file
where inc is defined (domain).
-/

#check inc

#reduce inc
-- fun x => x.succ
-- "a function that takes a Nat, x, and returns Nat.succ x"



/-
Put another way, you can increment a Nat, n, without knowing
anything about n beyonds its type, by just "wrapping" it in
another (Nat.succ _) construction.
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

#check K + M
#check (K + M) * N

end cs2120f24.arith
