import Cs2120f24.Library.natArithmetic.domain
import Cs2120f24.Library.natArithmetic.semantics

namespace cs2120f24.arith

/-!
# Domain: Natural Number Arithmetic

UNDER CONSTRUCTION. PROBABLY USEFUL BUT NOT FINISHED.
-/

/-!
## The Nat Datatype Type -/

#check Nat  -- Nat is a type. What's it's type? It's Type.
#print Nat  -- Here are it's constructors. Go to its definition!

-- constructors
#check Nat.zero       -- constant
#check (Nat.succ)     -- function: takes term of type Nat, returns another

-- notational variant
#check Nat.succ       -- alternative way to write the same function type

-- constructor expressions
#check Nat.zero       -- term has type Nat
#check 0              -- preferred notation for same value
#check Nat.succ 0     -- given Nat, construct next larger Nat
#reduce Nat.succ 0    -- reduce prints it in standard notation

-- operator expressions
#reduce 0 + 1         -- preferred notation for successor (here, of 0)
#reduce (0 + 1) + 1   -- Nat.succ (Nat.succ Nat.zero), i.e., 2
#reduce ((0 + 1) + 1) + 1   -- this term represents 3, etc., ad infinitum

/-!
This representation of natural numbers is what we'd call "unary"
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
## Elimination: Case Analysis and Pattern Matching

How can a function use some arbitrarilty selected value/term of
type Nat?

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
## Unary and Binary Operators
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

/-!
Predicate Function Representations of Properties and Relations

Just run the darned functions on your own argument(s) to
see if that sequence of values is "in the relation", which
we will interpret as "being in some particular relation of
interest to each other. As an example, less-than-or-equal
is a binary relation. As a predicate function it takes two
numeric arguments and returns a *Boolean* result indicating
whether the first (number represented by the first) is less
than or equal to the (number represented by the )second, by
the usual rules of arithmetic.

We call a unary relation--a relation/predicate with just one
argument--a set or a property. For example, the property of
being an *even* natural number corresponds with the of of all
the even numbers. A value is in the set if and only if it has
the intended property, here of being (a representation of) a
number that is even. We tend to use the word "relation" when
there are two or more arguments

Again, a predicate function indicates/decides if a given an
tuple (generally a pair but could be a sequence of any length)
of values is considered to be "in" the relation, or "related
in the specified manner." Exanple: the pair, (3, 7), is "in"
the less than or equal relation, *le : Nat → Nat → Bool*.

Here are some examples of *relational* operators on Nat-valued
arguments but now yielding Booleans indicating membership or not
in a given relation (or set), or possession of a given property.
-/

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

-- *variable expressions* from natural number indexed variables
def X : ArithExpr := {⟨0⟩}
def Y := {⟨1⟩}
def Z := {⟨2⟩}
def K := {⟨3⟩}
def M := {⟨4⟩}
def N := {⟨5⟩}

-- two interpretations

-- this one applied to any arithmetic *variable* reduces to 5
def interp_0 (_ : ArithVar) := 0

-- maps first six *variables* to given values and all the rest to 0
def interp_1 : ArithVar → Nat
| ⟨ 0 ⟩ => 2          -- X := 2
| ⟨ 1 ⟩ => 3          -- Y := 3
| ⟨ 2 ⟩ => 0          -- Z := 0
| ⟨ 3 ⟩ => 4          -- N := 4
| ⟨ 4 ⟩  => 6          -- M := 6
| ⟨ 5 ⟩  => 3          -- P := 3
| _ => 0               -- any other variable := 0


-- Here are some arithmetic expressions using abstract syntax
#eval! arithEval [3]                interp_0    -- expect 3
#eval! arithEval (ArithExpr.lit 3)  interp_0    -- desugar []
#eval! arithEval [3] interp_1       -- expect 3
#eval! arithEval ([5] !) interp_0   -- expect 120
#eval! arithEval X interp_0         -- expect 0
#eval arithEval X interp_1          -- expect 2
#eval arithEval Y interp_1          -- expect 3
#eval arithEval Z interp_1          -- expect 0


/-!
But these evaluations are not producing answers
that are not arithmetically correct. The problem
is that some of the semantic evaluation rules are
just "stubbed out" to always return zero. The goal
of Homework #3 is to get you to the point where you
genuinely know how to fix it and that it'll work.
-/

#eval arithEval (X + Y) interp_1    -- expect 5
#eval arithEval (X * Y) interp_1    -- expect 6
#eval arithEval (Y - [1]) interp_1  -- expect 2     --correction made here
#eval arithEval (Y !) interp_1      -- expect 6

end cs2120f24.arith
