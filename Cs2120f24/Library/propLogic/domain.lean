namespace cs2120f24

/-!
### Semantic Domain: Boolean Algebra

The semantic domain in propositional logic is
Boolean algebra. This file contributes a few
bits of Boolean algebra to the library provided
by Lean.

#### What is Boolean Algebra

Boolean algbra has
- the type, Boolean, with two values: true, false
- a type, var, for propositional logic variables
- types for unary and binary syntax-composing operators
  - the only unary operator we define is *not*
  - our binary operators are *and*, *or*, *imp*, etc.
  - each composes larger *expressions* from smaller ones
- an expression evaluation procedure
  - convert literal expressions to corresponding Booleans
  - convert variable v to Bool by applying interpretation
  - recursive expressions:
    - convert subexpressions to Bools recursively
    - combine resulting Bools using right Boolean function
    - example: in "P ∧ Q", ∧ is interpreted as Boolean &&


#### Lean's Library for Boolean Algebra

The standard Lean library defines Boolean functions
commonly used in programming (and, or, not, etc). But
it doesn't define all the ones we need, including the
likes of implies and iff. In other words, Lean doesn't
give us a complete enough specification of the semantic
domain of Boolean algebra. So in this file, we'll just
define the rest of what we need.

#### We need to define a few missing Boolean function
For now, that means binary Boolean functions for implies
and iff. These examples show how easy it it to specify
functions like these in Lean. Each is defined "by cases",
with one case for each possible combination of argument
values. In other words, we're specifying truth tables.
-/

-- Implication
def imp : Bool → Bool → Bool
| true, true => true
| true, false => false
| false, true => true
| false, false => true

-- Equivalence (bi-conditional, if and only if)
def iff : Bool → Bool → Bool
| true, true => true
| false, false => true
| _, _ => false

-- Define your own here.

-- Problem #1 (combinatorics): How many binary Boolean functions are there?
-- Problem #2 (Boolean algenra): Write a specification of the exclusive or function (xor)

end cs2120f24
