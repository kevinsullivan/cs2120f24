namespace cs2120f24.propLogicwithArith.domain

-- # Semantic Domain: Boolean Algebra

/-!
Lean already provides most of what we need, in its
library-provided Bool type and related operations:
&&, ||, !, etc. Here we define a few operators that
we need that are missing from the standard library.
In other words, we're taking Lean's Bool library as
the semantic domain for our language, augmented with
just a few hand-crafted definitions of our own.
-/

-- Boolean operation: implication
def imp : Bool → Bool → Bool
| true,   true  => true
| true,   false => false
| false,  true  => true
| false,  false => true

-- Boolean Operation: Equivalence
def iff : Bool → Bool → Bool
| true,   true => true
| false, false => true
| _,     _     => false

end cs2120f24.propLogicwithArith.domain
