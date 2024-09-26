namespace cs2120f24.propLogicwithArith.domain

-- # Semantic Domain: Boolean Algebra

/-!
Lean already provides most of what we need, in the
Bool type and its related operations: &&, ||, !, etc.

Here we define a few operations that we need that are
missing from the standard Lean libraries
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
