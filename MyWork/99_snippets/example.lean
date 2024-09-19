import «Cs2120f24».Library.natArithmetic.semantics

namespace cs2120f24.arith

-- variable expression from variable with index 0
def X := { ⟨ 0 ⟩ }

-- interpretation: every variable goes to 5
def i0 : ArithVar → Nat := fun _ => 5

-- what is the value of X under i0?
#eval arithEval X i0    -- expect 5

-- extra sauce: what does this show?
-- put it in mathy English
#eval arithEval {⟨9⟩} i0

end cs2120f24.arith
