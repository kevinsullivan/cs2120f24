import «Cs2120f24».Library.propLogic.model_theory.properties

namespace cs2120f24.propLogic

-- Let P, Q, and R be PL variable expressions
def P := {⟨0⟩}
def Q := {⟨1⟩}
def R := {⟨2⟩}

-- Here are fundamental *equivalences* in propositional logic

def andIdempotent   := P ↔ (P ∧ P)
def orIdempotent    := P ↔ (P ∨ P)

def andCommutative  := (P ∧ Q) ↔ (Q ∧ P)
def orCommutative   := (P ∨ Q) ↔ (Q ∨ P)

def identityAnd     := (P ∧ ⊤) ↔ P
def identityOr      := (P ∨ ⊥) ↔ P

def annhilateAnd    := (P ∧ ⊥) ↔ ⊥
def annhilateOr     := (P ∨ ⊤) ↔ ⊤

def orAssociative   := ((P ∨ Q) ∨ R) ↔ (P ∨ (Q ∨ R))
def andAssociative  := ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R))

def distribAndOr    := (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R))
def distribOrAnd    := (P ∨ (Q ∧ R)) ↔ ((P ∨ Q) ∧ (P ∨ R))

def distribNotAnd   := ¬(P ∧ Q) ↔ (¬P ∨ ¬Q)  -- DeMorgan's law
def distribNotOr    := ¬(P ∨ Q) ↔ (¬P ∧ ¬Q)  -- DeMorgan's law

def equivalence     := (P ↔ Q) ↔ ((P ⇒ Q) ∧ (Q ⇒ P))
def implication     := (P ⇒ Q) ↔ (¬P ∨ Q)
def exportation     := ((P ∧ Q) ⇒ R) ↔ (P ⇒ Q ⇒ R)
def absurdity       := (P ⇒ Q) ∧ (P ⇒ ¬Q) ⇒ ¬P

-- FYI, these "identities" really are all valid propositions

#eval! is_valid andIdempotent
#eval! is_valid orIdempotent

#eval! is_valid andCommutative
#eval! is_valid orCommutative

#eval! is_valid identityAnd
#eval! is_valid identityOr

#eval! is_valid annhilateAnd
#eval! is_valid annhilateOr

#eval! is_valid orAssociative
#eval! is_valid andAssociative

#eval! is_valid distribAndOr
#eval! is_valid distribOrAnd

#eval! is_valid distribNotAnd
#eval! is_valid distribNotOr

#eval! is_valid equivalence
#eval! is_valid implication
#eval! is_valid exportation
#eval! is_valid absurdity


end cs2120f24.propLogic
