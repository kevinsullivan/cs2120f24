import «Cs2120f24».Lectures.«02_prop_logic».formal.properties

namespace cs2120f24

def P := {⟨0⟩}
def Q := {⟨1⟩}
def R := {⟨2⟩}

def andCommutative  := (P ∧ Q) ↔ (Q ∧ P)
def orCommutative   := (P ∨ Q) ↔ (Q ∨ P)

def andAssociative  := ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R))
def orAssociative   := ((P ∨ Q) ∨ R) ↔ (P ∨ (Q ∨ R))

-- So-called "DeMorgan's Laws"
def distribNotAnd   := ¬(P ∧ Q) ↔ (¬P ∨ ¬ Q)
def distribNotOr    := ¬(P ∨ Q) ↔ (¬P ∧ ¬ Q)

def distribAndOr    := (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R))
def distribOrAnd    := (P ∨ (Q ∧ R)) ↔ ((P ∨ Q) ∧ (P ∨ R))
-- exercise translate this rule into English

def identityAnd     := (P ∧ ⊤) ↔ P
def identityOr      := (P ∨ ⊥) ↔ P

def annhilateAnd    := (P ∧ ⊥) ↔ ⊥
def annhilateOr     := (P ∨ ⊤) ↔ ⊤

def andIdempotent   := P ↔ (P ∧ P)
def orIdempotent    := P ↔ (P ∨ P)

def implication     := (P ⇒ Q) ↔ (¬P ∨ Q)
def equivalence     := (P ↔ Q) ↔ ((P ⇒ Q) ∧ (Q ⇒ P))
def exportation     := ((P ∧ Q) ⇒ R) ↔ (P ⇒ Q ⇒ R)
def noContradition  := ¬(P ∧ ¬P)
def absurdity       := (P ⇒ Q) ∧ (P ⇒ ¬Q) ⇒ ¬P
