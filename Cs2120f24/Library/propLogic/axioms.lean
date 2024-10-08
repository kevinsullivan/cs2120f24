import «Cs2120f24».Library.propLogic.syntax
import «Cs2120f24».Library.propLogic.semantics
import «Cs2120f24».Library.propLogic.model_theory.properties

/-!
-/


namespace cs2120f24.propLogic

def P : PLExpr := {⟨0⟩}
def Q : PLExpr := {⟨1⟩}
def R : PLExpr := {⟨2⟩}



def and_intro := R ⇒ Q ⇒ R ∧ Q
def and_elim_left := R ∧ Q ⇒ R
def and_elim_right := R ∧ Q ⇒ Q

def or_intro_left := R ⇒ R ∨ Q
def or_intro_right :=  Q ⇒ R ∨ Q
def or_elim := Q ∨ R ⇒ (Q ⇒ P) ⇒ (R ⇒ P) ⇒ P

def not_intro := (R ⇒ ⊥) ⇒ ¬R
def not_elim := ¬¬R ⇒ R

def imp_intro := R ⇒ P ⇒ (R ⇒ P)
def imp_elim := (R ⇒ P) ⇒ R ⇒ P

def equiv_intro := (R ⇒ P) ⇒ (P ⇒ R) ⇒ (R ↔ P)
def equiv_elim_left := (R ↔ P) ⇒ (R ⇒ P)
def equiv_elim_right := (R ↔ P) ⇒ (P ⇒ R)

def affirm_disjunct := (P ∨ R) ⇒ P ⇒ ¬R
def affirm_consequent := (R ⇒ P) ⇒ P ⇒ R
def deny_antecedent := (R ⇒ P) ⇒ ¬R ⇒ ¬P



/-
Are they valid?
-/

#eval! is_valid  and_intro
#eval! is_valid  and_elim_left
#eval! is_valid  and_elim_right

#eval! is_valid  or_intro_left
#eval! is_valid  or_intro_right
#eval! is_valid  or_elim

#eval! is_valid  not_intro
#eval! is_valid  not_elim

#eval! is_valid  imp_intro
#eval! is_valid  imp_elim

#eval! is_valid  equiv_intro
#eval! is_valid  equiv_elim_left
#eval! is_valid  equiv_elim_right

#eval! is_valid  affirm_disjunct
#eval! is_valid  affirm_consequent
#eval! is_valid  deny_antecedent

end cs2120f24.propLogic
