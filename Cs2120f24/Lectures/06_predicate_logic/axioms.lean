import «Cs2120f24».Library.propLogic.syntax
import «Cs2120f24».Library.propLogic.semantics
import «Cs2120f24».Library.propLogic.model_theory.properties

namespace cs2120f24.propLogic

def P : PLExpr := {⟨0⟩}
def Q : PLExpr := {⟨1⟩}
def R : PLExpr := {⟨2⟩}


/-!
The following *semantically* valid propositions,
organized into subsets pertaining to corresponding
logical connectives, provide a more informative
window that truth tables on the intended meanings
of the logical connectives.

For exaple the first cluster of three rules fully
defines the intended meaning of conjunction (and).
If two propositions, let's call them P and Q, are
each true, the P ∧ Q is true; and if P ∧ Q is true,
then so part P, and Q, individually. That's all we
need to say to precisely define "what and means" in
propositional, and many other, logics.
-/

-- AND
def and_intro := R ⇒ Q ⇒ R ∧ Q
def and_elim_left := R ∧ Q ⇒ R
def and_elim_right := R ∧ Q ⇒ Q

#check And
#check (@And)

-- OR
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

def true_intro := ⊤
def false_elim := ⊥ ⇒ P

/-!
As an aside, we can apply our validity checker
(our *is_valid* function) to each proposition
to confirm that each and every one of them is
valid.
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

#eval! is_valid  true_intro
#eval! is_valid false_elim

end cs2120f24.propLogic
