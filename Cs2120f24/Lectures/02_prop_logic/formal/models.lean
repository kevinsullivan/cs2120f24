import Cs2120f24.Lectures.«02_prop_logic».formal.semantics
import Cs2120f24.Lectures.«02_prop_logic».formal.interpretation
import Cs2120f24.Lectures.«02_prop_logic».formal.truth_table
import Cs2120f24.Lectures.«02_prop_logic».formal.utilities

namespace cs2120f24

/-!
As a final chapter in our unit on propositional logic, we
now present the concepts of models and counter-examples.

Given a proposition in propositional logic (a PLExpr), call
it e, we know that if we're also given any interpretation for
it, i, the our semantic evalation function, eval_expr applied
to e an i as arguments ("actual" parameters), returns the truth
value of e as it applies to "the state of affairs in the world"
represented by i.
-/


/-!
Examples. Will be moved to Main.lean at some point.
-/

-- Propositional variables for our examples
def P : PLExpr := { ⟨ 0 ⟩ }
def Q : PLExpr := { ⟨ 1 ⟩ }
def R : PLExpr := { ⟨ 2 ⟩ }

-- an more interesting proposition (expression), e

def e := ¬(P ∧ Q) ⇒ ¬P ∨ ¬Q

-- It uses just two propositional variables, P and Q

-- We can easily *enumerate* all possible interpretations

/-!
  index | P | Q | e
    0   | 0 | 0 |
    1   | 0 | 1 |
    2   | 1 | 0 |
    3   | 1 | 1 |
-/


/-!
What do you notice about the association between the index
of an interpretation (a row in the table) and the sequence
of values in that row? Does your observation hold up if you
go up one in the number of variables.
-/

end cs2120f24
