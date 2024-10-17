/-!
# Exam 1

This is an individual exam. You must complete it entirely on your own,
with no outside inputs of any kind other than in response to questions
posed directly to the instructor. You must take the exam while in class
in the classroom. When you come in to the classroom, spread yourselves
out, mix up, and don't sit where you or someone you know of might hope to
catch a glance.
-/

/-!
The sources of propositions on this exam will prominently include those
in the two files, Library/PropLogic/identities.lean and axioms.lean.
-/

/- #1

Given a proposition in propositional logic express it in precise English

Given a PL in English, formalize it as an expression in propositional logic (in Lean)

Given an expression, give examples of interpretations and evaluate the expression "under" them

Given a proposition in PL, write (in a Lean comment block) a truth table for it

If there are counter-examples, pick one and explain in English exactly why it's one
-/

/- #2

Given a proposition in propositional logic in Lean4, rewrite it to make
all implicit parentheses explicit, accounting for both associativity and
precedence (binding strength) properties of concrete operator notations.

Given a proposition in propositional logic in Lean4, rewrite it to
remove as many parentheses as you can without changing its meaning.
-/

/-! #3

Be able to show that you truly and fully understand the meaning of implication.
-/

/-! #4

Give a specification of the formal syntax and operational semantics of a tiny
little language, show that you fully understand what it's saying by filling in
a few missing bits or explaining particularly important elements. Concepts will
include abstract syntax (including literal, variable, and operator expressions),
concrete syntax concepts, interpretations, and the procedure for evaluating the
truth of an expression given an interpretation (semantic evaluation).
-/


/-!
semantic domain : some domain in which expressions will have meanings

syntax: we represent a syntax as a *type* whose values/terms represent (expressions in ourlanguage)
inductive, structure

semantics:
-/

-- syntax is a data type
inductive MyVariable : Type
| x
| y
| z

open MyVariable

-- variable interpretations
def i0 : MyVariable → Nat
| x => 2
| y => 4
| z => 6

#eval i0 x

def i2 : MyVariable → Nat
| x => 8
| y => 1
| z => 17

-- syntax!
inductive MySyntax : Type
| Zero
| Lit (n : Nat)
| Succ (s : MySyntax)
| Add (s1 : MySyntax) (s2 : MySyntax)
| Mul (s1 : MySyntax) (s2 : MySyntax)
| Var (v : MyVariable)

-- semantics!
open MySyntax
def semantics : MySyntax → (MyVariable → Nat) →  Nat
| Zero, _ => 0
| Lit n, _ => n
| Var v, i => i v
| Succ s, i => semantics s i + 1
| (MySyntax.Add s1 s2), i => (semantics s1 i) + (semantics s2 i)
| (MySyntax.Mul s1 s2), i => (semantics s1 i) * (semantics s2 i)

-- Examples
def e0 : MySyntax := MySyntax.Zero    -- 0
def e1 : MySyntax := Zero             -- 0
def e2 : MySyntax := Succ e1          -- e1 + 1 = 0 + 1 = 1
def e3 := Succ e2                     -- e2 + 1 =
def e4 := Succ (Succ (Succ (Zero)))   -- 3
def e5 := Add e4 e2
def e6 := Add (Var x) e4
def e7 := Mul e6 (Lit 2)

-- yay, we can compute meaing of any expression now!
#eval semantics e4 i0
#eval semantics e6 i0
#eval semantics e6 i2
#eval semantics e7 i0
