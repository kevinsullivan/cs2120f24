/-!
NOTE: This file is now dated. Refer first to Library/natArith
for a better structured natural number arithmetic library.
That said, original class notes and material covered, as
covered, is here for reference. END NOTE.
-/

/-!
An expression language for natural number arithmetic all in one file,
with homework on completing the syntax and semantics of this language.
The evolved and refined version of this code in Library/natArithmetic.

There we explore the domain by deliving into the Nat type, its simple
induction principle, and an expression language for this domain. We're
on a path to incorporating arithmetical relational expressions into
our currently bare version of propositional logic. That will give us a
wonderful version of proposition logic with arithmetic relations as a
theory extension.

That will take us to the end of our adventurea in formal language design.
We will not develop our own model theory for the artithmetic component.
That would involve solving natural number algebra problems.

Rather, we'll then turn to a real-world "satisfiability modulo theories"
language and solver that *can* solve systems of arithmetic constraints.
Understanding what we can do with a language and systen for PL extended
with a theory of natural number arithmetic should give you a sense of the
rapidly increasing expressiveness of logics we can envision, specify, and
use.
-/

namespace cs2120f24.lecture.natArithmetic

structure ArithVar : Type :=
  mk :: (index: Nat)
deriving Repr

inductive ArithUnOp : Type
| fac
deriving Repr

inductive ArithBinOp : Type
| add
| sub
| mul
deriving Repr

-- abstract syntax
inductive ArithExpr : Type
| lit (from_ : Nat) : ArithExpr
| var (from_var : ArithVar)
| unOp (op : ArithUnOp) (e : ArithExpr)
| binOp (op : ArithBinOp) (e1 e2 : ArithExpr)
deriving Repr

-- concrete syntax
notation " { " v " } " => ArithExpr.var v
notation " [ " n " ] " => ArithExpr.lit n
notation e " ! " => ArithExpr.unOp ArithUnOp.fac e
notation e1 " + " e2 => ArithExpr.binOp ArithBinOp.add e1 e2
notation e1 " - " e2 => ArithExpr.binOp ArithBinOp.sub e1 e2
notation e1 " * " e2 => ArithExpr.binOp ArithBinOp.mul e1 e2

-- Semantics (incomplete, to be finished in homework)
def arithEval : ArithExpr → (ArithVar → Nat) → Nat
| ArithExpr.lit (fromNat : Nat),       i =>  fromNat
| ArithExpr.var (fromVar : ArithVar), i => i fromVar
| ArithExpr.unOp op e,                i => 0
| ArithExpr.binOp op e1 e2,           i => 0

/-!
HOMEWORK:

Below are some expressions that aren't evaluating to the
right answers. The problem is that our specification of
the semantics is not yet complete. Your job is to complete
the specification the semantics of arithmetic expressions.
You should do this homework on your own. You may talk with
friends about our propositional logic expression language,
and that will likely help you to see how to proceed here,
but please do finish this assignment entirely on your own
to be sure you're prepared to move on in our class.
-/

/-!
We give you three variables expressions to work with and
two different interpretations.
-/

-- variable expressions
def X := { ⟨ 0 ⟩ }
def Y := { ⟨ 1 ⟩ }
def Z := { ⟨ 2 ⟩ }

def interp_0 (_ : ArithVar) := 0  -- every variable has value 0
def interp_1 : ArithVar → Nat     -- variables have specified values
| ArithVar.mk 0 => 2          -- X := 2
| ArithVar.mk 1 => 3          -- Y := 3
| ArithVar.mk 2 => 0          -- Z := 0
| ArithVar.mk 3 => 4          -- N := 4
| ArithVar.mk 4 => 6          -- M := 6
| ArithVar.mk 5 => 3          -- P := 3
| _ => 0                      -- any other variable := 0

-- We can now evaluate the value of some arithmetic expressions
#eval! arithEval (ArithExpr.lit 3) interp_0
#eval! arithEval [3] interp_0     -- expect 3
#eval! arithEval [3] interp_1     -- expect 3
#eval! arithEval ([5]!) interp_0  -- expect 120
#eval! arithEval X interp_0       -- expect 0
#eval arithEval X interp_1        -- expect 2
#eval arithEval Y interp_1        -- expect 3
#eval arithEval Z interp_1        -- expect 0

/-!
But these evaluations are not producing the mathematically
correct answers.
-/

#eval arithEval (X + Y) interp_1    -- expect 5
#eval arithEval (X * Y) interp_1    -- expect 6
#eval arithEval (Y - [1]) interp_1  -- expect 2   -- correction here

-- Extra credit: Make this work, too
#eval arithEval (Y !) interp_1      -- expect 6
/-
Note that we have to put that space between X and !.
If we write X!, Lean interprets that as a single name
and interprets it as an undefined name.
-/

end cs2120f24.lecture.natArithmetic
