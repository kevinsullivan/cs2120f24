
inductive UnOp where
| not

inductive BinOp where
| and
| or
| imp
| iff

structure BoolVar where (index : Nat)

inductive PLExpr : Type
| lit_expr (from_bool : Bool) : PLExpr
| var_expr (from_var : BoolVar)
| un_op_expr (op : UnOp) (e : PLExpr)
| bin_op_expr (op : BinOp) (e1 e2 : PLExpr)

open PLExpr

notation:max " ⊤ " => (PLExpr.lit_expr true)
notation:max " ⊥ " => (lit_expr false)
notation:max "{" v "}" => (var_expr v)

notation:max "¬" p:40 => un_op_expr UnOp.not p
infixr:35 " ∧ "  =>  PLExpr.bin_op_expr BinOp.and
infixr:30 " ∨  "  => PLExpr.bin_op_expr BinOp.or
infixr:25 " ⇒ " => bin_op_expr BinOp.imp
infixr:20 " ⇔ " => bin_op_expr BinOp.iff

def P := {⟨0⟩}
#check P
#check P ∧ P
#check (P ∧ P)
#check (P ∧ P) ⇒ P
#check P ∧ P ⇒ P

def wet : PLExpr := {⟨0⟩}
def rain : PLExpr := {⟨1⟩}
def sprink : PLExpr := {⟨2⟩}

def formal_0 := rain ∧ sprink ⇒ ⊥
