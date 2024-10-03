import cs2120f24.Library.natArithmetic.syntax

namespace cs2120f24.propLogicWithArith.syntax

structure Var : Type where
mk :: (index: Nat)


inductive UnOp : Type
| not


inductive BinOp : Type
| and
| or
| imp
| iff


open natArithmetic.syntax -- reveals definition of RelExpr, used here
inductive PLAExpr : Type
| lit_expr (from_bool : Bool) : PLAExpr
| var_expr (from_var : Var)
| un_op_expr (op : UnOp) (e : PLAExpr)
| bin_op_expr (op : BinOp) (e1 e2 : PLAExpr)
-- NEW! abstract syntax: relational operator expressions
| rel_op_expr (re : RelExpr)
open PLAExpr

-- concrete syntax/notations for PL operators
notation " ⊤ "          => lit_expr true
notation " ⊥ "          => lit_expr false
notation:max "{" v "}"  => var_expr ( v : PLAExpr)
notation:max "¬" p:40   => un_op_expr UnOp.not p
infixr:35 " ∧ "         =>  bin_op_expr BinOp.and
infixr:30 " ∨  "        => bin_op_expr BinOp.or
infixr:25 " ⇒ "         => bin_op_expr BinOp.imp
infixr:20 " ↔ "         => bin_op_expr BinOp.iff
-- NEW! concrete {r} syntax for (PLAExpr.rel_op_expr r)
notation:max " { " a " } " => rel_op_expr a

namespace cs2120f24.propLogicWithArith.syntax
