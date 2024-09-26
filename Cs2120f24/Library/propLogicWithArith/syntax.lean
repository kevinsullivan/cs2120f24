import cs2120f24.Library.natArithmetic.syntax

namespace cs2120f24.propLogicWithArith.syntax

/-!
# Propositional Logic: Syntax
-/

structure BoolVar : Type where
(index: Nat)


inductive UnOp : Type
| not


inductive BinOp : Type
| and
| or
| imp
| iff


--open natArithmetic

inductive PLExpr : Type
| lit_expr (from_bool : Bool) : PLExpr
| var_expr (from_var : BoolVar)
| un_op_expr (op : UnOp) (e : PLExpr)
| bin_op_expr (op : BinOp) (e1 e2 : PLExpr)
| rel_op_expr (op : natArithmetic.syntax.RelOp) (a1 a2 : natArithmetic.syntax.ArithExpr)


open PLExpr

notation:max " ⊤ " => (lit_expr true)
notation:max " ⊥ " => (lit_expr false)
notation:max "{" v "}" => (var_expr v)
notation:max "¬" p:40 => un_op_expr UnOp.not p
infixr:35 " ∧ "  =>  bin_op_expr BinOp.and
infixr:30 " ∨  "  => bin_op_expr BinOp.or
infixr:20 " ↔ " => bin_op_expr BinOp.iff
infixr:25 " ⇒ " => bin_op_expr BinOp.imp



namespace cs2120f24.propLogicWithArith.syntax
