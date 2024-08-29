import Cs2120f24.Lectures.«02_prop_logic».prop_logic_syntax
import Cs2120f24.Lectures.«02_prop_logic».prop_logic_semantics

/-
1) P ∧ ¬P
2) P ∨ ¬P
3) P ∧ Q → P
4) P ∨ Q → P
5) P ∨ Q
-/

open cs2120f24
open Expr

/-
Play with abstract syntax
-/

-- First we'll name us some *variable expressions*

def P : Expr := var_expr (var.mk 0)
def Q : Expr := var_expr (var.mk 1)
def R : Expr := var_expr (var.mk 2)

def P_and_Q : Expr := bin_op_expr bin_op.and P Q
def Q_or_R : Expr := bin_op_expr bin_op.or Q R
def P_and_Q_imp_Q_or_R : Expr := bin_op_expr bin_op.imp P_and_Q Q_or_R

/-
Play with concrete syntax
-/

def x := var.mk 0
def y := var.mk 1
def z := var.mk 2

def X := { x }
def Y := { x }
def Z := { x }

def X_and_Y := X ∧ Y
