/-
The size of a "numeral" grows in
direct relation to the size of the natural number represented,
whereas with binary (base-2) or decimal (base-10), the sizes of
numerals are in general far shorter than the numbers that they
represent. On the other hand, the simplicity of unary notation
has many benefits for ease of reasoning, so we'll go with it to
build our own little "theory" of natural number arithmetic.

Suggestive names bound here to a few small terms of type Nat.
Note that we're actually using Lean to assign names to these
terms, and to unfold these names to the terms to which they're
bound, as the case may be. Unfolding names to the meanings to
which they;re bound is called δ-reduction ("delta reduction").
I guess that means that the act of binding a name to a term
should be called δ-abstraction. By automated δ reductions we
can use names and the terms they designate interchangeably in
expressions. And not only there, but in our minds, where we can
thereafter chunk up a complex representation of some possibly
complex thing under the banner of a single, simple name.
-/

/-!
Binding and using δ abstractions
-/

/-!
The constructors of a type *introduce* new instances/values of that type
into the discussion. These are akin to the introduction and elimination
inference rules discussion elsewhere in this class.
-/


-- --------------




/- -------------

-- arithmetic variables
structure natVar where
  (index : Nat)

-- unary arithmetic operators (here increment, decrement)
inductive arith_UnOp where
| fac

-- binary arithemtic operators (here +, -, and *)
inductive arith_BinOp where
| add
| sub
| mul

-- abstract syntax
inductive arithExpr
| lit (n : Nat)
| var (v : natVar)
| UnOp (op : arith_UnOp) (e : arithExpr)
| BinOp (op : arith_BinOp) (e1 e2 : arithExpr)

-- concrete syntax
notation " { " v " } " => arithExpr.var v
notation:max "++" n => arithExpr.UnOp arith_UnOp.inc n
notation:max "--" n => arithExpr.UnOp arith_UnOp.dec n
notation e1 "+" e2 => arithExpr.BinOp arith_BinOp.add e1 e2
notation e1 "-" e2 => arithExpr.BinOp arith_BinOp.sub e1 e2
notation e1 "*" e2 => arithExpr.BinOp arith_BinOp.mul e1 e2
-/
