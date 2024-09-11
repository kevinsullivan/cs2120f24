#check (@List)  --

#check Nat → Type → Type

/-
We implement concept typebuilders as PCBs.

As such, they can be viewed as functions from
arguments ultimately to (concept) types.

Is the typeDB url a parameter of the concept type,
or a value you provide to a data constructor when
you create a concept instance.

Or is it a value that can be set at runtime?

*Not all parameters are type-building parameters.*
-/


structure Foo : Type where
(n : Nat)
(b : Bool)

example : Foo := ⟨ 1, true ⟩

structure Bar (n : Nat) : Type where
(b : Bool)

#check (@Foo)
#check (@Bar)


example : Bar 1 := ⟨ true ⟩
