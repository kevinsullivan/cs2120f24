import «Cs2120f24»

/-
The first thing to do: open Cs2120f24/Demo/Demo.lean,
read it, and work through the easy exercises. It will
help to have been there for Kevin's introduction to all
this. Feel free to give a holler: sullivan@virginia.edu.
-/


/-
Ok, so you've see that Lean is a proof assistant. But
there's more! It's not just a proof assistant, it's a
complete very usable functional programming language.
What it lacks in libraries it makes up, over languages
such as OCaml and Haskell, by *also* being a world-class
proof assistant. From now on you can build systems in
a cool language with both programming and foundational
verification facilities.
-/

def main : IO Unit :=
  IO.println s!"Hi!"

/-
You can run the main routine right here by using eval.
Hover over the #eval to see the result of its execution.
The {hello} string is defined in Cs2120f24/Welcome.lean.
-/

#eval main

/-
You can also compile and run it as an executable.
See the documentation for the *lake* command of the
Lean4 system.
-/
