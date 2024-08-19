import Lake
open Lake DSL

package «cs2120f24» where
  -- add package configuration options here

lean_lib «Cs2120f24» where
  -- add library configuration options here
  require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_exe «cs2120f24» where
  root := `Main
