import Lake
open Lake DSL


require Mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"

package matroidLinearProgramming {
  -- add package configuration options here
}

lean_lib MatroidLinearProgramming {
  -- add library configuration options here
}

@[default_target]
lean_exe matroidLinearProgramming {
  root := `Main
}
