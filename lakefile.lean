import Lake
open Lake DSL

package "mpctt" where
  -- add package configuration options here

lean_lib «Mpctt» where
  -- add library configuration options here

@[default_target]
lean_exe "mpctt" where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
