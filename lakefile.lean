import Lake
open Lake DSL

package cube {
  -- add package configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib Cube {
  -- add library configuration options here
}
