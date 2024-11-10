import Lake
open Lake DSL

package «fOL» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"


require mathlib_extra from "/home/pthomas/Desktop/github/mathlib_extra/"


@[default_target]
lean_lib «FOL» {
  globs := #[.andSubmodules `FOL]
  -- add any library configuration options here
}
