import Lake
open Lake DSL

package «fOL» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"


require mathlib_extra from git
  "git@github.com:pthomas505/mathlib_extra.git"


@[default_target]
lean_lib «FOL» {
  globs := #[.andSubmodules `FOL]
  -- add any library configuration options here
}
