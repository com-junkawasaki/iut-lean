import Lake
open Lake DSL

package «iut-lean» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib «IutLean» where
