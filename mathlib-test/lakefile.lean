import Lake
open Lake DSL

require wfinduct from ".."
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "nightly-testing-2024-02-02"

package «mathlib_test» where

@[default_target]
lean_lib «MathlibTest» where
