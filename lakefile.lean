import Lake
open Lake DSL

package wfinduct where

-- require std from git "https://github.com/leanprover/std4" @ "lean-pr-testing-3230"
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "nightly-testing-2024-02-02"

@[default_target]
lean_lib «WfInduct» where
   globs := #[.andSubmodules `WfInduct]
