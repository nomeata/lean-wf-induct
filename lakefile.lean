import Lake
open Lake DSL

package «wf-induct» where

require std from git "https://github.com/leanprover/std4" @ "main"

@[default_target]
lean_lib «WfInduct» where
   globs := #[.andSubmodules `WfInduct]
