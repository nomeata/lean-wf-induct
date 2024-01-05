import Lake
open Lake DSL

package «wf-induct» where

@[default_target]
lean_lib «WfInduct» where
   globs := #[.andSubmodules `WfInduct]
