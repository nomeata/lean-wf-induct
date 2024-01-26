import Mathlib
import WfInduct.Basic
import Lean

open Lean Elab Meta Command

elab "#derive_all_inductions" : command => runTermElabM fun _ => do
  logInfo "Running derive_all_inductions"
  for mod in WF.eqnInfoExt.toEnvExtension.getState (← getEnv) |>.importedEntries do
    for (_, eqnInfo) in mod do
      logInfo m!"Testing {eqnInfo.declNameNonRec}"
      -- IO.println s!"Testing {eqnInfo.declNameNonRec}"
      try
        let inductName ← deriveUnaryInduction eqnInfo.declNameNonRec
        logInfo m!"Derived {inductName}"
        -- logInfo m!" with type {indentExpr (← getConstInfo inductName).type}"
      catch e =>
        logInfo m!"Failed to derive: {e.toMessageData}"
        pure ()

  #derive_all_inductions
