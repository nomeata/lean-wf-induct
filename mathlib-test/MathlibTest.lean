import Mathlib
import WfInduct.Basic
import WfInduct.DelabPSigma
import Lean

open Lean Elab Meta Command

elab "derive_all_inductions" : command => runTermElabM fun _ => do
  logInfo "Running derive_all_inductions"
  let mut good := 0
  let mut bad := 0
  let mut seen : NameSet := {}
  for mod in WF.eqnInfoExt.toEnvExtension.getState (← getEnv) |>.importedEntries do
    for (_, eqnInfo) in mod do
      unless seen.contains eqnInfo.declNameNonRec do
        seen := seen.insert eqnInfo.declNameNonRec
        logInfo m!"Testing {eqnInfo.declNameNonRec}"
        -- IO.println s!"Testing {eqnInfo.declNameNonRec}"
        try
          deriveInduction eqnInfo.declNames[0]!
          -- logInfo m!"Derived {inductName} : {indentExpr (← getConstInfo inductName).type}"
          good := good + 1
        catch e =>
          logInfo m!"Failed to derive: {e.toMessageData}"
          bad := bad + 1
          pure ()
  logInfo m!"Successes {good}, failures {bad}"

derive_all_inductions
