import WfInduct.Basic
import Std.Tactic.GuardMsgs


def notAFix : Bool := true

/-- error: Term true is not a fixF application -/
#guard_msgs in
derive_induction notAFix

/-- error: unknown constant 'doesNotExist' -/
#guard_msgs in
derive_induction doesNotExist
