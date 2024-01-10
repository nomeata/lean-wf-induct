import WfInduct.Basic
import Std.Data.Array.Basic
import Std.Tactic.GuardMsgs

set_option autoImplicit false

def ackermann : (Nat × Nat) → Nat
  | (0, m) => m + 1
  | (n+1, 0) => ackermann (n, 1)
  | (n+1, m+1) => ackermann (n, ackermann (n + 1, m))
termination_by ackermann p => p
#derive_induction ackermann

/--
info: ackermann.induct (motive : Nat × Nat → Prop) (case1 : ∀ (m : Nat), motive (0, m))
  (case2 : ∀ (n : Nat), motive (n, 1) → motive (Nat.succ n, 0))
  (case3 : ∀ (n m : Nat), motive (n + 1, m) → motive (n, ackermann (n + 1, m)) → motive (Nat.succ n, Nat.succ m))
  (x : Nat × Nat) : motive x
-/
#guard_msgs in
#check ackermann.induct

inductive Tree
  | node : List Tree → Tree

def Tree.rev : Tree → Tree
  | node ts => .node (ts.attach.map (fun ⟨t, _ht⟩ => t.rev) |>.reverse)

#derive_induction Tree.rev

/--
info: Tree.rev.induct (motive : Tree → Prop)
  (case1 : ∀ (ts : List Tree), (∀ (t : Tree), t ∈ ts → motive t) → motive (Tree.node ts)) (x : Tree) : motive x
-/
#guard_msgs in
#check Tree.rev.induct
