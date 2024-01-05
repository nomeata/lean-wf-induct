import WfInduct.Basic

set_option autoImplicit false

def ackermann : (Nat × Nat) → Nat
  | (0, m) => m + 1
  | (n+1, 0) => ackermann (n, 1)
  | (n+1, m+1) => ackermann (n, ackermann (n + 1, m))
termination_by ackermann p => p

#derive_induction ackermann
#check ackermann.induct

inductive Tree
  | node : List Tree → Tree

def Tree.rev : Tree → Tree
  | node ts => .node (ts.attach.map (fun ⟨t, _ht⟩ => t.rev) |>.reverse)

#derive_induction Tree.rev
#check Tree.rev.induct
