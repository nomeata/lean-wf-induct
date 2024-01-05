Induction principles from well-founded function definitions
===========================================================

In this repository I am prototyping a tool that takes a (well-founded)
recursive function definition in Lean4, and derive a custom tailored induction
principle that follows that function's execution paths.

Examples:

```lean
def ackermann : (Nat × Nat) → Nat
  | (0, m) => m + 1
  | (n+1, 0) => ackermann (n, 1)
  | (n+1, m+1) => ackermann (n, ackermann (n + 1, m))
termination_by ackermann p => p

#derive_induction ackermann
#check ackermann.induct
```
produces
```lean
ackermann.induct (motive : Nat × Nat → Prop)
  (case1 : ∀ (m : Nat), motive (0, m))
  (case2 : ∀ (n : Nat), motive (n, 1) → motive (Nat.succ n, 0))
  (case3 :
    ∀ (n m : Nat),
      motive (n, ackermann (n + 1, m)) →
      motive (n + 1, m) →
      motive (Nat.succ n, Nat.succ m))
  (x : Nat × Nat) : motive x
```
and
```lean
inductive Tree
  | node : List Tree → Tree

def Tree.rev : Tree → Tree
  | node ts => .node (ts.attach.map (fun ⟨t, _ht⟩ => t.rev) |>.reverse)
```
produces
```lean
Tree.rev.induct (motive : Tree → Prop)
  (case1 : ∀ (ts : List Tree),
    (∀ (t : Tree), t ∈ ts → motive t) →
    motive (Tree.node ts))
  (x : Tree) : motive x
```

This is work in progress, so do not use this in production yet.

I am interested in interesting and small test cases. Just talk to me (Joachim Breitner) on zulip.