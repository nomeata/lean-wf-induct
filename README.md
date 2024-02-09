Induction principles from well-founded function definitions
===========================================================

In this repository I am prototyping a tool that takes a (well-founded)
recursive function definition in Lean4, and derive a custom tailored induction
principle that follows that function's execution paths.

Examples:

```lean
def ackermann : Nat → Nat → Nat
  | 0, m => m + 1
  | n+1, 0 => ackermann n 1
  | n+1, m+1 => ackermann n (ackermann (n + 1) m)
```
produces
```lean
ackermann.induct (motive : Nat → Nat → Prop) (case1 : ∀ (m : Nat), motive 0 m)
  (case2 : ∀ (n : Nat), motive n 1 → motive (Nat.succ n) 0)
  (case3 : ∀ (n m : Nat), motive (n + 1) m → motive n (ackermann (n + 1) m) → motive (Nat.succ n) (Nat.succ m))
  (x x : Nat) : motive x x
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

Implementation
--------------

The idea of the implemenation is to take the final function definition (in terms of `WellFounded.fix`), which has all the decreasing proofs in it, and rewrite that definition into one that proves the desired induction principle. The steps are

* Unfold the definition to expose the `WellFounded.fixF` function.
* Construct a suitable `motive`.
* Replace its argument (with the `oldIH` argument) as follows:
* For every recursive call (i.e. call to `oldIH`) we replace it with a call to
  the original function.
* Also, for every call to `oldIH`, we pass its argument o `newIH` to construct the induction 
  hypothesis for this recursive call.
* For top-level matches
  * check if it is refining the  `oldIH`; if it is, replace that with `newIH`.
  * use the splitter, if present, to get extra assumptions for overlapping matches
  * keep the match application
* In the branches of the top-level matches
  * Create a hole with the (refined) `motive`.
  * Pass all induction hypothese to that hole
* Finally, abstract over all these holes.
* Profit.
