import WfInduct.Basic
import Std.Tactic.GuardMsgs

namespace Unary

def ackermann : (Nat × Nat) → Nat
  | (0, m) => m + 1
  | (n+1, 0) => ackermann (n, 1)
  | (n+1, m+1) => ackermann (n, ackermann (n + 1, m))
termination_by p => p

#derive_induction ackermann

/--
info: Unary.ackermann.induct (motive : Nat × Nat → Prop) (case1 : ∀ (m : Nat), motive (0, m))
  (case2 : ∀ (n : Nat), motive (n, 1) → motive (Nat.succ n, 0))
  (case3 : ∀ (n m : Nat), motive (n + 1, m) → motive (n, ackermann (n + 1, m)) → motive (Nat.succ n, Nat.succ m))
  (x : Nat × Nat) : motive x
-/
#guard_msgs in
#check ackermann.induct

end Unary

namespace Binary

def ackermann : Nat → Nat → Nat
  | 0, m => m + 1
  | n+1, 0 => ackermann n 1
  | n+1, m+1 => ackermann n (ackermann (n + 1) m)
termination_by n m => (n, m)
#derive_induction ackermann

/--
info: Binary.ackermann.induct (motive : Nat → Nat → Prop) (case1 : ∀ (m : Nat), motive 0 m)
  (case2 : ∀ (n : Nat), motive n 1 → motive (Nat.succ n) 0)
  (case3 : ∀ (n m : Nat), motive (n + 1) m → motive n (ackermann (n + 1) m) → motive (Nat.succ n) (Nat.succ m))
  (a✝a✝¹ : Nat) : motive a✝ a✝¹
-/
#guard_msgs in
#check ackermann.induct

end Binary

universe u
opaque _root_.List.attach : {α : Type u} → (l : List α) → List { x // x ∈ l }

inductive Tree | node : List Tree → Tree
def Tree.rev : Tree → Tree
  | node ts => .node (ts.attach.map (fun ⟨t, _ht⟩ => t.rev) |>.reverse)
#derive_induction Tree.rev

/--
info: Tree.rev.induct (motive : Tree → Prop)
  (case1 : ∀ (ts : List Tree), (∀ (t : Tree), t ∈ ts → motive t) → motive (Tree.node ts)) (x : Tree) : motive x
-/
#guard_msgs in
#check Tree.rev.induct


def fib : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n+2 => fib n + fib (n+1)
termination_by n => n

#derive_induction fib
/--
info: fib.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : motive 1)
  (case3 : ∀ (n : Nat), motive n → motive (n + 1) → motive (Nat.succ (Nat.succ n))) (x : Nat) : motive x
-/
#guard_msgs in
#check fib.induct

set_option linter.unusedVariables false in
def have_tailrec : Nat → Nat
  | 0 => 0
  | n+1 =>
    have h2 : n < n+1 := Nat.lt_succ_self n
    have_tailrec n
termination_by n => n
#derive_induction have_tailrec

/--
info: have_tailrec.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : ∀ (n : Nat), motive n → motive (Nat.succ n))
  (x : Nat) : motive x
-/
#guard_msgs in
#check have_tailrec.induct

set_option linter.unusedVariables false in
def have_non_tailrec : Nat → Nat
  | 0 => 0
  | n+1 =>
    Nat.succ <|
      have h2 : n < n+1 := Nat.lt_succ_self n
      have_non_tailrec n
termination_by n => n
#derive_induction have_non_tailrec

/--
info: have_non_tailrec.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : ∀ (n : Nat), motive n → motive (Nat.succ n))
  (x : Nat) : motive x
-/
#guard_msgs in
#check have_non_tailrec.induct

set_option linter.unusedVariables false in
def let_tailrec : Nat → Nat
  | 0 => 0
  | n+1 =>
    let h2 : n < n+1 := Nat.lt_succ_self n
    let_tailrec n
termination_by n => n
#derive_induction let_tailrec

/--
info: let_tailrec.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : ∀ (n : Nat), motive n → motive (Nat.succ n))
  (x : Nat) : motive x
-/
#guard_msgs in
#check let_tailrec.induct

set_option linter.unusedVariables false in
def let_non_tailrec : Nat → Nat
  | 0 => 0
  | n+1 =>
    Nat.succ <|
      let h2 : n < n+1 := Nat.lt_succ_self n
      let_non_tailrec n
termination_by n => n
#derive_induction let_non_tailrec

/--
info: let_non_tailrec.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : ∀ (n : Nat), motive n → motive (Nat.succ n))
  (x : Nat) : motive x
-/
#guard_msgs in
#check let_non_tailrec.induct


set_option linter.unusedVariables false in
def with_ite_tailrec : Nat → Nat
  | 0 => 0
  | n+1 =>
    if n % 2 = 0 then
      with_ite_tailrec n
    else
      with_ite_tailrec n
termination_by n => n
#derive_induction with_ite_tailrec

/--
info: with_ite_tailrec.induct (motive : Nat → Prop) (case1 : motive 0)
  (case2 : ∀ (n : Nat), n % 2 = 0 → motive n → motive (Nat.succ n))
  (case3 : ∀ (n : Nat), ¬n % 2 = 0 → motive n → motive (Nat.succ n)) (x : Nat) : motive x
-/
#guard_msgs in
#check with_ite_tailrec.induct


set_option linter.unusedVariables false in
def with_ite_non_tailrec : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 =>
    Nat.succ <|
      if n % 2 = 0 then
        with_ite_non_tailrec (n+1)
      else
        with_ite_non_tailrec n
termination_by n => n
#derive_induction with_ite_non_tailrec

/--
info: with_ite_non_tailrec.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : motive 1)
  (case3 : ∀ (n : Nat), motive (n + 1) → motive n → motive (Nat.succ (Nat.succ n))) (x : Nat) : motive x
-/
#guard_msgs in
#check with_ite_non_tailrec.induct

set_option linter.unusedVariables false in
def with_dite_non_tailrec (n : Nat) : Nat :=
  Nat.succ <|
    if h : n - 1 < n then
      with_dite_non_tailrec (n-1)
    else
      0
termination_by n
#derive_induction with_dite_non_tailrec

/--
info: with_dite_non_tailrec.induct (motive : Nat → Prop)
(case1 : ∀ (x : Nat), (x - 1 < x → motive (x - 1)) → motive x)
  (x : Nat) : motive x
-/
#guard_msgs in
#check with_dite_non_tailrec.induct

set_option linter.unusedVariables false in
def with_dite_tailrec (n : Nat) : Nat :=
    if h : n - 1 < n then
      with_dite_tailrec (n-1)
    else
      0
termination_by n
#derive_induction with_dite_tailrec

/--
info: with_dite_tailrec.induct (motive : Nat → Prop)
(case1 : ∀ (x : Nat), x - 1 < x → motive (x - 1) → motive x)
  (case2 : ∀ (x : Nat), ¬x - 1 < x → motive x) (x : Nat) : motive x
-/
#guard_msgs in
#check with_dite_tailrec.induct

set_option linter.unusedVariables false in
def with_match_tailrec : Nat → Nat
  | 0 => 0
  | n+1 =>
    match n % 2 with
    | 0 => with_match_tailrec n
    | _ => with_match_tailrec n
termination_by n => n
#derive_induction with_match_tailrec

/--
info: with_match_tailrec.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : ∀ (n : Nat), motive n → motive (Nat.succ n))
  (x : Nat) : motive x
-/
#guard_msgs in
#check with_match_tailrec.induct


set_option linter.unusedVariables false in
def with_match_non_tailrec : Nat → Nat
  | 0 => 0
  | n+1 =>
  Nat.succ <|
    match n % 2 with
    | 0 => with_match_non_tailrec n
    | _ => with_match_non_tailrec n
termination_by n => n
#derive_induction with_match_non_tailrec

/--
info: with_match_non_tailrec.induct (motive : Nat → Prop) (case1 : motive 0)
  (case2 : ∀ (n : Nat), motive n → motive (Nat.succ n)) (x : Nat) : motive x
-/
#guard_msgs in
#check with_match_non_tailrec.induct

def with_overlap : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | n+1 => with_overlap n
termination_by n => n
#derive_induction with_overlap

/--
info: with_overlap.induct (motive : Nat → Prop) (case1 : motive 0) (case2 : motive 1) (case3 : motive 2) (case4 : motive 3)
  (case5 : ∀ (n : Nat), (n = 0 → False) → (n = 1 → False) → (n = 2 → False) → motive n → motive (Nat.succ n))
  (x : Nat) : motive x
-/
#guard_msgs in
#check with_overlap.induct


namespace UnusedExtraParams

-- This test how unused fixed function parameters are handled.
-- See comment in the code

def unary (base : Nat) : Nat → Nat
  | 0 => base
  | n+1 => unary base n
termination_by n => n
#derive_induction unary

/--
info: UnusedExtraParams.unary.induct (base : Nat) (motive : Nat → Prop) (case1 : motive 0)
  (case2 : ∀ (n : Nat), motive n → motive (Nat.succ n)) (x : Nat) : motive x
-/
#guard_msgs in
#check unary.induct

def binary (base : Nat) : Nat → Nat → Nat
  | 0, m => base + m
  | n+1, m => binary base n m
termination_by n => n
#derive_induction binary

/--
info: UnusedExtraParams.binary.induct (base : Nat) (motive : Nat → Nat → Prop) (case1 : ∀ (m : Nat), motive 0 m)
  (case2 : ∀ (n m : Nat), motive n m → motive (Nat.succ n) m) (a✝a✝¹ : Nat) : motive a✝ a✝¹
-/
#guard_msgs in
#check binary.induct

end UnusedExtraParams
