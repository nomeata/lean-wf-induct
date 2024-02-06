import WfInduct.Basic
import Std.Tactic.GuardMsgs
import Std.Tactic.OpenPrivate
import WfInduct.DelabPSigma

set_option autoImplicit false

universe u

inductive RBColor where
  | red
  | black

inductive RBNode (α : Type u) where
  | nil
  | node (c : RBColor) (l : RBNode α) (v : α) (r : RBNode α)

variable (α : Type u)

open RBColor
namespace RBNode

@[simp] def size : RBNode α → Nat
  | nil => 0
  | node _ x _ y => x.size + y.size + 1

-- Problem here:
-- The splitter has fewer alt parametrs than the matcher
-- when there are @-patterns involved.

def RBNode.append : RBNode α → RBNode α → RBNode α
  | nil, x | x, nil => x
  | node red a x b, node red c y d =>
    match append b c with
    | node red b' z c' => node red (node red a x b') z (node red c' y d)
    | bc               => node red a x (node .red bc y d)
  | node black a x b, node black c y d =>
    match append b c with
    | node red b' z c' => node red (node black a x b') z (node black c' y d)
    | bc               => node red a x (node black bc y d) -- removed balLeft
  | a@(node .black ..), node red b x c => node red (append a b) x c
  | node red a x b, c@(node black ..) => node red a x (append b c)
termination_by x y => x.size + y.size

set_option pp.proofs.withType false
set_option pp.match false
-- #derive_induction RBNode.append

/-

elab "#tmp" : command => Lean.Elab.Command.runTermElabM  fun _ => do
  if let some mi ← Lean.Meta.getMatcherInfo? `RBNode.RBNode.append.match_2 then
    Lean.logInfo m!"altnumParams: {mi.altNumParams}"
  let eqns ← Lean.Meta.Match.getEquationsFor `RBNode.RBNode.append.match_2
  Lean.logInfo m!"splitterAltNumParams: {eqns.splitterAltNumParams}"
#tmp

#check RBNode.RBNode.append.match_2
#check RBNode.RBNode.append.match_2.eq_5
#check RBNode.RBNode.append.match_2.splitter

theorem ex (n : Nat ): (match n with
  | 0 => 0
  | a@(Nat.succ _) => a) = n := by
  split
  sorry

#check ex.match_1.splitter

-/

namespace NoAsPattern

def RBNode.append : RBNode α → RBNode α → RBNode α
  | nil, x | x, nil => x
  | node red a x b, node red c y d =>
    match append b c with
    | node red b' z c' => node red (node red a x b') z (node red c' y d)
    | bc               => node red a x (node .red bc y d)
  | node black a x b, node black c y d =>
    match append b c with
    | node red b' z c' => node red (node black a x b') z (node black c' y d)
    | bc               => node red a x (node black bc y d) -- removed balLeft
  | (node .black z1 z2 z3), node red b x c => node red (append (node .black z1 z2 z3) b) x c
  | node red a x b, (node .black z1 z2 z3) => node red a x (append b (node .black z1 z2 z3))
termination_by x y => x.size + y.size

#derive_induction RBNode.append
/--
info: RBNode.NoAsPattern.RBNode.append.induct.{u} (α : Type u) (motive : RBNode α → RBNode α → Prop)
  (case1 : ∀ (x : RBNode α), motive nil x) (case2 : ∀ (x : RBNode α), (x = nil → False) → motive x nil)
  (case3 :
    ∀ (a : RBNode α) (x : α) (b c : RBNode α) (y : α) (d : RBNode α),
      motive b c → motive (node red a x b) (node red c y d))
  (case4 :
    ∀ (a : RBNode α) (x : α) (b c : RBNode α) (y : α) (d : RBNode α),
      motive b c → motive (node black a x b) (node black c y d))
  (case5 :
    ∀ (z1 : RBNode α) (z2 : α) (z3 b : RBNode α) (x : α) (c : RBNode α),
      motive (node black z1 z2 z3) b → motive (node black z1 z2 z3) (node red b x c))
  (case6 :
    ∀ (a : RBNode α) (x : α) (b z1 : RBNode α) (z2 : α) (z3 : RBNode α),
      motive b (node black z1 z2 z3) → motive (node red a x b) (node black z1 z2 z3))
  (x x : RBNode α) : motive x x
-/
#guard_msgs in
#check RBNode.append.induct

end NoAsPattern
