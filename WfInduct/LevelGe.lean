import Lean
import WfInduct.Basic
import WfInduct.DelabPSigma
import Std.Tactic.GuardMsgs

open Lean

set_option autoImplicit false

def levelGeq (u v : Lean.Level) : Bool :=
    u == v ||
    match u, v with
    | _,           .zero       => true
    | u,           .max v₁ v₂  => levelGeq u v₁ && levelGeq u v₂
    | .max u₁ u₂,  v           => levelGeq u₁ v || levelGeq u₂ v
    | u,           .imax v₁ v₂ => levelGeq u v₁ && levelGeq u v₂
    | .imax _  u₂, v           => levelGeq u₂ v
    | .succ u,     .succ v     => levelGeq u v
    | _, _ =>
      let v' := v.getLevelOffset
      (u.getLevelOffset == v' || v'.isZero)
      && u.getOffset ≥ v.getOffset
termination_by (u, v)

#derive_induction levelGeq

/--
info: levelGeq.induct (motive : Level → Level → Prop)
  (case1 :
    ∀ (fst snd : Level),
      (match fst, snd with
        | x, Level.zero => True
        | u, Level.max v₁ v₂ => motive u v₁ ∧ motive u v₂
        | Level.max u₁ u₂, v => motive u₁ v ∧ motive u₂ v
        | u, Level.imax v₁ v₂ => motive u v₁ ∧ motive u v₂
        | Level.imax a u₂, v => motive u₂ v
        | Level.succ u, Level.succ v => motive u v
        | x, x_1 => True) →
        motive fst snd)
  (u v : Level) : motive u v
-/
#guard_msgs in
#check levelGeq.induct
