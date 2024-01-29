import Lean
import WfInduct.Basic
import WfInduct.DelabPSigma
import Std.Tactic.GuardMsgs

open Lean

set_option autoImplicit false

namespace Original

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

-- TODO: Refining through matcherApps even in non-tail-positions

set_option pp.proofs.withType false
#derive_induction levelGeq

end Original

namespace Easier

def levelGeq (u v : Lean.Level) : Bool :=
    if u == v then true else
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

-- TODO: How to feed fst ≠ snd through the matcher refinement?

/--
info: Easier.levelGeq.induct (motive : Level → Level → Prop)
  (case1 : ∀ (fst snd : Level), (fst == snd) = true → motive fst snd) (case2 : ∀ (x : Level), motive x Level.zero)
  (case3 : ∀ (u v₁ v₂ : Level), motive u v₁ → motive u v₂ → motive u (Level.max v₁ v₂))
  (case4 :
    ∀ (u₁ u₂ v : Level),
      (v = Level.zero → False) →
        (∀ (v₁ v₂ : Level), v = Level.max v₁ v₂ → False) → motive u₁ v → motive u₂ v → motive (Level.max u₁ u₂) v)
  (case5 :
    ∀ (u v₁ v₂ : Level),
      (∀ (u₁ u₂ : Level), u = Level.max u₁ u₂ → False) → motive u v₁ → motive u v₂ → motive u (Level.imax v₁ v₂))
  (case6 :
    ∀ (a u₂ v : Level),
      (v = Level.zero → False) →
        (∀ (v₁ v₂ : Level), v = Level.max v₁ v₂ → False) →
          (∀ (v₁ v₂ : Level), v = Level.imax v₁ v₂ → False) → motive u₂ v → motive (Level.imax a u₂) v)
  (case7 : ∀ (u v : Level), motive u v → motive (Level.succ u) (Level.succ v))
  (case8 :
    ∀ (x x_1 : Level),
      (x_1 = Level.zero → False) →
        (∀ (v₁ v₂ : Level), x_1 = Level.max v₁ v₂ → False) →
          (∀ (u₁ u₂ : Level), x = Level.max u₁ u₂ → False) →
            (∀ (v₁ v₂ : Level), x_1 = Level.imax v₁ v₂ → False) →
              (∀ (a u₂ : Level), x = Level.imax a u₂ → False) →
                (∀ (u v : Level), x = Level.succ u → x_1 = Level.succ v → False) → motive x x_1)
  (u v : Level) : motive u v
-/
#guard_msgs in
#check levelGeq.induct

end Easier
