import Std
import WfInduct.Basic

def rev {α} (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size / 2 then
    rev (arr.swap ⟨i, by omega⟩ ⟨arr.size - i - 1, by omega⟩) (i + 1)
  else
    arr
termination_by arr.size - i
decreasing_by simp_wf; omega

namespace Manual

theorem size_rev {α} (arr : Array α) (i : Nat) : (rev arr i).size = arr.size := by
  /-
  if h : i < arr.size / 2 then
    -- can we unfold nicely here?
  else
    done
  -/
  unfold rev
  split
  · rw [size_rev _ _] -- fix for that in #3204
    rw [Array.size_swap]
  · rfl
termination_by arr.size - i
decreasing_by simp_wf; omega

end Manual

#derive_induction rev

/--
info: rev.induct.{u_1} {α : Type u_1} (motive : Array α → Nat → Prop)
  (case1 :
    ∀ (fst : Array α) (snd : Nat) (h : snd < Array.size fst / 2),
      motive
          (Array.swap fst { val := snd, isLt := (_ : snd < Array.size fst) }
            { val := Array.size fst - snd - 1, isLt := (_ : Array.size fst - snd - 1 < Array.size fst) })
          (snd + 1) →
        motive fst snd)
  (case2 : ∀ (fst : Array α) (snd : Nat), ¬snd < Array.size fst / 2 → motive fst snd) (arr : Array α) (i : Nat) :
  motive arr i
-/
#guard_msgs in
#check rev.induct

theorem size_rev {α} (arr : Array α) (i : Nat) : (rev arr i).size = arr.size := by
  induction arr, i using rev.induct
  case case1 arr i h IH =>
    -- this unfolding does not work nicely
    rw [rev]
    simp only [h, ↓reduceDite]
    -- but now its pretty
    simp [IH]
  case case2 arr i h =>
    rw [rev]
    simp only [h, ↓reduceDite]
    -- the simp even solves it
    done
