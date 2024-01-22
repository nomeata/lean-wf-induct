import Std
import WfInduct.Basic

def rev {α} (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size / 2 then
    rev (arr.swap ⟨i, by omega⟩ ⟨arr.size - i - 1, by omega⟩) (i + 1)
  else
    arr
termination_by arr.size - i
decreasing_by simp_wf; omega

theorem size_rev {α} (arr : Array α) (i : Nat) : (rev arr i).size = arr.size := by
  unfold rev
  split
  · rw [size_rev _ _] -- fix for that in #3204
    rw [Array.size_swap]
  · rfl
termination_by arr.size - i
decreasing_by simp_wf; omega

-- #derive_induction size_rev._unary
