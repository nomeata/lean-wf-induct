import WfInduct.Basic

universe uu

variable {α : Type uu} (r : α → α → Prop) [DecidableRel r]

local infixl:50 " ≼ " => r

open List

namespace Unary

def merge : List α × List α → List α
  | ([], l') => l'
  | (l, []) => l
  | (a :: l, b :: l') => if a ≼ b then a :: merge (l, b :: l') else b :: merge (a :: l, l')
  termination_by merge l => length l.1 + length l.2

-- set_option pp.raw true
-- set_option pp.proofs.withType false
#derive_induction merge
#check merge.induct

-- just a warmup
theorem perm_length (l) : length (merge r l) = length l.1 + length l.2 := by
  -- TODO: induction principle does not take extra parameters like r
  induction l using merge.induct -- (r := r)
  case r a b => exact r a b
  case inst inst => exact inst
  case case1 => simp [merge]
  case case2 =>
    simp [merge]
    rw [merge._eq_2]
    · sorry -- TODO: Need overlapping information to apply equation
  case case3 a l b l' hr IH =>
    -- TODO: simp [merge] nees the hr hypothesis
    simp [merge, hr, IH]
    simp_arith
  case case4 a l b l' hr IH =>
    -- TODO: simp [merge] nees the hr hypothesis
    simp [merge, hr, IH]
    simp_arith

/-
theorem perm_merge : ∀ l l' : List α, merge r l l' ~ l ++ l'
  | [], [] => by simp [merge]
  | [], b :: l' => by simp [merge]
  | a :: l, [] => by simp [merge]
  | a :: l, b :: l' => by
    by_cases h : a ≼ b
    · simpa [merge, h] using perm_merge _ _
    · suffices b :: merge r (a :: l) l' ~ a :: (l ++ b :: l') by simpa [merge, h]
      exact ((perm_merge _ _).cons _).trans ((swap _ _ _).trans (perm_middle.symm.cons _))
  termination_by perm_merge l₁ l₂ => length l₁ + length l₂
  -/


end Unary

namespace Binary

def merge : List α → List α → List α
  | [], l' => l'
  | l, [] => l
  | a :: l, b :: l' => if a ≼ b then a :: merge l (b :: l') else b :: merge (a :: l) l'
  termination_by merge l₁ l₂ => length l₁ + length l₂
-- #derive_induction merge._unary

end Binary
