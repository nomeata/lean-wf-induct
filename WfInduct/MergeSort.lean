import WfInduct.Basic
import Std

def merge (r : α → α → Bool) : List α → List α → List α
  | [], l' => l'
  | l, [] => l
  | a :: l, b :: l' => if r a b then a :: merge r l (b :: l') else b :: merge r (a :: l) l'
  termination_by l₁ l₂ => l₁.length + l₂.length

#derive_induction merge

/--
info: merge.induct.{u_1} {α : Type u_1} (r : α → α → Bool) (motive : List α → List α → Prop)
  (case1 : ∀ (l' : List α), motive [] l') (case2 : ∀ (l : List α), (l = [] → False) → motive l [])
  (case3 : ∀ (a : α) (l : List α) (b : α) (l' : List α), r a b = true → motive l (b :: l') → motive (a :: l) (b :: l'))
  (case4 : ∀ (a : α) (l : List α) (b : α) (l' : List α), ¬r a b = true → motive (a :: l) l' → motive (a :: l) (b :: l'))
  (a✝a✝¹ : List α) : motive a✝ a✝¹
-/
#guard_msgs in
#check merge.induct

-- just a warmup
theorem perm_length (l : List α) (l' : List α) :
    (merge r l l').length = l.length + l'.length := by
  induction l, l' using merge.induct (r := r) -- NB: Needs lean4#3188
  case case1 => simp [merge]
  case case2 =>
    simp [merge] -- NB: ¬ (l = []) is provided, and used by simp
  case case3 a l b l' hr IH =>
    simp only [merge, hr, ↓reduceIte]
    simp_arith [IH]
  case case4 a l b l' hr IH =>
    simp only [merge, hr, ↓reduceIte]
    simp_arith [IH]
