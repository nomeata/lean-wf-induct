import WfInduct.Basic

universe uu


namespace Unary

def merge (r : α → α → Bool) : List α × List α → List α
  | ([], l') => l'
  | (l, []) => l
  | (a :: l, b :: l') => if r a b then a :: merge r (l, b :: l') else b :: merge r (a :: l, l')
  termination_by merge r l => l.1.length + l.2.length

-- set_option pp.raw true
-- set_option pp.proofs.withType false

#derive_induction merge
#check merge.induct


/-
theorem merge.induct1 {α : Type uu} (r : α → α → Prop) [DecidableRel r] (motive : List α × List α → Prop)
  (case1 : ∀ (l' : List α), motive ([], l'))
  (case2 : ∀ (l : List α), ¬ (l = []) → motive (l, []))
  (case3 : ∀ (a : α) (l : List α) (b : α) (l' : List α), r a b → motive (l, b :: l') → motive (a :: l, b :: l'))
  (case4 : ∀ (a : α) (l : List α) (b : α) (l' : List α), ¬r a b → motive (a :: l, l') → motive (a :: l, b :: l'))
  (x : List α × List α) : motive x := sorry

#check @merge.induct = @merge.induct1

theorem merge.induct2 {α : Type uu} (r : α → α → Prop) (motive : (r : α → α → Prop) → (DecidableRel r) → List α × List α → Prop)
  (case1 : ∀  [DecidableRel r] (l' : List α), motive r ‹_› ([], l'))
  (case2 : ∀  [DecidableRel r] (l : List α), ¬ (l = []) →  motive r ‹_› (l, []))
  (case3 : ∀  [DecidableRel r] (a : α) (l : List α) (b : α) (l' : List α), r a b → motive r ‹_› (l, b :: l') → motive r ‹_› (a :: l, b :: l'))
  (case4 : ∀ [DecidableRel r] (a : α) (l : List α) (b : α) (l' : List α), ¬r a b → motive r ‹_› (a :: l, l') → motive r ‹_› (a :: l, b :: l'))
  (dr : DecidableRel r) (x : List α × List α)  : motive r ‹_› x := sorry

theorem merge.induct3 {α : Type uu} (r : α → α → Prop) (motive : (r : α → α → Prop) → List α × List α → Prop)
  (case1 : ∀  [DecidableRel r] (l' : List α), motive r ([], l'))
  (case2 : ∀  [DecidableRel r] (l : List α), ¬ (l = []) →  motive r (l, []))
  (case3 : ∀  [DecidableRel r] (a : α) (l : List α) (b : α) (l' : List α), r a b → motive r (l, b :: l') → motive r (a :: l, b :: l'))
  (case4 : ∀ [DecidableRel r] (a : α) (l : List α) (b : α) (l' : List α), ¬r a b → motive r (a :: l, l') → motive r (a :: l, b :: l'))
  (x : List α × List α) : motive r x := sorry
-/

-- just a warmup
theorem perm_length (l : List α × List α) : (merge r l).length = l.1.length + l.2.length := by
  induction l using merge.induct
  case r x y => exact r x y -- TODO: Allow merge.induct (r := r)
  case case1 => simp [merge]
  case case2 => simp [merge] -- NB: ¬ (l = []) is provided, and used by simp
  case case3 a l b l' hr IH =>
    simp [merge, hr, IH]
    simp_arith
  case case4 a l b l' hr IH =>
    simp [merge, hr, IH]
    simp_arith

-- #check Unary.merge._eq_3

end Unary


namespace Binary

def merge (r : α → α → Bool): List α → List α → List α
  | [], l' => l'
  | l, [] => l
  | a :: l, b :: l' => if r a b then a :: merge r l (b :: l') else b :: merge r (a :: l) l'
  termination_by merge r l₁ l₂ => l₁.length + l₂.length
-- #derive_induction merge._unary

end Binary
