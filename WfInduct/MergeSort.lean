import WfInduct.Basic
import Std

def merge (r : α → α → Prop) [DecidableRel r] : (l : List α) → (l' : List α) → List α
  | [], l' => l'
  | l, [] => l
  | a :: l, b :: l' => if r a b then a :: merge r l (b :: l') else b :: merge r (a :: l) l'
  termination_by l₁ l₂ => l₁.length + l₂.length

derive_induction merge

/--
info: merge.induct.{u_1} {α : Type u_1} (r : α → α → Prop) [inst✝ : DecidableRel r] (motive : List α → List α → Prop)
  (case1 : ∀ (l' : List α), motive [] l') (case2 : ∀ (l : List α), (l = [] → False) → motive l [])
  (case3 : ∀ (a : α) (l : List α) (b : α) (l' : List α), r a b → motive l (b :: l') → motive (a :: l) (b :: l'))
  (case4 : ∀ (a : α) (l : List α) (b : α) (l' : List α), ¬r a b → motive (a :: l) l' → motive (a :: l) (b :: l'))
  (x x : List α) : motive x x
-/
#guard_msgs in
#check merge.induct

theorem merge_length (r : α → α → Prop) [DecidableRel r] (l : List α) (l' : List α) :
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

open List in
theorem merge_perm (r : α → α → Prop) [DecidableRel r] (l l' : List α) : merge r l l' ~ l ++ l' := by
  induction l, l' using merge.induct (r := r)
  case case1 l => simp [merge]
  case case2 l overlap => simp [merge]
  case case3 a l b l' hr IH => simpa [merge, hr] using IH
  case case4 a l b l' hr IH =>
    suffices b :: merge r (a :: l) l' ~ a :: (l ++ b :: l') by simpa [merge, hr]
    exact (IH.cons _).trans ((Perm.swap _ _ _).trans (perm_middle.symm.cons _))

theorem merge_pairwise (r : α → α → Prop) [DecidableRel r]
    (trans : ∀ {a b c}, r a b → r b c → r a c)
    (total : ∀ a b, r a b ∨ r b a )
    {l l' : List α} (h₁ : l.Pairwise r) (h₂ : l'.Pairwise r) : (merge r l l').Pairwise r := by
  induction l, l' using merge.induct (r := r)
  case case1 l => simpa only [merge] using h₂
  case case2 l hoverlap => simpa only [merge] using h₁
  case case3 a l b l' hr IH =>
    suffices ∀ b' ∈ merge r l (b :: l'), r a b' by
      simpa [merge, hr, IH h₁.of_cons h₂]
    intro b' bm
    rcases show b' = b ∨ b' ∈ l ∨ b' ∈ l' by
        simpa [or_left_comm] using (merge_perm _ _ _).subset bm with
      (be | bl | bl')
    · subst b'
      assumption
    · exact List.rel_of_pairwise_cons h₁ bl
    · exact trans hr (List.rel_of_pairwise_cons h₂ bl')
  case case4 a l b l' hr IH =>
    suffices ∀ a' ∈ merge r (a :: l) l', r b a' by
      simpa [merge, hr, IH h₁ h₂.of_cons]
    replace hr : r b a := by cases total a b <;> [contradiction ; assumption]
    intro a' am
    rcases show a' = a ∨ a' ∈ l ∨ a' ∈ l' by
        simpa [or_right_comm] using (merge_perm _ _ _).subset am with
      (ae | al | al')
    · subst a'
      assumption
    · exact trans hr (List.rel_of_pairwise_cons h₁ al)
    · exact List.rel_of_pairwise_cons h₂ al'


@[simp]
def split (l : List α) : List α × List α :=
  (l.take (l.length / 2), l.drop (l.length / 2))

def mergeSort (r : α → α → Prop) [DecidableRel r] (l : List α) : List α :=
  let n := l.length
  if n < 2
    then l
  else
    merge r (mergeSort r (l.take (n/2))) (mergeSort r (l.drop (n/2)))
termination_by l.length
decreasing_by
 · simp_wf; simp only [Nat.min_def]; split <;> omega
 · simp_wf; omega

derive_induction mergeSort

/--
info: mergeSort.induct.{u_1} {α : Type u_1} (r : α → α → Prop) [inst✝ : DecidableRel r] (motive : List α → Prop)
  (case1 :
    ∀ (x : List α),
      let n := List.length x;
      n < 2 → motive x)
  (case2 :
    ∀ (x : List α),
      let n := List.length x;
      ¬n < 2 → motive (List.take (n / 2) x) → motive (List.drop (n / 2) x) → motive x)
  (x : List α) : motive x
-/
#guard_msgs in
#check mergeSort.induct

theorem List.pairwise_of_length_lt_2 {r : α → α → Prop} :
    ∀ {l : List α},  l.length < 2 → l.Pairwise r
  | [], _ => List.Pairwise.nil
  | [x], _ => by simp [List.Pairwise]
  | (_::_::_), h => by contradiction

theorem mergeSort_pairwise (r : α → α → Prop) [DecidableRel r]
    (trans : ∀ {a b c}, r a b → r b c → r a c)
    (total : ∀ a b, r a b ∨ r b a )
    {l : List α} : (mergeSort r l).Pairwise r := by
  induction l using  mergeSort.induct (r := r)
  case case1 l n =>
    intro h -- TODO: the induction tactic seems to miscount params, maybe due to the let
    unfold mergeSort; simp [h]
    exact List.pairwise_of_length_lt_2 h
  case case2 l n h IH₁ =>
    intro IH₂ -- TODO: the induction tactic seems to miscount params, maybe due to the let
    unfold mergeSort; simp [h]
    apply merge_pairwise r trans total IH₁ IH₂

open List in
theorem mergeSort_perm (r : α → α → Prop) [DecidableRel r] (l : List α) : mergeSort r l ~ l := by
  induction l using mergeSort.induct (r := r)
  case case1 l n =>
    intro h
    simp [mergeSort, h]
  case case2 l n h IH₁ =>
    intro IH₂
    unfold mergeSort; simp [h] -- simp [mergeSort] does not work well here
    apply (merge_perm _ _ _).trans
    apply (Perm.append IH₁ IH₂).trans
    simp only [take_append_drop, Perm.refl]
