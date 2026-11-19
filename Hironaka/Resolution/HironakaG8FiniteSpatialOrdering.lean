import Mathlib.Data.List.Perm.Basic

set_option autoImplicit false
namespace Hironaka.HironakaG8FiniteSpatialOrdering

variable {α : Type*}

/-- An actual adjacent exchange in a finite list, recording its zero-based index. -/
inductive SwapAt (independent : α → α → Prop) : ℕ → List α → List α → Prop
  | here {a b : α} {s : List α} (h : independent a b) : SwapAt independent 0 (a::b::s) (b::a::s)
  | later {i : ℕ} {l m : List α} (a : α) (h : SwapAt independent i l m) :
    SwapAt independent (i+1) (a::l) (a::m)

/-- A word of executable adjacent exchanges, in chronological order. -/
inductive SwapWord (independent : α → α → Prop) : List ℕ → List α → List α → Prop
  | nil (l : List α) : SwapWord independent [] l l
  | cons {i : ℕ} {word : List ℕ} {l m t : List α}
      (h : SwapAt independent i l m) (tail : SwapWord independent word m t) :
      SwapWord independent (i::word) l t

theorem SwapWord.prepend {I : α → α → Prop} {w : List ℕ} {l m : List α}
    (h : SwapWord I w l m) (a : α) : SwapWord I (w.map Nat.succ) (a::l) (a::m) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (.later a h) ih

theorem SwapWord.append {I : α → α → Prop} {w₁ w₂ : List ℕ} {l m t : List α}
    (h₁ : SwapWord I w₁ l m) (h₂ : SwapWord I w₂ m t) :
    SwapWord I (w₁ ++ w₂) l t := by
  induction h₁ with
  | nil => exact h₂
  | cons h _ ih => exact .cons h (ih h₂)

private theorem move_to_front {I : α → α → Prop} (p s : List α) (a : α)
    (h : ∀ b ∈ p, I b a) :
    ∃ w, SwapWord I w (p ++ a::s) (a::(p ++ s)) := by
  induction p with
  | nil => exact ⟨[],.nil _⟩
  | cons b p ih =>
    obtain ⟨w,hw⟩ := ih (fun c hc => h c (by simp [hc]))
    exact ⟨_,(hw.prepend b).append (.cons (.here (h b (by simp))) (.nil _))⟩

/-- If both lists give orders of the same finite events, and the first
preserves the target order on every dependent pair, there is a finite
word of adjacent independent swaps between them. The target's strict
rank order rules out duplicate event labels. -/
theorem exists_swap_word_of_preserved_order {I : α → α → Prop} (rank : α → ℕ)
    {source target : List α} (hPerm : source.Perm target)
    (hSource : source.Pairwise (fun a b => I a b ∨ rank a < rank b))
    (hTarget : target.Pairwise (fun a b => rank a < rank b)) :
    ∃ w, SwapWord I w source target := by
  induction target generalizing source with
  | nil =>
    have hNil := hPerm.eq_nil
    subst source
    exact ⟨[],.nil _⟩
  | cons a t ih =>
    have ha : a ∈ source := hPerm.mem_iff.mpr (by simp)
    obtain ⟨p,s,rfl⟩ := List.append_of_mem ha
    have hStart := List.pairwise_append.mp hSource
    have hTail : (p ++ s).Pairwise (fun a b => I a b ∨ rank a < rank b) :=
      List.pairwise_append.mpr ⟨hStart.1,(List.pairwise_cons.mp hStart.2.1).2,
        fun b hb c hc => hStart.2.2 b hb c (by simp [hc])⟩
    have hMove : ∀ b ∈ p, I b a := by
      intro b hb
      refine (hStart.2.2 b hb a (by simp)).resolve_right ?_
      have hb' : b ∈ a::t := hPerm.mem_iff.mp (by simp [hb])
      rcases List.mem_cons.mp hb' with h | ht
      · subst b
        exact Nat.lt_irrefl _
      · exact Nat.not_lt_of_ge (Nat.le_of_lt ((List.pairwise_cons.mp hTarget).1 b ht))
    have htPerm : (p ++ s).Perm t := by
      apply (List.perm_cons a).mp
      exact (List.perm_middle (a := a) (l₁ := p) (l₂ := s)).symm.trans hPerm
    obtain ⟨w,hw⟩ := move_to_front p s a hMove
    obtain ⟨v,hv⟩ := ih htPerm hTail (List.pairwise_cons.mp hTarget).2
    exact ⟨_,hw.append (hv.prepend a)⟩

end Hironaka.HironakaG8FiniteSpatialOrdering
