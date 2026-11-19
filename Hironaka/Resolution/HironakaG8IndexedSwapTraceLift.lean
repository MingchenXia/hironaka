import Hironaka.Resolution.HironakaG8NestedVisibleWordLift

set_option autoImplicit false
namespace Hironaka.HironakaG8IndexedSwapTraceLift

open HironakaG8FiniteSpatialOrdering HironakaG8NestedVisibleWordLift

/-- Read a pointwise indexed exchange as a single actual list exchange. -/
theorem swapAt_of_getElem {α : Type*} {I : α → α → Prop} (i : ℕ)
    (l r : List α) (hLen : r.length = l.length) (hi : i + 1 < l.length)
    (hI : I l[i] l[i+1])
    (hSwap : ∀ (j : ℕ) (hj : j < r.length),
      r[j] = l[Equiv.swap i (i+1) j]'(by
        rw [hLen] at hj
        by_cases h0 : j = i
        · simpa [h0]
        by_cases h1 : j = i+1
        · simp [h1]; omega
        · simpa only [Equiv.swap_apply_of_ne_of_ne h0 h1])) :
    SwapAt I i l r := by
  induction i generalizing l r with
  | zero =>
      obtain _ | ⟨a, _ | ⟨b, s⟩⟩ := l <;> simp at hi
      obtain _ | ⟨c, _ | ⟨d, t⟩⟩ := r <;> simp at hLen
      have hc : c = b := by
        have hs := hSwap 0 (by simp)
        simp only [Equiv.swap_apply_left] at hs
        exact hs
      have hd : d = a := by
        have hs := hSwap (0+1) (by simp)
        simp only [Equiv.swap_apply_right] at hs
        exact hs
      have ht : t = s := by
        apply List.ext_getElem hLen
        intro j hj hk
        have hs := hSwap (j+2) (by simp; omega)
        simpa only [Equiv.swap_apply_of_ne_of_ne (by omega : j+2 ≠ 0)
          (by omega : j+2 ≠ 0+1), List.getElem_cons_succ] using hs
      subst c d t
      exact .here hI
  | succ i ih =>
      obtain _ | ⟨a, l⟩ := l <;> simp at hi
      obtain _ | ⟨b, r⟩ := r <;> simp at hLen
      have hb : b = a := by
        have hs := hSwap 0 (by simp)
        simpa only [Equiv.swap_apply_of_ne_of_ne (by omega : 0 ≠ i+1)
          (by omega : 0 ≠ i+1+1), List.getElem_cons_zero] using hs
      subst b
      have hlt : i+1 < l.length := by omega
      refine SwapAt.later a (ih l r (by simpa using hLen) hlt hI ?_)
      intro j hj
      have hs := hSwap (j+1) (by simpa)
      have hEq : Equiv.swap (i+1) (i+1+1) (j+1) = Equiv.swap i (i+1) j + 1 := by
        by_cases h0 : j = i
        · simp [h0]
        by_cases h1 : j = i+1
        · simp [h1]
        rw [Equiv.swap_apply_of_ne_of_ne (by omega : j+1 ≠ i+1)
          (by omega : j+1 ≠ i+1+1), Equiv.swap_apply_of_ne_of_ne h0 h1]
      simpa only [hEq, List.getElem_cons_succ] using hs


open Set TopologicalSpace BlowupTowers HironakaG8OccupiedSlotComparison
  HironakaG8FirstFootprintOrder

/-- Exact indexed footprint data of a realized physical move. Each raw slot
of both towers is occupied, so equality of lengths follows from the readback. -/
def IndexedOccupiedReadback {n : ℕ} {X : CMfd.{0} n} (i : ℕ)
    (L M : TowerAt X) : Prop :=
  i+1 < L.2.length ∧
  Disjoint (slotFootprint L.2 i) (slotFootprint L.2 (i+1)) ∧
  (∀ j < L.2.length, (slotFootprint L.2 j).Nonempty) ∧
  (∀ j < M.2.length, (slotFootprint M.2 j).Nonempty) ∧
  ∀ j, slotFootprint M.2 j = slotFootprint L.2 (Equiv.swap i (i+1) j)

/-- An indexed exchange with exact occupied readback induces the exact
adjacent swap of footprint intersections on every open. -/
theorem indexed_readback_trace_swap {n : ℕ} {X : CMfd.{0} n} (U : Opens X)
    {i : ℕ} {L M : TowerAt X} (h : IndexedOccupiedReadback i L M) :
    SwapAt Disjoint i (footprintTraces U L) (footprintTraces U M) := by
  obtain ⟨hi,hDisj,hL,hM,hSwap⟩ := h
  have hMi : i+1 < M.2.length := by
    obtain ⟨x,hx⟩ := hL i (by omega)
    have : x ∈ slotFootprint M.2 (i+1) := by simpa only [hSwap,Equiv.swap_apply_right]
    exact hit_slot_lt_length M.2 this
  have hLen : M.2.length = L.2.length := by
    rcases lt_trichotomy M.2.length L.2.length with hlt | heq | hgt
    · obtain ⟨x,hx⟩ := hL M.2.length hlt
      have hm : x ∈ slotFootprint M.2 M.2.length := by
        simpa only [hSwap,Equiv.swap_apply_of_ne_of_ne (by omega : M.2.length ≠ i)
          (by omega : M.2.length ≠ i+1)]
      exact (Nat.lt_irrefl _ (hit_slot_lt_length M.2 hm)).elim
    · exact heq
    · obtain ⟨x,hx⟩ := hM L.2.length hgt
      have hl : x ∈ slotFootprint L.2 L.2.length := by
        simpa only [hSwap,Equiv.swap_apply_of_ne_of_ne (by omega : L.2.length ≠ i)
          (by omega : L.2.length ≠ i+1)] using hx
      exact (Nat.lt_irrefl _ (hit_slot_lt_length L.2 hl)).elim
  apply swapAt_of_getElem i _ _ (by simpa [footprintTraces,footprints]) (by simpa [footprintTraces,footprints])
  · simpa [footprintTraces,footprints] using
      hDisj.mono (inter_subset_left : slotFootprint L.2 i ∩ (U : Set X) ⊆ _)
        (inter_subset_left : slotFootprint L.2 (i+1) ∩ (U : Set X) ⊆ _)
  · intro j hj
    simp [footprintTraces,footprints,hSwap]


/-- The larger geometric move may retain extra data. Its exact indexed
footprints already provide the list-step readback needed by the nested lift. -/
theorem lift_indexed_occupied_word {n : ℕ} {X : CMfd.{0} n} (U : Opens X)
    (largeMove : ℕ → TowerAt X → TowerAt X → Prop)
    (smallMove : ℕ → TowerAt (CMfd.of (n := n) U) → TowerAt (CMfd.of (n := n) U) → Prop)
    (indexedRead : ∀ {i L M}, largeMove i L M → IndexedOccupiedReadback i L M)
    (nestedMove : ∀ {i L M S}, largeMove i L M → LiteralNestedTower U L S →
      footprintsIn S = (footprintTraces U L).filter visibleTrace →
      if ((footprintTraces U L)[i]?.any visibleTrace &&
          (footprintTraces U L)[i+1]?.any visibleTrace) then
        ∃ T, smallMove (((footprintTraces U L).take i).filter visibleTrace).length S T ∧
          LiteralNestedTower U M T ∧ footprintsIn T = (footprintTraces U M).filter visibleTrace
      else LiteralNestedTower U M S)
    {w : List ℕ} {L M : TowerAt X} (h : RealizedWord largeMove w L M)
    {S : TowerAt (CMfd.of (n := n) U)} (hComp : LiteralNestedTower U L S)
    (hRead : footprintsIn S = (footprintTraces U L).filter visibleTrace) :
    ∃ (v : List ℕ) (T : TowerAt (CMfd.of (n := n) U)), v.length ≤ w.length ∧
      RealizedWord smallMove v S T ∧ SwapWord Disjoint v (footprintsIn S) (footprintsIn T) ∧
      LiteralNestedTower U M T ∧ footprintsIn T = (footprintTraces U M).filter visibleTrace :=
  lift_nested_tower_word U largeMove smallMove
    (fun h => indexed_readback_trace_swap U (indexedRead h)) nestedMove h hComp hRead

end Hironaka.HironakaG8IndexedSwapTraceLift
