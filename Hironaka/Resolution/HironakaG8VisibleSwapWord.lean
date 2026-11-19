import Hironaka.Resolution.HironakaG8FiniteSpatialOrdering
import Hironaka.Resolution.HironakaG8CompressedVisibleAdjacency

set_option autoImplicit false
namespace Hironaka.HironakaG8VisibleSwapWord
open HironakaG8FiniteSpatialOrdering
variable {α : Type*} {I : α → α → Prop}

theorem swapAt_filter_exact (visible : α → Bool) {i : ℕ} {l m : List α}
    (h : SwapAt I i l m) :
    if (l[i]?.any visible && l[i+1]?.any visible) then
      SwapAt I ((l.take i).filter visible).length (l.filter visible) (m.filter visible)
    else l.filter visible = m.filter visible := by
  induction h with
  | @here a b s h =>
    cases ha : visible a <;> cases hb : visible b <;>
      simp [ha,hb,SwapAt.here h]
  | @later i l m a h ih =>
    simp only [List.getElem?_cons_succ, Nat.add_assoc, List.take_succ_cons]
    split at ih
    · rename_i hv
      rw [if_pos hv]
      cases ha : visible a
      · simpa [ha] using ih
      · simpa [ha] using SwapAt.later a ih
    · rename_i hv
      rw [if_neg hv,List.filter_cons,List.filter_cons,ih]

/-- Filtering to the visible events deletes exchanges with at most one
visible event and retains each surviving exchange at its filtered prefix index. -/
theorem swapWord_filter (visible : α → Bool) {w : List ℕ} {l m : List α}
    (h : SwapWord I w l m) :
    ∃ v : List ℕ, v.length ≤ w.length ∧ SwapWord I v (l.filter visible) (m.filter visible) := by
  induction h with
  | nil l => exact ⟨[], by simp, .nil _⟩
  | @cons i w l m t h _ ih =>
    obtain ⟨v,hLen,hWord⟩ := ih
    have hStep := swapAt_filter_exact visible h
    split at hStep
    · exact ⟨_::v,Nat.succ_le_succ hLen,.cons hStep hWord⟩
    · exact ⟨v,Nat.le_trans hLen (Nat.le_succ _),hStep.symm ▸ hWord⟩

open Set TopologicalSpace
open scoped Manifold ContDiff
open BlowupTowers BlowupTowerTransforms HironakaStageCenters
  HironakaG3EmptyAwareHistory HironakaG8CofinalOccupiedAncestry HironakaG8OccupiedSlotComparison
  HironakaG8CompressedVisibleAdjacency

/-- In an actual chart, the filter keeping the range of the compressed
restriction embedding is exactly the filter by traces that meet the open. -/
theorem filter_by_compressed_visibleSlots {n : ℕ} {X Y Z : CMfd.{0} n}
    (T : BlowupTower X Y) (U : Opens X) {Q : BlowupTower (CMfd.of (n := n) U) Z}
    {e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T U)}
    (hQ : StageCentres (fun _ C => C.Nonempty) Q)
    (h : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
      Q (restrict U T) e)
    (l : List {k // Occupied T k})
    [DecidablePred (fun k : {k // Occupied T k} => k ∈ Set.range (compressedVisibleSlots T U hQ h))]
    [DecidablePred (fun k : {k // Occupied T k} => (slotFootprint T k.val ∩ (U : Set X)).Nonempty)] :
    l.filter (fun k => decide (k ∈ Set.range (compressedVisibleSlots T U hQ h))) =
      l.filter (fun k => decide (slotFootprint T k.val ∩ (U : Set X)).Nonempty) := by
  congr 1
  funext k
  exact Bool.eq_iff_iff.mpr (by
    simpa only [decide_eq_true_eq] using compressedVisibleSlots_range T U hQ h k.property)

end Hironaka.HironakaG8VisibleSwapWord

#print axioms Hironaka.HironakaG8VisibleSwapWord.swapAt_filter_exact
#print axioms Hironaka.HironakaG8VisibleSwapWord.swapWord_filter

#print axioms Hironaka.HironakaG8VisibleSwapWord.filter_by_compressed_visibleSlots
