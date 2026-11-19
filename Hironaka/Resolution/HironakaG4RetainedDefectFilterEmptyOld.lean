import Hironaka.Resolution.HironakaG4OrderedCrestEmptyOld
import Hironaka.Resolution.HironakaG8BFamilyPad
import Hironaka.Resolution.HironakaG3SNCListPermutation
import Hironaka.Resolution.HironakaG4OrderedCrestEmptyBorn

/-! The actual retained defect is unchanged after filtering all empty old
and born slots in their respective orders. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4RetainedDefectFilterEmptyOld

noncomputable section
attribute [local instance] Classical.propDecidable

open Hironaka.BlowupSequences BlowupTowers NormalCrossings
  NormalCrossingsComparison HironakaG4PreparedCentreCoordinates HironakaG4OrderedCrestEmptyOld
  HironakaG4OrderedCrestEmptyBorn HironakaSharpActualChronologicalDistinctDefect
  HironakaOriginalBoundaryEmptyFilterComparison

variable {n : ℕ} {X : CMfd.{u} n}

/-- The actual defect uses the same proper germ classes and the same order
after any number of empty old slots have been removed. -/
theorem actualFamilyDistinctDefect_filter_empty_old (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hDense : N ⊆ closure (N \ ⋃ H ∈ old ++ born, H)) :
    actualFamilyDistinctDefect N (oldResidualPart N (old.filter fun H => decide H.Nonempty) born) =
      actualFamilyDistinctDefect N (oldResidualPart N old born) := by
  let valid (L : List (Set X)) :=
    IsSNCDivisor n (L ++ born) ∧ N ⊆ closure (N \ ⋃ H ∈ L ++ born, H)
  let defect (L : List (Set X)) :=
    actualFamilyDistinctDefect N (oldResidualPart N L born)
  let V (L : List (Set X)) : Set X := if valid L then defect L else ∅
  have hStep (L : List (Set X)) (k : ℕ) (hk : k ≤ L.length) :
      V (L.insertIdx k ∅) = V L := by
    let hPerm := (List.perm_insertIdx (∅ : Set X) L hk).append_right born
    have hUnion : (⋃ H ∈ L.insertIdx k ∅ ++ born, H) = ⋃ H ∈ L ++ born, H := by
      ext x
      simp only [mem_iUnion, exists_prop, hPerm.mem_iff, List.cons_append, List.mem_cons]
      constructor
      · rintro ⟨H, hH | hH, hx⟩
        · subst H
          exact hx.elim
        · exact ⟨H, hH, hx⟩
      · rintro ⟨H, hH, hx⟩
        exact ⟨H, Or.inr hH, hx⟩
    have hValid : valid (L.insertIdx k ∅) ↔ valid L := by
      dsimp only [valid]
      rw [hUnion]
      refine and_congr_left' ⟨fun h => isSNCDivisor_of_sublist h
        ((List.sublist_insertIdx L k ∅).append_right born), fun h => ?_⟩
      exact HironakaG3SNCListPermutation.isSNCDivisor_of_perm
        (HironakaG8BFamilyPad.isSNCDivisor_cons_empty_iff.mpr h) hPerm
    by_cases h : valid L
    · dsimp only [V]
      rw [if_pos h, if_pos (hValid.mpr h)]
      exact actualFamilyDistinctDefect_insert_empty_old hn hN h.1 hTr h.2
        ⟨k, Nat.lt_succ_of_le hk⟩
    · dsimp only [V]
      rw [if_neg h, if_neg (mt hValid.mp h)]
  have hOld : valid old := ⟨hE, hDense⟩
  have hFiltered : valid (old.filter fun H => decide H.Nonempty) := by
    have hSub : ((old.filter fun H => decide H.Nonempty) ++ born).Sublist (old ++ born) :=
      List.filter_sublist.append_right born
    refine ⟨isSNCDivisor_of_sublist hE hSub, hDense.trans (closure_mono ?_)⟩
    intro x hx
    refine ⟨hx.1, fun h => hx.2 ?_⟩
    simp only [mem_iUnion, exists_prop] at h ⊢
    obtain ⟨H, hH, hxH⟩ := h
    exact ⟨H, hSub.subset hH, hxH⟩
  simpa only [V, if_pos hOld, if_pos hFiltered, defect] using
    filter_value_of_empty_insertion V hStep old

/-- Both boundary roles admit removal of all empty slots at once, retaining
the original chronology of the nonempty members of each role. -/
theorem actualFamilyDistinctDefect_filter_empty_boundaries (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hDense : N ⊆ closure (N \ ⋃ H ∈ old ++ born, H)) :
    actualFamilyDistinctDefect N (oldResidualPart N
        (old.filter fun H => decide H.Nonempty) (born.filter fun H => decide H.Nonempty)) =
      actualFamilyDistinctDefect N (oldResidualPart N old born) := by
  rw [oldResidualPart_filter_empty_born]
  exact actualFamilyDistinctDefect_filter_empty_old hn hN hE hTr hDense

end
end Hironaka.HironakaG4RetainedDefectFilterEmptyOld
