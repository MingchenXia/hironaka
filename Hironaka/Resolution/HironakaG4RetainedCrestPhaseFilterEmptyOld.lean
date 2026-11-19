import Hironaka.Resolution.HironakaG4RetainedCrestPhaseEmptyOld
import Hironaka.Resolution.HironakaOriginalBoundaryEmptyFilterComparison

/-! Filtering all empty old slots from a realized native retained crest. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators

universe u

namespace Hironaka.HironakaG4RetainedCrestPhaseFilterEmptyOld

noncomputable section
attribute [local instance] Classical.propDecidable

open Hironaka.BlowupSequences BlowupTowers NormalCrossings NormalCrossingsComparison
  HironakaG4OrderedCrestEmptyOld HironakaG4RetainedDefectRelativeDecrease
  HironakaG4RetainedCrestPhaseEmptyOld HironakaActualRetainedBoundaryJointStep
  HironakaOriginalBoundaryEmptyFilterComparison

variable {n : ℕ} {X Y : CMfd.{u} n} {hn : 0 < n}
  {N : Set X} {old born : List (Set X)} {T : BlowupTower X Y}

set_option maxHeartbeats 600000 in
/-- Deleting all literally empty old slots keeps their original nonempty
order and gives a native crest phase with the same physical tower, active
open, footprint, and canonical marked problem. -/
theorem exists_filterEmptyOldRetainedCrestPhase
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hDense : N ⊆ closure (N \ ⋃ H ∈ old ++ born, H))
    (P : RetainedDefectCrestPhase hn N old born T) (hFoot : P.footprint.Nonempty) :
    let O := old.filter fun H => decide H.Nonempty
    ∃ Q : RetainedDefectCrestPhase hn N O born T,
      Q.footprint = P.footprint ∧ Q.active = P.active ∧
        jointProfileMarked N O born (∑ i, Q.profile i) Q.inactive =
          jointProfileMarked N old born (∑ i, P.profile i) P.inactive := by
  let Valid (L : List (Set X)) :=
    IsSNCDivisor n (L ++ born) ∧ N ⊆ closure (N \ ⋃ H ∈ L ++ born, H)
  let mark {L : List (Set X)} (S : RetainedDefectCrestPhase hn N L born T) :=
    jointProfileMarked N L born (∑ i, S.profile i) S.inactive
  let R (L L' : List (Set X)) :=
    Valid L → Valid L' ∧ ∀ (S : RetainedDefectCrestPhase hn N L born T),
      S.footprint.Nonempty → ∃ Q : RetainedDefectCrestPhase hn N L' born T,
        Q.footprint = S.footprint ∧ Q.active = S.active ∧ mark Q = mark S
  have hRefl (L : List (Set X)) : R L L := fun h => ⟨h, fun S _ => ⟨S, rfl, rfl, rfl⟩⟩
  have hTrans {L₁ L₂ L₃ : List (Set X)} (h₁₂ : R L₁ L₂) (h₂₃ : R L₂ L₃) : R L₁ L₃ := by
    intro h₁
    obtain ⟨h₂, hLift₁₂⟩ := h₁₂ h₁
    obtain ⟨h₃, hLift₂₃⟩ := h₂₃ h₂
    refine ⟨h₃, fun S hS => ?_⟩
    obtain ⟨Q, hFoot₂, hOpen₂, hMark₂⟩ := hLift₁₂ S hS
    obtain ⟨S', hFoot₃, hOpen₃, hMark₃⟩ := hLift₂₃ Q (hFoot₂.symm ▸ hS)
    exact ⟨S', hFoot₃.trans hFoot₂, hOpen₃.trans hOpen₂, hMark₃.trans hMark₂⟩
  have hStep (L : List (Set X)) (k : ℕ) (hk : k ≤ L.length) :
      R (L.insertIdx k ∅) L := by
    let j : Fin (L.length + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
    change R (oldBoundaryInsert L j) L
    intro h
    have hSub : (L ++ born).Sublist (oldBoundaryInsert L j ++ born) :=
      (List.sublist_insertIdx L k ∅).append_right born
    have hUnion : (⋃ H ∈ L ++ born, H) ⊆ ⋃ H ∈ oldBoundaryInsert L j ++ born, H :=
      iUnion₂_subset fun H hH => subset_iUnion₂ (s := fun G _ => G) H (hSub.subset hH)
    have hValid : Valid L :=
      ⟨isSNCDivisor_of_sublist h.1 hSub, h.2.trans (closure_mono (sdiff_subset_sdiff_right hUnion))⟩
    refine ⟨hValid, fun S hS => ?_⟩
    exact ⟨removeEmptyOldRetainedCrestPhase hN hValid.1 hTr hValid.2 j S hS,
      removeEmptyOldRetainedCrestPhase_data hN hValid.1 hTr hValid.2 j S hS⟩
  exact (filter_rel_of_empty_insertion R hRefl hTrans hStep old ⟨hE, hDense⟩).2 P hFoot

end
end Hironaka.HironakaG4RetainedCrestPhaseFilterEmptyOld
