import Hironaka.Resolution.HironakaG4RetainedDefectRelativeDecrease
import Hironaka.Resolution.HironakaG4JointProfileEmptyOld

/-! Removing a literally empty old boundary slot from a realized retained crest. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators

universe u

namespace Hironaka.HironakaG4RetainedCrestPhaseEmptyOld

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers NormalCrossings HironakaG4OrderedDefectStamp
  HironakaG4OrderedCrestEmptyOld HironakaG4JointProfileEmptyOld
  HironakaG4RetainedDefectRelativeDecrease HironakaActualRetainedBoundaryJointStep

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Read the rank of a native enlarged stamp in the length-indexed inserted rows. -/
private theorem retainedDefectOrderedRank_insert_empty_old (N : Set X) {old : List (Set X)}
    (born : List (Set X)) (j : Fin (old.length + 1)) (x : X) :
    let S := retainedDefectStamp N old born x
    retainedDefectOrderedRank N (oldBoundaryInsert old j) born x =
      orderedDefectStampRank (j.insertNth 0 S.1) (S.2.map j.succAboveEmb) := by
  dsimp only
  obtain ⟨hr, hp⟩ := retainedDefectStamp_insert_empty_old N born j x
  exact orderedDefectStampRank_eq_of_ordered_cast (oldBoundaryInsert_length old j).symm
    _ _ _ _ (fun i => congrFun hr i) (by
      rw [hp, Finset.map_map]
      rfl)

/-- Removing one common empty old row preserves the ordering of actual native stamps. -/
theorem retainedDefectOrderedRank_le_insert_empty_old_iff (N : Set X) {old : List (Set X)}
    (born : List (Set X)) (j : Fin (old.length + 1)) {x y : X} :
    retainedDefectOrderedRank N (oldBoundaryInsert old j) born x ≤
      retainedDefectOrderedRank N (oldBoundaryInsert old j) born y ↔
    retainedDefectOrderedRank N old born x ≤ retainedDefectOrderedRank N old born y := by
  rw [retainedDefectOrderedRank_insert_empty_old N born j x,
    retainedDefectOrderedRank_insert_empty_old N born j y]
  exact orderedDefectStampRank_le_insert_zero_iff j

private theorem retainedDefectOrderedRank_eq_insert_empty_old_iff (N : Set X)
    {old : List (Set X)} (born : List (Set X)) (j : Fin (old.length + 1)) {x y : X} :
    retainedDefectOrderedRank N (oldBoundaryInsert old j) born x =
      retainedDefectOrderedRank N (oldBoundaryInsert old j) born y ↔
    retainedDefectOrderedRank N old born x = retainedDefectOrderedRank N old born y := by
  rw [le_antisymm_iff, le_antisymm_iff, retainedDefectOrderedRank_le_insert_empty_old_iff N born j,
    retainedDefectOrderedRank_le_insert_empty_old_iff N born j]

variable {hn : 0 < n} {N : Set X} {old born : List (Set X)} {T : BlowupTower X Y}

private theorem retainedCrestPhase_jointProfileMarked_eq_at
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hDense : N ⊆ closure (N \ ⋃ H ∈ old ++ born, H))
    (j : Fin (old.length + 1)) (P : RetainedDefectCrestPhase hn N (oldBoundaryInsert old j) born T)
    {x : X} (hx : x ∈ P.footprint) :
    let S := retainedDefectStamp N old born x
    jointProfileMarked N old born (∑ i, S.1 i) S.2 =
      jointProfileMarked N (oldBoundaryInsert old j) born (∑ i, P.profile i) P.inactive := by
  dsimp only
  let S := retainedDefectStamp N old born x
  let S' := retainedDefectStamp N (oldBoundaryInsert old j) born x
  have hStamp : S' = (P.profile, P.inactive) :=
    orderedDefectStamp_eq_of_rank_eq ((P.footprint_iff x).mp hx).2
  obtain ⟨hr, hp⟩ := retainedDefectStamp_insert_empty_old N born j x
  change (fun i => S'.1 (finCongr (oldBoundaryInsert_length old j).symm i)) =
    j.insertNth 0 S.1 at hr
  change S'.2 = S.2.map (oldBoundaryInsertEmb (old := old) j) at hp
  have hsum : (∑ i, S'.1 i) = ∑ i, S.1 i := by
    rw [← (finCongr (oldBoundaryInsert_length old j).symm).sum_comp S'.1, hr,
      Fin.sum_insertNth, zero_add]
  change jointProfileMarked N old born (∑ i, S.1 i) S.2 = _
  rw [← show S'.1 = P.profile from congrArg Prod.fst hStamp,
    ← show S'.2 = P.inactive from congrArg Prod.snd hStamp, hsum, hp]
  exact (jointProfileMarked_insertEmpty_old hn hN hE hTr hDense j _ _).symm

set_option maxHeartbeats 600000 in
/-- A nonempty retained crest admits the same physical phase and active marked
record after removing one originally empty old boundary slot. -/
def removeEmptyOldRetainedCrestPhase
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hDense : N ⊆ closure (N \ ⋃ H ∈ old ++ born, H))
    (j : Fin (old.length + 1)) (P : RetainedDefectCrestPhase hn N (oldBoundaryInsert old j) born T)
    (hFoot : P.footprint.Nonempty) : RetainedDefectCrestPhase hn N old born T := by
  let x := hFoot.some
  have hx : x ∈ P.footprint := hFoot.some_mem
  have hDefect := actualFamilyDistinctDefect_insert_empty_old hn hN hE hTr hDense j
  have hRank := ((P.footprint_iff x).mp hx).2
  let S := retainedDefectStamp N old born x
  refine { profile := S.1
           inactive := S.2
           footprint := P.footprint
           isClosed_footprint := P.isClosed_footprint
           active := P.active
           footprint_subset := P.footprint_subset
           centresOver := P.centresOver
           rank_bound := ?_
           footprint_iff := ?_
           active_record := ?_ }
  · intro y hy
    change retainedDefectOrderedRank N old born y ≤ retainedDefectOrderedRank N old born x
    apply (retainedDefectOrderedRank_le_insert_empty_old_iff N born j).mp
    rw [hRank]
    exact P.rank_bound y (hDefect.symm ▸ hy)
  · intro y
    change y ∈ P.footprint ↔ y ∈ _ ∧
      retainedDefectOrderedRank N old born y = retainedDefectOrderedRank N old born x
    rw [P.footprint_iff, hDefect, ← hRank, retainedDefectOrderedRank_eq_insert_empty_old_iff N born j]
  · dsimp only
    rw [retainedCrestPhase_jointProfileMarked_eq_at hN hE hTr hDense j P hx]
    exact P.active_record

/-- Removing the empty slot retains the literal active open, closed footprint,
and entire marked record. The tower is the same in the type of both phases. -/
theorem removeEmptyOldRetainedCrestPhase_data
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hDense : N ⊆ closure (N \ ⋃ H ∈ old ++ born, H))
    (j : Fin (old.length + 1)) (P : RetainedDefectCrestPhase hn N (oldBoundaryInsert old j) born T)
    (hFoot : P.footprint.Nonempty) :
    let Q := removeEmptyOldRetainedCrestPhase hN hE hTr hDense j P hFoot
    Q.footprint = P.footprint ∧ Q.active = P.active ∧
      jointProfileMarked N old born (∑ i, Q.profile i) Q.inactive =
        jointProfileMarked N (oldBoundaryInsert old j) born (∑ i, P.profile i) P.inactive :=
  ⟨rfl, rfl, retainedCrestPhase_jointProfileMarked_eq_at hN hE hTr hDense j P hFoot.some_mem⟩

end
end Hironaka.HironakaG4RetainedCrestPhaseEmptyOld
