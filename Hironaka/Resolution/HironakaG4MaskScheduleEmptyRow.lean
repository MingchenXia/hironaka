import Hironaka.Resolution.HironakaG4ProcessedMaskIncidenceOrder
import Mathlib.Data.List.Sort

/-! Inserting an absent old slot only inserts empty phases in the fixed
descending incidence schedule. -/

set_option autoImplicit false

namespace Hironaka.HironakaG4MaskScheduleEmptyRow

noncomputable section

open HironakaG4ProcessedMaskIncidenceOrder HironakaG4OrderedRowCode
  HironakaG4RelativeOrderedProcessedFinish

/-- Drop a padded mask if it selects the absent position, and otherwise
read its incident set through the original chronological indices. -/
def eraseAbsentMask {r : ℕ} (j : Fin (r+1)) (P : Finset (Fin (r+1))) : Option (Finset (Fin r)) :=
  if j ∈ P then none else some (Finset.univ.filter fun i => j.succAbove i ∈ P)

theorem eraseAbsentMask_eq_none_iff {r : ℕ} (j : Fin (r+1)) (P : Finset (Fin (r+1))) :
    eraseAbsentMask j P = none ↔ j ∈ P := by
  unfold eraseAbsentMask
  split <;> simp_all

theorem map_of_eraseAbsentMask_eq_some {r : ℕ} {j : Fin (r+1)}
    {P : Finset (Fin (r+1))} {Q : Finset (Fin r)} (h : eraseAbsentMask j P = some Q) :
    Q.map j.succAboveEmb = P := by
  have hj : j ∉ P := by
    intro hJ
    have hNone := (eraseAbsentMask_eq_none_iff j P).mpr hJ
    rw [hNone] at h
    contradiction
  have hQ : Finset.univ.filter (fun i => j.succAbove i ∈ P) = Q := by
    simpa [eraseAbsentMask,hj] using h
  rw [←hQ]
  ext i
  refine Fin.succAboveCases j ?_ (fun k => ?_) i
  · have hNone : j ∉ (Finset.univ.filter fun i => j.succAbove i ∈ P).map j.succAboveEmb := by
      rintro hMem
      obtain ⟨k,_hk,hEq⟩ := Finset.mem_map.mp hMem
      exact j.succAbove_ne k hEq
    simp [hNone,hj]
  · rw [show j.succAbove k = j.succAboveEmb k from rfl,Finset.mem_map']
    simp

theorem eraseAbsentMask_map {r : ℕ} (j : Fin (r+1)) (P : Finset (Fin r)) :
    eraseAbsentMask j (P.map j.succAboveEmb) = some P := by
  have hj : j ∉ P.map j.succAboveEmb := by
    rintro h
    obtain ⟨i,_hi,hEq⟩ := Finset.mem_map.mp h
    exact j.succAbove_ne i hEq
  simp only [eraseAbsentMask,if_neg hj,Option.some.injEq]
  ext i
  rw [Finset.mem_filter,show j.succAbove i = j.succAboveEmb i from rfl,Finset.mem_map']
  simp

private abbrev key {r : ℕ} (P : Finset (Fin r)) := orderedRowTieCode (fun _ => 0) P

private theorem key_le_map_iff {r : ℕ} (j : Fin (r+1)) (P Q : Finset (Fin r)) :
    key (P.map j.succAboveEmb) ≤ key (Q.map j.succAboveEmb) ↔ key P ≤ key Q := by
  have hZero : j.insertNth 0 (fun _ : Fin r => (0 : ℕ)) = (fun _ => 0) := by
    funext i
    refine Fin.succAboveCases j ?_ (fun k => ?_) i
    · exact Fin.insertNth_apply_same j _ _
    · exact Fin.insertNth_apply_succAbove j _ _ k
  simpa only [hZero] using
    (orderedRowTieCode_le_insert_zero_iff j
      (r := fun _ => 0) (s := fun _ => 0) (P := P) (Q := Q) rfl)

private theorem orderedMaskLevel_pairwise (r q : ℕ) :
    (orderedMaskLevel r q).Pairwise (fun P Q => key P ≤ key Q) := by
  unfold orderedMaskLevel
  simpa only [decide_eq_true_eq] using
    (List.pairwise_mergeSort (le := fun P Q : Finset (Fin r) => decide (key P ≤ key Q))
      (fun _ _ _ hPQ hQR => decide_eq_true ((of_decide_eq_true hPQ).trans (of_decide_eq_true hQR)))
      (fun P Q => by simpa only [Bool.or_eq_true,decide_eq_true_eq] using le_total (key P) (key Q))
      (((Finset.univ : Finset (Fin r)).powersetCard q).toList))

private theorem orderedMaskLevel_nodup (r q : ℕ) : (orderedMaskLevel r q).Nodup := by
  unfold orderedMaskLevel
  exact (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)

private theorem mem_orderedMaskLevel {r q : ℕ} (P : Finset (Fin r)) :
    P ∈ orderedMaskLevel r q ↔ P.card = q := by
  rw [←List.mem_toFinset,orderedMaskLevel_toFinset,Finset.mem_powersetCard]
  exact and_iff_right (Finset.subset_univ _)

/-- On each level the order of genuinely corresponding masks is exactly
unchanged by adding one absent old position. -/
theorem orderedMaskLevel_eraseAbsentMask {r : ℕ} (j : Fin (r+1)) (q : ℕ) :
    (orderedMaskLevel (r+1) q).filterMap (eraseAbsentMask j) = orderedMaskLevel r q := by
  have hSorted := (orderedMaskLevel_pairwise (r+1) q).filterMap (eraseAbsentMask j)
    (fun P P' h Q hQ Q' hQ' => (key_le_map_iff j Q Q').mp
      (by rwa [map_of_eraseAbsentMask_eq_some hQ,map_of_eraseAbsentMask_eq_some hQ']))
  have hNodup : ((orderedMaskLevel (r+1) q).filterMap (eraseAbsentMask j)).Nodup := by
    exact List.Nodup.filterMap (f := eraseAbsentMask j)
      (fun P P' Q hQ hQ' => (map_of_eraseAbsentMask_eq_some hQ).symm.trans
        (map_of_eraseAbsentMask_eq_some hQ')) (orderedMaskLevel_nodup (r+1) q)
  have hPerm : List.Perm ((orderedMaskLevel (r+1) q).filterMap (eraseAbsentMask j))
      (orderedMaskLevel r q) := (List.perm_ext_iff_of_nodup hNodup (orderedMaskLevel_nodup r q)).mpr fun Q => by
    rw [List.mem_filterMap,mem_orderedMaskLevel]
    constructor
    · rintro ⟨P,hP,hQ⟩
      have hCard := (mem_orderedMaskLevel P).mp hP
      rw [←map_of_eraseAbsentMask_eq_some hQ,Finset.card_map] at hCard
      exact hCard
    · intro hCard
      exact ⟨Q.map j.succAboveEmb,(mem_orderedMaskLevel _).mpr (by simpa only [Finset.card_map] using hCard),
        eraseAbsentMask_map j Q⟩
  exact List.Perm.eq_of_pairwise (le := fun P Q => key P ≤ key Q)
    (fun P Q _ _ hPQ hQP => (orderedRowTieCode_inj rfl (le_antisymm hPQ hQP)).2)
    hSorted (orderedMaskLevel_pairwise r q) hPerm

/-- Projection of the whole fixed descending schedule, including the
native singleton tail, is the smaller original schedule at the same cap. -/
theorem descendingMaskLabels_eraseAbsentMask {r : ℕ} (j : Fin (r+1)) :
    ∀ q, (descendingMaskLabels (orderedMaskLevel (r+1)) q).filterMap (eraseAbsentMask j) =
      descendingMaskLabels (orderedMaskLevel r) q
  | 0 => orderedMaskLevel_eraseAbsentMask j 1
  | 1 => orderedMaskLevel_eraseAbsentMask j 1
  | q+2 => by
    simp only [descendingMaskLabels,List.filterMap_append,orderedMaskLevel_eraseAbsentMask,
      descendingMaskLabels_eraseAbsentMask j (q+1)]

/-- A count above the number of available rows contributes no phase. -/
theorem orderedMaskLevel_eq_nil_of_lt {r q : ℕ} (h : r < q) :
    orderedMaskLevel r q = [] := by
  cases hL : orderedMaskLevel r q with
  | nil => rfl
  | cons P L =>
    have hMem : P ∈ orderedMaskLevel r q := hL.symm ▸ List.mem_cons_self
    have hCount : P.card = q := (mem_orderedMaskLevel P).mp hMem
    have hBound : P.card ≤ r := by
      simpa only [Fintype.card_fin] using Finset.card_le_univ P
    omega

/-- Raising any cap at or above the original old length has no effect on
the actual ordered list. -/
theorem descendingMaskLabels_eq_at_length {r q : ℕ} (h : r ≤ q) :
    descendingMaskLabels (orderedMaskLevel r) q =
      descendingMaskLabels (orderedMaskLevel r) r := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => rfl
  | succ k ih =>
    have hStep (p : ℕ) (hP : r ≤ p) :
        descendingMaskLabels (orderedMaskLevel r) (p+1) =
          descendingMaskLabels (orderedMaskLevel r) p := by
      cases p with
      | zero => rfl
      | succ p =>
        have hEmpty := orderedMaskLevel_eq_nil_of_lt (r := r) (q := p+2) (by omega)
        simp only [descendingMaskLabels,hEmpty,List.nil_append]
    exact (hStep (r+k) (by omega)).trans (ih (by omega))

/-- The canonical schedules on independently chosen caps at or above
their own old lengths have the same genuine masked phases, even when
one old list has an extra absent slot. -/
theorem descendingMaskLabels_eraseAbsentMask_of_caps {r q q' : ℕ}
    (j : Fin (r+1)) (hCap : r ≤ q) (hCap' : r+1 ≤ q') :
    (descendingMaskLabels (orderedMaskLevel (r+1)) q').filterMap (eraseAbsentMask j) =
      descendingMaskLabels (orderedMaskLevel r) q := by
  rw [descendingMaskLabels_eraseAbsentMask,
    descendingMaskLabels_eq_at_length (r := r) (q := q') (by omega),
    descendingMaskLabels_eq_at_length hCap]

end
end Hironaka.HironakaG4MaskScheduleEmptyRow
