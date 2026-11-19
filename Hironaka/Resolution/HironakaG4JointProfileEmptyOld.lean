import Hironaka.Resolution.HironakaG4JointProfileEmptyBorn
import Hironaka.Resolution.HironakaG4OrderedCrestEmptyOld
import Hironaka.Resolution.HironakaG34JointMaskEquivariance
import Hironaka.Resolution.FactorizationFromResolution

/-! Exact native joint masks under insertion of a literal empty old row. -/

set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4JointProfileEmptyOld
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaActualFiniteMarkedSumHistories HironakaG34JointMaskEquivariance
  HironakaActualRetainedBoundaryJointStep HironakaG4PreparedCentreCoordinates
  HironakaG4JointProfileEmptyBorn HironakaG4OrderedCrestEmptyOld
  FactorizationFromResolution MonomialInvariantEmptyMember NormalCrossings
  RelativePrincipalizationSpan RestrictedIdealExtension InvertibleIdealQuotient IdealWeightPowers

variable {n : ℕ} {X : CMfd.{u} n}

private theorem finiteSum_mark_one_mem_iff (A : MarkedIdeal n X) (L : List (MarkedIdeal n X))
    (hA : A.ideal.IsCoherent ∧ A.d = 1)
    (hL : ∀ B ∈ L, B.ideal.IsCoherent ∧ B.d = 1)
    (x : X) (g : X → ℂ) :
    (finiteSum A L).ideal.mem x g ↔
      IsInSpanAt (n := n) (fun f => ∃ B ∈ A :: L, B.ideal.mem x f) x g := by
  induction L generalizing A g with
  | nil =>
    change A.ideal.mem x g ↔ IsInSpanAt (n := n) (fun f => ∃ B ∈ [A], B.ideal.mem x f) x g
    constructor
    · intro hg
      exact isInSpanAt_self ⟨A,List.mem_singleton_self A,hg⟩ (GermIdeal.IsCoherent.holomorphicAt_mem hA.1 hg)
    · intro hg
      apply HomogenizedIdeal.mem_of_isInSpanAt hA.1
      exact hg.mono fun _ ⟨B,hB,hf⟩ => (List.mem_singleton.mp hB) ▸ hf
  | cons B L ih =>
    have hB := hL B List.mem_cons_self
    have hTail (C : MarkedIdeal n X) (hC : C ∈ L) := hL C (List.mem_cons_of_mem B hC)
    have hcTail := isCoherent_finiteSum B L hB.1 (fun C hC => (hTail C hC).1)
    have hdTail := finiteSum_mark_one B L hB.2 (fun C hC => (hTail C hC).2)
    change (sumIdeal (idealPow A.ideal (finiteSum B L).d)
      (idealPow (finiteSum B L).ideal A.d)).mem x g ↔ _
    rw [hA.2,hdTail,idealPow_one_of_isCoherent hA.1,idealPow_one_of_isCoherent hcTail]
    change IsInSpanAt (n := n) (fun f => A.ideal.mem x f ∨ (finiteSum B L).ideal.mem x f) x g ↔ _
    constructor
    · intro hg
      apply IsInSpanAt.trans _ hg
      intro f hf
      rcases hf with hAf | hRest
      · exact isInSpanAt_self ⟨A,List.mem_cons_self,hAf⟩
          (GermIdeal.IsCoherent.holomorphicAt_mem hA.1 hAf)
      · exact ((ih B hB hTail f).mp hRest).mono fun _ ⟨C,hC,hCf⟩ => ⟨C,List.mem_cons_of_mem A hC,hCf⟩
    · intro hg
      apply IsInSpanAt.mono _ hg
      intro f hf
      obtain ⟨C,hC,hCf⟩ := hf
      rcases List.mem_cons.mp hC with rfl | hC
      · exact Or.inl hCf
      · exact Or.inr ((ih B hB hTail f).mpr
          (isInSpanAt_self ⟨C,hC,hCf⟩ (GermIdeal.IsCoherent.holomorphicAt_mem
            (hL C hC).1 hCf)))

/-- Reordering coherent mark-one factors leaves the exact marked sum
unchanged, for any first summand and any mark of that summand. -/
theorem finiteSum_eq_of_perm_mark_one {A : MarkedIdeal n X}
    {L L' : List (MarkedIdeal n X)} (hP : L.Perm L')
    (hL : ∀ B ∈ L, B.ideal.IsCoherent ∧ B.d = 1) :
    finiteSum A L = finiteSum A L' := by
  cases L with
  | nil =>
    have h : L' = [] := List.length_eq_zero_iff.mp (show L'.length = 0 from hP.length_eq.symm)
    rw [h]
  | cons B L =>
    cases L' with
    | nil => exact False.elim (by simpa using hP.length_eq)
    | cons C L' =>
      have hL' (D : MarkedIdeal n X) (hD : D ∈ C :: L') := hL D (hP.mem_iff.mpr hD)
      have hB := hL B List.mem_cons_self
      have hC := hL' C List.mem_cons_self
      have hT (D : MarkedIdeal n X) (hD : D ∈ L) := hL D (List.mem_cons_of_mem B hD)
      have hT' (D : MarkedIdeal n X) (hD : D ∈ L') := hL' D (List.mem_cons_of_mem C hD)
      have hdB := finiteSum_mark_one B L hB.2 (fun D hD => (hT D hD).2)
      have hdC := finiteSum_mark_one C L' hC.2 (fun D hD => (hT' D hD).2)
      have hI : (finiteSum B L).ideal = (finiteSum C L').ideal := by
        ext x g
        rw [finiteSum_mark_one_mem_iff B L hB hT,finiteSum_mark_one_mem_iff C L' hC hT']
        constructor
        · exact IsInSpanAt.mono (fun _ ⟨D,hD,hf⟩ => ⟨D,hP.mem_iff.mp hD,hf⟩)
        · exact IsInSpanAt.mono (fun _ ⟨D,hD,hf⟩ => ⟨D,hP.mem_iff.mpr hD,hf⟩)
      refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ ?_
      · change sumIdeal (idealPow A.ideal (finiteSum B L).d)
          (idealPow (finiteSum B L).ideal A.d) =
          sumIdeal (idealPow A.ideal (finiteSum C L').d) (idealPow (finiteSum C L').ideal A.d)
        rw [hdB,hdC,hI]
      · change A.d * (finiteSum B L).d = A.d * (finiteSum C L').d
        rw [hdB,hdC]

private theorem finset_mapped_toList_perm {α β : Type*} (P : Finset α) (e : α ↪ β) :
    (P.map e).toList.Perm (P.toList.map e) := by
  classical
  apply List.perm_of_nodup_nodup_toFinset_eq
    (Finset.nodup_toList _) ((Finset.nodup_toList _).map e.injective)
  ext j
  simp only [List.mem_toFinset,Finset.mem_toList,List.mem_map,Finset.mem_map]


/-- The inserted old row is a unit. With inactive positions transported
by the ordered embedding, the whole joint profile mark is identical. -/
theorem jointProfileMarked_insertEmpty_old (hn : 0 < n)
    {N : Set X} {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hDense : N ⊆ closure (N \ ⋃ D ∈ old ++ born,D))
    (j : Fin (old.length + 1)) (q : ℕ) (P : Finset (Fin old.length)) :
    jointProfileMarked N (oldBoundaryInsert old j) born q
      (P.map (oldBoundaryInsertEmb (old := old) j)) =
      jointProfileMarked N old born q P := by
  let O := oldBoundaryInsert old j
  let e := oldBoundaryInsertEmb (old := old) j
  have hFactor (i : Fin old.length) :
      canonicalFactorMarked N O born (e i) = canonicalFactorMarked N old born i :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl
      (original_old_rows_insert_empty N born j i).2.1 rfl
  have hFactors : ((P.map e).toList.map (canonicalFactorMarked N O born)).Perm
      (P.toList.map (canonicalFactorMarked N old born)) := by
    refine ((finset_mapped_toList_perm P e).map (canonicalFactorMarked N O born)).trans ?_
    apply List.Perm.of_eq
    rw [List.map_map]
    exact List.map_congr_left (fun i _ => hFactor i)
  have hCoherent (B : MarkedIdeal n X)
      (hB : B ∈ P.toList.map (canonicalFactorMarked N old born)) :
      B.ideal.IsCoherent ∧ B.d = 1 := by
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hB
    exact ⟨(actual_old_parts_geometry hn hN hE hTr hDense i).2.2.2.2.1,rfl⟩
  unfold jointProfileMarked
  rw [canonicalProductMarked_insert_empty_old hn hN hE hTr hDense j q]
  exact (finiteSum_eq_of_perm_mark_one hFactors.symm hCoherent).symm

/-- Old insertion is removed from the mark, and born insertion is
retained literally in its ordered boundary record. -/
theorem jointProfileMarked_insertEmpty_old_born (hn : 0 < n)
    {N : Set X} {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hDense : N ⊆ closure (N \ ⋃ D ∈ old ++ born,D))
    (j : Fin (old.length + 1)) (q : ℕ) (P : Finset (Fin old.length))
    {b : ℕ} (hb : b ≤ born.length) :
    jointProfileMarked N (oldBoundaryInsert old j) (born.insertIdx b ∅) q
      (P.map (oldBoundaryInsertEmb (old := old) j)) =
      insertEmpty b (jointProfileMarked N old born q P) := by
  rw [jointProfileMarked_insertEmpty_born N (oldBoundaryInsert old j) born q
    (P.map (oldBoundaryInsertEmb (old := old) j)) hb,
    jointProfileMarked_insertEmpty_old hn hN hE hTr hDense j q P]


end
end Hironaka.HironakaG4JointProfileEmptyOld
