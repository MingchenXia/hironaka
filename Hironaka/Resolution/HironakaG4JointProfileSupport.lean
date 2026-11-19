import Hironaka.Resolution.HironakaActualRetainedBoundaryMaskBlock

/-! The actual joint mark is supported exactly where its fixed profile and
inactive old-factor labels occur simultaneously. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
universe u

namespace Hironaka.HironakaG4JointProfileSupport
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaSharpActualFiniteChronologicalHistory HironakaActualRetainedBornResidualSeed
  HironakaActualRetainedBoundaryJointStep HironakaActualRetainedBoundaryMaskBlock
  HironakaG4PreparedCentreCoordinates HironakaActualFiniteMarkedSumHistories
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpOriginalProductTraceOrder
  RelativePrincipalizationSpan DivisorExponentAlong GermIdealOrder

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- With a fixed row cap and inactive-count cap, the joint cosupport has
exactly the selected row profile and exactly the selected inactive mask. -/
theorem jointProfileMarked_cosupp_iff_actual_profile_mask_at (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    (profile : Fin old.length → ℕ) (q : ℕ) (hq : 1 ≤ q) (hsum : ∑ i,profile i=q)
    (P : Finset (Fin old.length)) (hP : ∀ i ∈ P,profile i=0) (x : X)
    (hOrd : x ∈ N → ∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ profile i)
    (hBound : x ∈ N → ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal x=q →
      (inactiveCanonicalRows N old born profile x).card ≤ P.card) :
    x ∈ (jointProfileMarked N old born q P).cosupp ↔
      x ∈ N ∧ (∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x=profile i) ∧
        inactiveCanonicalRows N old born profile x = P := by
  classical
  let A := canonicalProductMarked N old born q
  let L := P.toList.map (canonicalFactorMarked N old born)
  let D := oldMonomialPart N old born
  let J := oldResidualPart N old born
  let I := inactiveCanonicalRows N old born profile x
  have h0 := retained_product_geometry hn hN hE hTr hdense q (.refl : BlowupTower X X) trivial
  have hAc : A.ideal.IsCoherent := h0.1
  have hNz : ∀ y ∈ N,IsNonzeroAlongAt N A.ideal y := h0.2.1
  have hSum (hx : x ∈ N) : ordinaryTraceOrder N A.ideal x = ∑ i,ordinaryTraceOrder N (J i) x :=
    h0.2.2.2 x hx
  have hD (i : Fin old.length) : (D i).IsCoherent :=
    (actual_old_parts_geometry hn hN hE hTr hdense i).2.2.2.2.1
  have hL : ∀ B ∈ L,B.N=A.N ∧ B.E=A.E ∧ B.ideal.IsCoherent ∧ 1 ≤ B.d := by
    intro B hB
    obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hB
    exact ⟨rfl,rfl,hD i,le_rfl⟩
  have hJoint : x ∈ (jointProfileMarked N old born q P).cosupp ↔
      x ∈ A.cosupp ∧ ∀ i ∈ P,x ∈ (canonicalFactorMarked N old born i).cosupp := by
    have h := (finiteSum_history A L hN hAc hq hL (.refl : BlowupTower X X)).2 trivial |>.1
    change x ∈ (finiteSum A L).cosupp ↔ _
    rw [←geoTransformAlong_refl (finiteSum A L),h]
    simp only [Set.mem_ofPred_eq,geoTransformAlong_refl,List.mem_cons,forall_eq_or_imp]
    constructor
    · rintro ⟨hA,hF⟩
      exact ⟨hA,fun i hi => hF _ (List.mem_map_of_mem (Finset.mem_toList.mpr hi))⟩
    · rintro ⟨hA,hF⟩
      refine ⟨hA,?_⟩
      intro B hB
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hB
      exact hF i (Finset.mem_toList.mp hi)
  have hDChar (i : Fin old.length) (hi : i ∈ P) (hx : x ∈ N) :
      x ∈ (canonicalFactorMarked N old born i).cosupp ↔ i ∈ I := by
    change x ∈ cosupport n N (D i) 1 ↔ i ∈ I
    rw [cosupport_one (fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem (hD i) h)]
    have h := actual_proper_iff_zeroLocus hD i x
    have hNotUnit : ¬(D i).mem x 1 ↔ x ∈ (D i).zeroLocus := by
      simpa only [actualProperPositions,Finset.mem_filter,Finset.mem_univ,true_and] using h
    simp only [Set.mem_inter_iff,hx,true_and,I,inactiveCanonicalRows,Finset.mem_filter,
      Finset.mem_univ,hP i hi]
    exact hNotUnit.symm
  rw [hJoint]
  constructor
  · rintro ⟨hA,hMask⟩
    have hx : x ∈ N := hA.1
    have hLe := (Finset.sum_le_sum (fun i _ => hOrd hx i)).trans_eq hsum
    have hqle := (ordinaryTraceOrder_cosupport_iff hN hAc hNz hx q).mp hA
    have hqeq : ordinaryTraceOrder N A.ideal x=q := ((hSum hx).trans_le hLe).antisymm hqle
    have hEqSum := (hSum hx).symm.trans (hqeq.trans hsum.symm)
    have hRowEq := (Finset.sum_eq_sum_iff_of_le (fun i _ => hOrd hx i)).mp hEqSum
    have hSub : P ⊆ I := fun i hi => (hDChar i hi hx).mp (hMask i hi)
    exact ⟨hx,fun i => hRowEq i (Finset.mem_univ i),
      (Finset.eq_of_subset_of_card_le hSub (hBound hx hqeq)).symm⟩
  · rintro ⟨hx,hRow,hMask⟩
    have hqeq : ordinaryTraceOrder N A.ideal x=q :=
      (hSum hx).trans ((Finset.sum_congr rfl (fun i _ => hRow i)).trans hsum)
    refine ⟨(ordinaryTraceOrder_cosupport_iff hN hAc hNz hx q).mpr hqeq.ge,?_⟩
    intro i hi
    apply (hDChar i hi hx).mpr
    change i ∈ inactiveCanonicalRows N old born profile x
    rwa [hMask]

/-- The joint cosupport under fixed ambient row and inactive-count caps. -/
theorem jointProfileMarked_cosupp_iff_actual_profile_mask (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    (profile : Fin old.length → ℕ) (q : ℕ) (hq : 1 ≤ q) (hsum : ∑ i,profile i=q)
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ profile i)
    (P : Finset (Fin old.length)) (hP : ∀ i ∈ P,profile i=0)
    (hBound : ∀ x ∈ N,ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal x=q →
      (inactiveCanonicalRows N old born profile x).card ≤ P.card) (x : X) :
    x ∈ (jointProfileMarked N old born q P).cosupp ↔
      x ∈ N ∧ (∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x=profile i) ∧
        inactiveCanonicalRows N old born profile x = P :=
  jointProfileMarked_cosupp_iff_actual_profile_mask_at hn hN hE hTr hdense
    profile q hq hsum P hP x (hOrd x) (hBound x)

/-- The endpoint strictly reduces the actual joint rank over every point
in the selected initial cosupport. If the total order is unchanged, the
whole residual profile is unchanged and the actual inactive mask shrinks. -/
theorem retained_joint_mask_progress_over_cosupp (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    (profile : Fin old.length → ℕ) (q : ℕ) (hq : 1 ≤ q) (hsum : ∑ i,profile i=q)
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ profile i)
    (P : Finset (Fin old.length)) (hP : ∀ i ∈ P,profile i=0)
    (hBound : ∀ x ∈ N,ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal x=q →
      (inactiveCanonicalRows N old born profile x).card ≤ P.card)
    (R : BlowupTower X Y) (hR : RetainedJointMaskResult N old born profile q P R)
    (z : Y) (hz : z ∈ (geoTransformAlong (geometricTemplate N born) R).N)
    (hFoot : R.proj z ∈ (jointProfileMarked N old born q P).cosupp) :
    let A := geoTransformAlong (geometricTemplate N born) R
    let r := fun i : Fin old.length => ordinaryTraceOrder A.N
      (chronologicalMarked (retainedResidualMarked N old born i) R).ideal z
    (∑ i,r i) < q ∨
      r = profile ∧ retainedInactiveRows N old born r R z ⊂ P := by
  classical
  intro A r
  obtain ⟨_hx,hProfile,hMask⟩ :=
    (jointProfileMarked_cosupp_iff_actual_profile_mask hn hN hE hTr hdense
      profile q hq hsum hOrd P hP hBound (R.proj z)).mp hFoot
  have hEnd :
      IsGeoTestTower (geometricTemplate N born) R ∧
      (∀ i : Fin old.length,r i ≤ ordinaryTraceOrder N (oldResidualPart N old born i) (R.proj z)) ∧
      retainedInactiveRows N old born profile R z ⊆ inactiveCanonicalRows N old born profile (R.proj z) := by
    cases R <;>
      obtain ⟨hTest,_,_,_,hRows,_,_,_,_,_,_,hAct⟩ := hR.2.2.1 0 <;>
      exact ⟨hTest,hRows z hz,hAct z hz⟩
  have hRowLe (i : Fin old.length) : r i ≤ profile i := (hEnd.2.1 i).trans_eq (hProfile i)
  have hLe := (Finset.sum_le_sum (fun i _ => hRowLe i)).trans_eq hsum
  rcases hLe.eq_or_lt with heq | hlt
  · have hEq : r = profile := funext fun i =>
      (Finset.sum_eq_sum_iff_of_le (fun i _ => hRowLe i)).mp
        (heq.trans hsum.symm) i (Finset.mem_univ i)
    refine Or.inr ⟨hEq,?_⟩
    rw [hEq]
    have hSub : retainedInactiveRows N old born profile R z ⊆ P := hMask ▸ hEnd.2.2
    have hProd := (retained_product_geometry hn hN hE hTr hdense q R hEnd.1).2.2.2 z hz
    obtain ⟨i,hi,hUnit⟩ := hR.2.2.2 z hz (hProd.trans heq)
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hSub,fun hEqual => ?_⟩
    have hi' : i ∈ retainedInactiveRows N old born profile R z := hEqual.symm ▸ hi
    exact (Finset.mem_filter.mp hi').2.2 hUnit
  · exact Or.inl hlt

end
end Hironaka.HironakaG4JointProfileSupport
