import Hironaka.Resolution.HironakaG4OriginalSelectedResidualTail
import Hironaka.Resolution.HironakaG4RecordedTowerResidualCompatibility
import Hironaka.Invariant.DropMembers

/-! A true selected lower-boundary test tail extends the SAME original
carrier and whole ambient boundary history. Source-first complete chapter:
hironaka-g4-original-selected-lower-boundary-history.tex. No other-row
order preservation, future comparison packet or terminal NC is assumed. -/

set_option autoImplicit false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4OriginalSelectedLowerBoundaryHistory

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers HomogenizedGlueingTower MemberInterTowerAlong NormalCrossings
  HironakaG4OriginalSelectedResidualTail HironakaG4RecordedTowerResidualCompatibility
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualTraceIncidence
  HironakaSharpActualCurveWholeBoundaryTransversality NormalCrossingsComparison
  HironakaSharpOriginalProductTraceOrder SimultaneousNormalCrossings
  NonmonomialTransformAlong RelativePrincipalizationSpan RestrictedIdealExtension
  CoefficientIdealRestriction DropMembers GermIdealOrder IdealWeightPowers
  MarkedIdeals MarkedIdeals.MarkedIdeal

variable {n : ℕ} {X Y : CMfd.{u} n}

theorem actual_zero_mark_test_of_lower_test (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hd : M.d=0) {S : Set X} {F : List (Set X)}
    (hSN : S ⊆ M.N) (hEF : M.E.Sublist F) :
    ∀ {Q : CMfd.{u} n} (R : BlowupTower X Q),
      IsGeoTestTower (geometricTemplate S F) R → IsGeoTestTower M R ∧
        (geoTransformAlong M R).E.Sublist (geoTransformAlong (geometricTemplate S F) R).E
  | _,.refl,_hR => ⟨trivial,hEF⟩
  | _,.step R C π hπ,hR => by
    obtain ⟨hOld,hSub⟩ := actual_zero_mark_test_of_lower_test M hM hd hSN hEF R hR.1
    have hw := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM R hOld
    have hCS : C ⊆ strictAlong R S := by
      have hField : (geoTransformAlong (geometricTemplate S F) R).N=strictAlong R S :=
        N_geoTransformAlong (geometricTemplate S F) R
      rw [←hField]
      exact hR.2.subset_N
    have hCN : C ⊆ (geoTransformAlong M R).N := by
      rw [N_geoTransformAlong]
      exact hCS.trans (strictAlong_mono R hSN)
    have hAdm : (geoTransformAlong M R).IsAdmissibleCentre C := by
      refine ⟨hR.2.1,?_,hasNormalCrossings_of_forall_mem hR.2.2.2
        (fun _ hH => hSub.subset hH)⟩
      change C ⊆ cosupport n _ _ (geoTransformAlong M R).d
      rw [d_geoTransformAlong,hd,cosupport_zero
        (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hw.isCoherent hg)]
      exact hCN
    refine ⟨⟨hOld,hAdm⟩,?_⟩
    exact sublist_transformE π C hSub

private theorem actual_selected_support_subset_own_old (hn : 0 < n) {W : Set X}
    {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (i : Fin E.length)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T) :
    let A := chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T
    A.N ∩ A.ideal.zeroLocus ⊆ strictAlong T (E.get i) := by
  let A := chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T
  let B := geoTransformAlong (geometricTemplate W []) T
  let H := strictAlong T (E.get i)
  let I := restrictOn n B.N (vanishingIdeal (n := n) H)
  have hAN : A.N=B.N :=
    (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i)) T).1
  have hActual := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  obtain ⟨hcI,_hnzI,hNm,_hFactor⟩ := hActual.2.2.2.2 i
  have hIle : I.Le A.ideal := by
    rw [←hNm]
    exact le_nonmonomialPartAlong_self hcI
  have hMem : H ∈ E.map (strictAlong T) ++ B.E :=
    List.mem_append_left _ (List.mem_map_of_mem (List.get_mem E i))
  obtain ⟨k,hk⟩ := List.mem_iff_get.mp hMem
  have hHsmooth := MonomialPart.isClosedSubmanifold_get hn hActual.2.1 k
  rw [hk] at hHsmooth
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHsmooth
  change A.N ∩ A.ideal.zeroLocus ⊆ strictAlong T (E.get i)
  intro x hx
  have hxN : x ∈ B.N := hAN ▸ hx.1
  have hxI : x ∈ I.zeroLocus := fun g hg => hx.2 g (hIle x g hg)
  have hxH := (zeroLocus_restrictOn_iff hcH hxN).mp hxI
  rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hHsmooth.1] at hxH

/-- ONE actual selected lower test internally extends BOTH original geometry
tests on the SAME append and retains the selected ORIGINAL whole ideal. -/
theorem actual_original_selected_lower_boundary_history (hn : 0 < n) {W : Set X}
    {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (i : Fin E.length)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1) :
    let A := chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T
    let B := geoTransformAlong (geometricTemplate W []) T
    let F := (E.map (strictAlong T)).eraseIdx i.val ++ B.E
    let Z := A.N ∩ A.ideal.zeroLocus
    IsClosedSubmanifold n Z ∧ A.ideal=vanishingIdeal (n := n) Z ∧
      ∀ {Q : CMfd.{u} n} (R : BlowupTower Y Q),IsGeoTestTower (geometricTemplate Z F) R →
        IsGeoTestTower (geometricTemplate W []) (T.append R) ∧
        IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append R) ∧
        IsClosedSubmanifold n (strictAlong R A.N) ∧ IsClosedSubmanifold n (strictAlong R Z) ∧
        strictAlong R Z ⊆ strictAlong R A.N ∧
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append R)).N=strictAlong R A.N ∧
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append R)).ideal=
          vanishingIdeal (n := n) (strictAlong R Z) := by
  let A := chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T
  let B := geoTransformAlong (geometricTemplate W []) T
  let old := E.map (strictAlong T)
  let F := old.eraseIdx i.val ++ B.E
  let Z := A.N ∩ A.ideal.zeroLocus
  obtain ⟨hZ,hWhole,hTail⟩ := actual_original_selected_residual_tail hn hW hE hdense i T hT hOrd
  have hOwn : Z ⊆ strictAlong T (E.get i) :=
    actual_selected_support_subset_own_old hn hW hE hdense i T hT hFull
  have hAN : A.N=B.N :=
    (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i)) T).1
  have hwCarrier : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwB := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwCarrier T hT
  let M := geoTransformAlong (geometricTemplate (univ : Set X) E) T
  have hwAmbient : (geometricTemplate (univ : Set X) E).IsWellFormed :=
    ⟨⟨isClosed_univ,fun x _ => ⟨n,AnalyticIrreducibleComponents.regularAtDim_univ x⟩⟩,
      isCoherent_unitIdeal,hE,isTransverse_univ_of_isSNCDivisor hE⟩
  have hwM := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwAmbient T hFull
  have hMN : M.N=univ := (pullback_eq_mul_geoTransformAlong
    (𝔪 := geometricTemplate (univ : Set X) E) rfl isCoherent_unitIdeal T hFull).1
  have hME : M.E=old ++ B.E := actual_whole_ambient_boundary_ordered_dictionary W E T
  have hFsub : F.Sublist M.E := by
    rw [hME]
    exact (List.eraseIdx_sublist old i.val).append (List.Sublist.refl B.E)
  have hMissing : ∀ H ∈ M.E,H ∉ F → Z ⊆ H := by
    intro H hH hNot
    rw [hME] at hH
    rcases List.mem_append.mp hH with hOld | hBorn
    · obtain ⟨j,hj⟩ := List.mem_iff_get.mp hOld
      let k : Fin old.length := ⟨i.val,by simpa only [old,List.length_map] using i.isLt⟩
      have hji : j.val=i.val := by
        by_contra hne
        exact hNot (List.mem_append_left B.E
          (List.mem_eraseIdx_iff_getElem.mpr ⟨j.val,j.isLt,hne,hj⟩))
      have hjk : j=k := Fin.ext hji
      have hGet : old.get k=strictAlong T (E.get i) := by simp [old,k]
      rw [hjk,hGet] at hj
      rw [←hj]
      exact hOwn
    · exact False.elim (hNot (List.mem_append_right _ hBorn))
  refine ⟨hZ,hWhole,?_⟩
  intro Q R hR
  have hwZ : (geometricTemplate Z []).IsWellFormed :=
    ⟨hZ,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hZ⟩
  have hSelected : IsGeoTestTower (geometricTemplate Z []) R :=
    (actual_zero_mark_test_of_lower_test (geometricTemplate Z []) hwZ rfl
      (Subset.rfl) (List.nil_sublist F) R hR).1
  have hParent : IsGeoTestTower B R :=
    (actual_zero_mark_test_of_lower_test B hwB (by rw [d_geoTransformAlong]; rfl)
      (inter_subset_left.trans (fun _ hx => hAN ▸ hx))
      (List.sublist_append_right _ _) R hR).1
  let M' : MarkedIdeal n Y := {M with E := F}
  have hwM' : M'.IsWellFormed := isWellFormed_withE hwM hFsub
  have hSmall : IsGeoTestTower M' R :=
    (actual_zero_mark_test_of_lower_test M' hwM' (by change M.d=0; rw [d_geoTransformAlong]; rfl)
      (by change Z ⊆ M.N; rw [hMN]; exact subset_univ Z)
      (List.Sublist.refl F) R hR).1
  have hCentres : CentresIn Z R :=
    centresIn_of_isGeoTestTower_withN (geometricTemplate (univ : Set Y) F) Z R hR
  have hFullTail : IsGeoTestTower M R :=
    (isGeoTestTower_withE_iff_of_centresIn M hwM
      (fun _ hH => hFsub.subset hH) hMissing R hCentres).1.mp hSmall
  exact ⟨(isGeoTestTower_append_iff _ T R).mpr ⟨hT,hParent⟩,
    (isGeoTestTower_append_iff _ T R).mpr ⟨hFull,hFullTail⟩,hTail R hSelected⟩

end
end Hironaka.HironakaG4OriginalSelectedLowerBoundaryHistory
