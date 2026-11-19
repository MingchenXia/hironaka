import Hironaka.Resolution.HironakaActualSharpBadFirstMaximumBlowup
import Hironaka.Invariant.DropMembers

/-! Actual original canonical sharp-ideal histories produce full ambient geometry.
The omitted containing old member is restored with no future-geometry premise. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaCanonicalSharpBadHistoryFullGeometry
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  Hironaka.RegularLocusDense BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealRestrictOpen MarkedIdealBiholomorphism
  MarkedIdealEquivalence.MarkedIdeal HomogenizedGlueingTower CoefficientIdealRestriction
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance SimultaneousNormalCrossings
  HironakaOriginalNCMarkedStratumHistoryValue HironakaOriginalNCMarkedStratumCanonicalHistory
  HironakaOriginalOldBranchOpenHistory HironakaOriginalNCOldStratumStrictEquality
  HironakaNormalCrossingsSNCBlockCarrier HironakaNormalCrossingsBoundaryTransform
  HironakaG4RecordedTowerResidualCompatibility HironakaActualSharpBadMaximumProcessedSlice
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpOriginalProductTraceOrder
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualTraceIncidence
  HironakaSharpOriginalMultiBoundaryBadLocus RelativePrincipalizationSpan RestrictedIdealExtension
  MonomialPartAlong NonmonomialTransformAlong DropMembers
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X Y Z : CMfd.{u} n}

theorem canonical_empty_native_history_full_geometry
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (hEmpty : M.E = [])
    (old born : List (Set X)) (hFull : IsSNCDivisor n (old ++ born))
    (j : Fin old.length) (hOwn : M.N ⊆ old.get j)
    (R : BlowupTower X Y)
    (hCan : IsCanonical M
      (markedStratumHistoryValue M (⋃D∈old.eraseIdx j.val ++ born,D)) R) :
    IsGeoTestTower M R ∧
      IsOriginalBranchTestTower M (⋃D∈old.eraseIdx j.val ++ born,D) R ∧
      IsGeoTestTower
        (HironakaOriginalNCOldStratumStrictEquality.boundaryGeometry (old ++ born)) R ∧
      ∀ r : ℕ, IsSNCDivisor n
        ((old ++ born).map (strictAlong (head R r)) ++
          (geoTransformAlong M (head R r)).E) := by
  let F := old.eraseIdx j.val ++ born
  let H := ⋃D∈F,D
  have hF : IsSNCDivisor n F := isSNCDivisor_of_sublist hFull
    ((List.eraseIdx_sublist old j.val).append (List.Sublist.refl born))
  have hH : IsBoundaryAdaptedCarrier (n := n) H M.E := by
    rw [hEmpty]
    exact boundaryAdapted_union_of_snc_append F [] (by simpa only [List.append_nil] using hF)
  obtain ⟨hTest,hHistory,_,_⟩ := markedStratum_canonical_history_joint_interpretation M hM hH R hCan
  let U : Opens X := ⊤
  let B := F.map ((Subtype.val : U → X) ⁻¹' ·)
  have hEU : (MarkedIdeal.pullback (Subtype.val : U → X) M).E = [] := by
    change M.E.map _ = []
    rw [hEmpty]
    rfl
  have hBU : IsSNCDivisor n (B ++ (MarkedIdeal.pullback (Subtype.val : U → X) M).E) := by
    rw [hEU,List.append_nil]
    exact isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hF
  have hUnion : (Subtype.val : U → X) ⁻¹' H = ⋃D∈B,D := by
    ext y
    simp [H,B]
  have hTop := hHistory U B hBU hUnion
  have hTop' : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X)
      ({M with E := F} : MarkedIdeal n X)) (restrict U R) := by
    convert hTop using 1
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of
      (𝔪 := MarkedIdeal.pullback (Subtype.val : U → X) ({M with E := F} : MarkedIdeal n X))
      (𝔫 := ({MarkedIdeal.pullback (Subtype.val : U → X) M with
        E := B ++ (MarkedIdeal.pullback (Subtype.val : U → X) M).E} : MarkedIdeal n U)) rfl ?_ rfl rfl
    change B = B ++ (MarkedIdeal.pullback (Subtype.val : U → X) M).E
    rw [hEU,List.append_nil]
  have hAug := isGeoTestTower_of_restrict_cosupport_cover M
    hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent F U
    (fun _ _ => mem_univ _) R hTest hTop'
  have hSmall : IsGeoTestTower (boundaryGeometry (X := X) F) R :=
    boundaryGeometry_test ({M with E := F} : MarkedIdeal n X) hF R hAug
  let D := boundaryGeometry (X := X) (old ++ born)
  have hD : D.IsWellFormed := ⟨isClosedSubmanifold_univ,IdealWeightPowers.isCoherent_unitIdeal,hFull,
    isTransverse_univ_of_isSNCDivisor hFull⟩
  have hSub : F.Sublist D.E := (List.eraseIdx_sublist old j.val).append (List.Sublist.refl born)
  have hMissing : ∀ A∈D.E,A∉F → M.N⊆A := by
    intro A hA hNot
    rcases List.mem_append.mp hA with hOld | hBorn
    · obtain ⟨a,ha⟩ := List.mem_iff_get.mp hOld
      have haj : a.val = j.val := by
        by_contra hne
        exact hNot (List.mem_append_left born
          (List.mem_eraseIdx_iff_getElem.mpr ⟨a.val,a.isLt,hne,ha⟩))
      have he : a = j := Fin.ext haj
      rw [he] at ha
      rw [←ha]
      exact hOwn
    · exact (hNot (List.mem_append_right _ hBorn)).elim
  have hCentres : CentresIn M.N R := by
    apply centresIn_of_isGeoTestTower_withN M M.N R
    exact hTest
  have hFullTest : IsGeoTestTower D R :=
    (isGeoTestTower_withE_iff_of_centresIn D hD (fun _ h => hSub.subset h) hMissing R hCentres).1.mp hSmall
  refine ⟨hTest,hHistory,hFullTest,?_⟩
  intro r
  let K := head R r
  have hK : IsGeoTestTower D K := ((isGeoTestTower_iff_head_tail D R r).mp hFullTest).1
  have hDK := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hD K hK
  have hInit : ({M with E := (old++born) ++ M.E} : MarkedIdeal n X).E = D.E := by
    change (old++born) ++ M.E = old++born
    rw [hEmpty,List.append_nil]
  have hECurrent := E_geoTransformAlong_eq
    (𝔪 := ({M with E := (old++born) ++ M.E} : MarkedIdeal n X)) (𝔫 := D) hInit K
  have hDict := entire_original_old_retained_boundary M (old++born) K
  have hWhole : (geoTransformAlong D K).E =
      (old++born).map (strictAlong K) ++ (geoTransformAlong M K).E := hECurrent.symm.trans hDict
  rw [←hWhole]
  exact hDK.isSNCDivisor

theorem actual_sharp_bad_canonical_history_full_geometry
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃H∈E,H))
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ x∈(geoTransformAlong (geometricTemplate W []) T).N,
      ∀ a : Fin E.length,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal x ≤ 1)
    (d : ℕ)
    (hReg : ∀ x∈(geoTransformAlong (geometricTemplate W []) T).N,
      RegularAtDim (n := n) (geoTransformAlong (geometricTemplate W []) T).N x (d+1))
    (hDistinct : chronologicalDistinctDefect W E T = ∅)
    (j : Fin E.length) (R : BlowupTower Y Z)
    (hCan :
      let A := geoTransformAlong (geometricTemplate W []) T
      let L := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus
      let Fj := (E.map (strictAlong T)).eraseIdx j.val ++ A.E
      let Bj := originalSharpBadLocus (n := n) L Fj
      let M : MarkedIdeal n Y := ⟨L,[],vanishingIdeal (n := n) Bj,1⟩
      IsCanonical M (markedStratumHistoryValue M (⋃D∈Fj,D)) R) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let old := E.map (strictAlong T)
    let L := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal.zeroLocus
    let Fj := old.eraseIdx j.val ++ A.E
    let Bj := originalSharpBadLocus (n := n) L Fj
    let M : MarkedIdeal n Y := ⟨L,[],vanishingIdeal (n := n) Bj,1⟩
    IsInvDomain n M ∧ IsGeoTestTower M R ∧
      IsOriginalBranchTestTower M (⋃D∈Fj,D) R ∧
      IsGeoTestTower
        (HironakaOriginalNCOldStratumStrictEquality.boundaryGeometry (old ++ A.E)) R ∧
      ∀ r : ℕ, IsSNCDivisor n
        ((old ++ A.E).map (strictAlong (head R r)) ++
          (geoTransformAlong M (head R r)).E) := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let old := E.map (strictAlong T)
  let Jj := (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal
  let L := A.N ∩ Jj.zeroLocus
  let Fj := old.eraseIdx j.val ++ A.E
  let Bj := originalSharpBadLocus (n := n) L Fj
  let M : MarkedIdeal n Y := ⟨L,[],vanishingIdeal (n := n) Bj,1⟩
  obtain ⟨_,_,_,hM,_⟩ := sharp_bad_native_domain hn hW hE hdense T hT hFull hOrd d hReg hDistinct j
  have hRec := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  let jo : Fin old.length := ⟨j.val,by simp [old]⟩
  have hGet : old.get jo = strictAlong T (E.get j) := by simp [old,jo]
  have hOld := isSNCDivisor_of_sublist hRec.2.1 (List.sublist_append_left old A.E)
  have hOldSmooth : IsClosedSubmanifold n (strictAlong T (E.get j)) := by
    rw [←hGet]
    exact MonomialPart.isClosedSubmanifold_get hn hOld jo
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hOldSmooth
  obtain ⟨hcI,_,hNm,_⟩ := hRec.2.2.2.2 j
  have hLe : (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get j)))).Le Jj := by
    change (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get j)))).Le
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal
    rw [←hNm]
    exact le_nonmonomialPartAlong_self hcI
  have hOwn : M.N ⊆ old.get jo := by
    rw [hGet]
    intro x hx
    have hz : x∈(vanishingIdeal (n := n) (strictAlong T (E.get j))).zeroLocus :=
      (zeroLocus_restrictOn_iff hcH hx.1).mp (fun g hg => hx.2 g (hLe x g hg))
    rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hOldSmooth.1] at hz
  have hGeometry := canonical_empty_native_history_full_geometry M hM rfl old A.E hRec.2.1 jo hOwn R hCan
  exact ⟨hM,hGeometry⟩

end
end Hironaka.HironakaCanonicalSharpBadHistoryFullGeometry
