import Hironaka.Resolution.HironakaG4OriginalSelectedLowerBoundaryHistory
import Hironaka.Resolution.HironakaG4ResidualInductionInputs
import Hironaka.Resolution.HironakaSharpActualCurveGlobalBoundaryCoordinates
import Hironaka.Invariant.MemberInterLocusAlong

/-! Literal CURRENT lower bad points are CURRENT original bad points on the
SAME selected history. Source-first complete chapter:
hironaka-g4-original-selected-lower-bad-history.tex. The native static
geometric inclusion and whole boundary/strict-append laws are reused. -/

set_option autoImplicit false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4OriginalSelectedLowerBadHistory

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers HomogenizedGlueingTower NormalCrossings MemberInterLocusAlong
  HironakaG4OriginalSelectedLowerBoundaryHistory HironakaG4ResidualInductionInputs
  HironakaG4RecordedTowerResidualCompatibility HironakaG4PreparedCentreCoordinates
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpOriginalProductTraceOrder
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaSharpActualCurveGlobalBoundaryCoordinates
  HironakaSharpActualCurveWholeBoundaryTransversality
  RelativePrincipalizationSpan RestrictedIdealExtension MonomialPartAlong
  MarkedIdeals MarkedIdeals.MarkedIdeal

variable {n : ℕ} {X Y Q : CMfd.{u} n}

private theorem actual_remaining_boundary_dictionary (W : Set X) (E : List (Set X))
    (i : ℕ) (T : BlowupTower X Y) (S : Set Y) (R : BlowupTower Y Q) :
    let B := geoTransformAlong (geometricTemplate W []) T
    (geoTransformAlong (geometricTemplate S ((E.map (strictAlong T)).eraseIdx i ++ B.E)) R).E=
      (E.map (strictAlong (T.append R))).eraseIdx i ++
        (geoTransformAlong (geometricTemplate W []) (T.append R)).E := by
  let B := geoTransformAlong (geometricTemplate W []) T
  let F := (E.map (strictAlong T)).eraseIdx i ++ B.E
  let K := geometricTemplate (univ : Set Y) []
  have hOld : (E.map (strictAlong T)).map (strictAlong R)=E.map (strictAlong (T.append R)) := by
    rw [List.map_map]
    exact congrArg (fun f : Set X → Set Q => E.map f)
      (funext fun H => (strictAlong_append T H R).symm)
  have hBorn : (geoTransformAlong (geometricTemplate W []) (T.append R)).E=
      B.E.map (strictAlong R) ++ (geoTransformAlong K R).E := by
    rw [geoTransformAlong_append]
    exact boundary_geoTransformAlong_decomposition B K rfl R
  calc
    (geoTransformAlong (geometricTemplate S F) R).E
        = F.map (strictAlong R) ++ (geoTransformAlong K R).E :=
      boundary_geoTransformAlong_decomposition (geometricTemplate S F) K rfl R
    _ = ((E.map (strictAlong T)).eraseIdx i).map (strictAlong R) ++
        (B.E.map (strictAlong R) ++ (geoTransformAlong K R).E) := by
      rw [List.map_append,List.append_assoc]
    _ = (E.map (strictAlong (T.append R))).eraseIdx i ++
        (B.E.map (strictAlong R) ++ (geoTransformAlong K R).E) := by
      rw [←List.eraseIdx_map,hOld]
    _ = _ := by rw [←hBorn]

/-- ONE actual lower test tail internally identifies its CURRENT literal bad
locus as a subset of the SAME original appended CURRENT full-boundary bad locus. -/
theorem actual_original_selected_lower_current_bad_subset (hn : 0 < n) {W : Set X}
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
    ∀ {Q : CMfd.{u} n} (R : BlowupTower Y Q),IsGeoTestTower (geometricTemplate Z F) R →
      let P := geoTransformAlong (geometricTemplate Z F) R
      let U := geoTransformAlong (geometricTemplate W []) (T.append R)
      let V := geoTransformAlong (geometricTemplate (univ : Set X) E) (T.append R)
      originalSharpBadLocus (n := n) P.N P.E ⊆ originalSharpBadLocus (n := n) U.N V.E := by
  let A := chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T
  let B := geoTransformAlong (geometricTemplate W []) T
  let F := (E.map (strictAlong T)).eraseIdx i.val ++ B.E
  let Z := A.N ∩ A.ideal.zeroLocus
  dsimp only
  intro Q R hR
  let U := geoTransformAlong (geometricTemplate W []) (T.append R)
  let V := geoTransformAlong (geometricTemplate (univ : Set X) E) (T.append R)
  let P := geoTransformAlong (geometricTemplate Z F) R
  let old := E.map (strictAlong (T.append R))
  obtain ⟨_hZ,_hWhole,hTails⟩ := actual_original_selected_lower_boundary_history
    hn hW hE hdense i T hT hFull hOrd
  obtain ⟨hUpper,hAmbient,_hNR,hZR,hSub,hChronN,hWhole⟩ := hTails R hR
  obtain ⟨hN,hSNC,hTr,hDense,hRows⟩ := actual_recorded_tower_residual_dictionary
    hn hW hE hdense (T.append R) hUpper hAmbient
  let j : Fin old.length := ⟨i.val,by simpa only [old,List.length_map] using i.isLt⟩
  have hGet : old.get j=strictAlong (T.append R) (E.get i) := by simp [old,j]
  have hIdeal : oldResidualPart U.N old U.E j=vanishingIdeal (n := n) (strictAlong R Z) := by
    change nonmonomialPartAlong n U.N
      (restrictOn n U.N (vanishingIdeal (n := n) (old.get j))) U.E=_
    rw [hGet,(hRows i).2.2.1]
    exact hWhole
  have hParentN : U.N=strictAlong R A.N :=
    (chronologicalMarked_geometric_fields
      (originalRelativeMemberMarked W (E.get i)) (T.append R)).1.symm.trans hChronN
  have hSelectedSub : strictAlong R Z ⊆ U.N := by
    rw [hParentN]
    exact hSub
  have hLowerN : P.N=strictAlong R Z := N_geoTransformAlong (geometricTemplate Z F) R
  have hSupport : U.N ∩ (oldResidualPart U.N old U.E j).zeroLocus=P.N := by
    rw [hIdeal,BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hZR.1,hLowerN]
    exact inter_eq_right.mpr hSelectedSub
  have hRemaining : remainingBoundary old U.E j=P.E :=
    (actual_remaining_boundary_dictionary W E i.val T Z R).symm
  have hBoundary : old ++ U.E=V.E :=
    (actual_whole_ambient_boundary_ordered_dictionary W E (T.append R)).symm
  have hStatic := originalSharpBadLocus_residual_subset hn hN hSNC hTr hDense j
  rw [hSupport,hRemaining,hBoundary] at hStatic
  exact hStatic

end
end Hironaka.HironakaG4OriginalSelectedLowerBadHistory
