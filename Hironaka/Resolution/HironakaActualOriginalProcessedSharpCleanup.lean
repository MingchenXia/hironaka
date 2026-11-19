import Hironaka.Resolution.HironakaActualOriginalProcessedJointPreparedness
import Hironaka.Resolution.HironakaActualProcessedSharpCleanup

/-! Original processed-state cleanup on the SAME literal history. Its
historical native parents are real, root-restored artifacts; no private
support or shadow is used. Complete BP precedes this source.
Original processed-state K3 only; arbitrary entry/K1/fullG4 remain separate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualOriginalProcessedSharpCleanup
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower NormalCrossings
  HironakaG4PreparedCentreCoordinates HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpActualChronologicalStrictStep HironakaActualProcessedMaskFiniteBlock
  HironakaActualOriginalProcessedJointPreparedness
  HironakaG4RecordedTowerResidualCompatibility HironakaSharpActualCurveWholeBoundaryTransversality
  RelativePrincipalizationSpan RestrictedIdealExtension MonomialPartAlong GermIdealOrder
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossingsComparison
  HironakaG4MonomialFamilyInvariant HironakaG4CompactWholeMonomialMaskPhase

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Every original WHOLE I/D/STRICT-J record and literal old/born clock is
derived on this actual geometric tower. No raw/D controlled mark is invented. -/
theorem actual_original_tower_parts_and_clocks (hn : 0<n) {W : Set X}
    {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W\⋃H∈E,H)) (P : BlowupTower X Y)
    (hP : IsGeoTestTower (geometricTemplate W []) P)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) P) :
    let A:=geoTransformAlong (geometricTemplate W []) P
    let F:=(geoTransformAlong (geometricTemplate (univ : Set X) E) P).E
    F=E.map (strictAlong P)++A.E ∧ A.E.length=P.length ∧
      F.length=E.length+P.length ∧
      ∀i : Fin E.length,
        let I:=restrictOn n A.N (vanishingIdeal (n:=n) (strictAlong P (E.get i)))
        let D:=monomialPartAlong n A.N I A.E
        let J:=chronologicalMarked (originalRelativeMemberMarked W (E.get i)) P
        J.N=A.N ∧ J.E=A.E ∧ J.d=0 ∧ J.IsWellFormed ∧
          I.IsCoherent ∧ D.IsCoherent ∧
          nonmonomialPartAlong n A.N I A.E=J.ideal ∧
          I=restrictOn n A.N (D.mul J.ideal) := by
  let A:=geoTransformAlong (geometricTemplate W []) P
  have hRecorded:=actual_recorded_tower_residual_dictionary hn hW hE hdense P hP hFull
  have hBoundary:=actual_whole_ambient_boundary_ordered_dictionary W E P
  have hBornLength : A.E.length=P.length := by
    simpa only [A,geometricTemplate,List.length_nil,Nat.zero_add] using
      length_E_geoTransformAlong (geometricTemplate W []) P
  refine ⟨hBoundary,hBornLength,?_,?_⟩
  · rw [hBoundary,List.length_append,List.length_map,hBornLength]
  · intro i
    obtain ⟨hJN,hJE,hJd,hJwell,_hJnonzero,_hJprincipal⟩:=
      original_members_actual_finite_chronological_geometry hn hW hE hdense i P hP
    obtain ⟨hI,hNonzero,hNm,hFactor⟩:=hRecorded.2.2.2.2 i
    have hBorn:=isSNCDivisor_of_sublist hRecorded.2.1
      (List.sublist_append_right (E.map (strictAlong P)) A.E)
    exact ⟨hJN,hJE,hJd,hJwell,hI,
      isCoherent_monomialPartAlong hn hRecorded.1 hBorn hRecorded.2.2.1 hI hNonzero,hNm,hFactor⟩

/-- Genuine K3 processed cleanup, with joint preparedness INTERNAL and every
original whole-part/STRICT-J record retained on EVERY literal head of U. -/
theorem exists_actual_original_processed_sharp_cleanup (hn : 0<n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W⊆closure (W\⋃H∈E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (hK : IsCompact (originalSharpBadLocus (n:=n) W E))
    (hOrd : ∀x∈(geoTransformAlong (geometricTemplate W []) T).N,
      ∀i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x≤1)
    (hNC : ∀i : Fin E.length,
      let A:=geoTransformAlong (geometricTemplate W []) T
      let S:=A.N∩(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val++A.E))
    (hDenseS : ∀i : Fin E.length,
      let A:=geoTransformAlong (geometricTemplate W []) T
      let S:=A.N∩(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      S⊆closure (S\⋃H∈(E.map (strictAlong T)).eraseIdx i.val++A.E,H)) :
    ∃(Z : CMfd.{u} n)(R : BlowupTower Y Z),
      let U:=T.append R
      let A:=geoTransformAlong (geometricTemplate W []) U
      let F:=(geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
      IsGeoTestTower (geometricTemplate W []) U ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
      CurrentSharpCentres W E U ∧
      RestrictEmptyTower.CentresOver (originalSharpBadLocus (n:=n) W E) U ∧
      (∀x∈A.N,tauD (factorMatrix W E U x)=0) ∧
      IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
      IsProperMap U.proj ∧ IsIsomorphismOver n U.proj (originalSharpBadLocus (n:=n) W E)ᶜ ∧
      ∀k : ℕ,
        let P:=BlowupTowerSplit.head U k
        let B:=geoTransformAlong (geometricTemplate W []) P
        let G:=(geoTransformAlong (geometricTemplate (univ : Set X) E) P).E
        G=E.map (strictAlong P)++B.E ∧ B.E.length=P.length ∧ G.length=E.length+P.length ∧
          ∀i : Fin E.length,
            let I:=restrictOn n B.N (vanishingIdeal (n:=n) (strictAlong P (E.get i)))
            let D:=monomialPartAlong n B.N I B.E
            let J:=chronologicalMarked (originalRelativeMemberMarked W (E.get i)) P
            J.N=B.N ∧ J.E=B.E ∧ J.d=0 ∧ J.IsWellFormed ∧
              I.IsCoherent ∧ D.IsCoherent ∧
              nonmonomialPartAlong n B.N I B.E=J.ideal ∧
              I=restrictOn n B.N (D.mul J.ideal) := by
  have hPrepared:=actual_original_processed_joint_preparedness hn hW hE hdense
    T hT hFull hOrd hNC hDenseS
  obtain ⟨Z,R,hU,hUF,hUS,hOver,hZero,hSmooth,hSNC,hFinalNC,hProper,hIso⟩:=
    HironakaActualProcessedSharpCleanup.exists_actual_processed_sharp_cleanup
      hn hW hE hdense T hT hFull hSharp hK hOrd hNC hDenseS hPrepared
  refine ⟨Z,R,hU,hUF,hUS,hOver,hZero,hSmooth,hSNC,hFinalNC,hProper,hIso,?_⟩
  intro k
  have hHead:=((BlowupTowerSplit.isGeoTestTower_iff_head_tail
    (geometricTemplate W []) (T.append R) k).mp hU).1
  have hHeadFull:=((BlowupTowerSplit.isGeoTestTower_iff_head_tail
    (geometricTemplate (univ : Set X) E) (T.append R) k).mp hUF).1
  exact actual_original_tower_parts_and_clocks hn hW hE hdense
    (BlowupTowerSplit.head (T.append R) k) hHead hHeadFull

end
end Hironaka.HironakaActualOriginalProcessedSharpCleanup
