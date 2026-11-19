import Hironaka.Resolution.HironakaG4ActualUnitWindowProtection
import Hironaka.Resolution.HironakaActualProtectedOtherRowLocalStep

/-! A processed original row is protected at its unit points. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4OriginalUnitStepProtection
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms BlowupFlatCoordinates BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaSharpActualFiniteChronologicalHistory HironakaG4PreparedCentreCoordinates
  HironakaG4RecordedTowerResidualCompatibility HironakaActualProtectedOtherRowLocalStep
  HironakaG4ActualUnitWindowProtection HironakaG34LowerCleanupLift
  HironakaSharpOriginalProductTraceOrder RelativePrincipalizationSpan RestrictedIdealExtension
  MonomialPartAlong NonmonomialTransformAlong DivisorExponentAlong

variable {n : ℕ} {X Y Z Q : CMfd.{u} n}

/-- A selected prepared native row has an actual protected window at a
source unit point of the lower and full-boundary test step. -/
theorem native_prepared_row_unit_step_certificate
    (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hFull : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hDense : N ⊆ closure (N \ ⋃ D ∈ old ++ born,D))
    (i : Fin old.length)
    (hOrd : ∀ y ∈ N, ordinaryTraceOrder N (oldResidualPart N old born i) y ≤ 1)
    (hNC : HasNormalCrossings n (N ∩ (oldResidualPart N old born i).zeroLocus)
      (old.eraseIdx i.val ++ born))
    (hDenseS : N ∩ (oldResidualPart N old born i).zeroLocus ⊆
      closure ((N ∩ (oldResidualPart N old born i).zeroLocus) \ ⋃ D ∈ old.eraseIdx i.val ++ born,D))
    (P B : MarkedIdeal n X) (hPN : P.N ⊆ N) (hBE : B.E = old ++ born)
    (R : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hTest : IsGeoTestTower P (.step R C π hπ))
    (hB : IsGeoTestTower B (.step R C π hπ)) (x : Y)
    (hxi : R.proj x ∈ N ∩ (oldResidualPart N old born i).zeroLocus)
    (hUnit : (oldMonomialPart N old born i).mem (R.proj x) 1) :
    let S := N ∩ (oldResidualPart N old born i).zeroLocus
    ProtectedWindowAt (strictAlong R N) (strictAlong R S)
      ((old.eraseIdx i.val ++ born).map (strictAlong R) ++
        (geoTransformAlong (geometricTemplate N []) R).E) C x := by
  obtain ⟨U,hxU,_,Haux,hEF,hTF,hSlice,hRes⟩ :=
    native_prepared_source_slice_window hn hN hFull hTr hDense i hOrd hNC hDenseS hxi ⊤ (by trivial)
  have hxAux : (⟨R.proj x,hxU⟩ : U) ∈ Haux :=
    ((Set.ext_iff.mp hSlice ⟨R.proj x,hxU⟩).mp hxi).2
  exact actual_unit_window_protects_full_test_step hn P B N _ old born hPN hBE hN hFull
    hTr hDense i U Haux hEF hTF hSlice hRes R C π hπ hTest hB x hxU hxi.1 hxAux hUnit

/-- The original prepared-row hypotheses produce a protected certificate at
any unit point of an arbitrary lower and full-boundary test step. -/
theorem original_prepared_row_unit_step_certificate
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (i : Fin E.length) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1)
    (hNC : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDenseS : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H))
    (P B : MarkedIdeal n Y)
    (hPN : P.N ⊆ (geoTransformAlong (geometricTemplate W []) T).N)
    (hBE : B.E = (E.map (strictAlong T)) ++ (geoTransformAlong (geometricTemplate W []) T).E)
    (R : BlowupTower Y Z) (C : Set Z) (π : Q → Z) (hπ : IsBlowupAlong n C π)
    (hTest : IsGeoTestTower P (.step R C π hπ))
    (hB : IsGeoTestTower B (.step R C π hπ)) (x : Z)
    (hxi : R.proj x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus)
    (hunit : let A := geoTransformAlong (geometricTemplate W []) T
      let old := E.map (strictAlong T)
      let oi : Fin old.length := ⟨i.val,by simpa only [old,List.length_map] using i.isLt⟩
      (oldMonomialPart A.N old A.E oi).mem (R.proj x) 1) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let Si := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
    let K := geometricTemplate A.N []
    ProtectedWindowAt (strictAlong R A.N) (strictAlong R Si)
      (((E.map (strictAlong T)).eraseIdx i.val ++ A.E).map (strictAlong R) ++
        (geoTransformAlong K R).E) C x := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let old := E.map (strictAlong T)
  let J := (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  let oi : Fin old.length := ⟨i.val,by simpa only [old,List.length_map] using i.isLt⟩
  have hGeti : old.get oi = strictAlong T (E.get i) := by simp [old,oi]
  have hNi := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i)) T).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N = A.N at hNi
  have hRecorded := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hJ : oldResidualPart A.N old A.E oi = J := by
    simpa only [oldResidualPart,oldTraceIdeal,hGeti] using (hRecorded.2.2.2.2 i).2.2.1
  have hOrd' : ∀ y ∈ A.N, ordinaryTraceOrder A.N (oldResidualPart A.N old A.E oi) y ≤ 1 := by
    rw [hJ,←hNi]
    exact hOrd
  have hNC' : HasNormalCrossings n (A.N ∩ (oldResidualPart A.N old A.E oi).zeroLocus)
      (old.eraseIdx oi.val ++ A.E) := by rw [hJ]; exact hNC
  have hD' : A.N ∩ (oldResidualPart A.N old A.E oi).zeroLocus ⊆
      closure ((A.N ∩ (oldResidualPart A.N old A.E oi).zeroLocus) \
        ⋃ D ∈ old.eraseIdx oi.val ++ A.E,D) := by rw [hJ]; exact hDenseS
  have hXi : R.proj x ∈ A.N ∩ (oldResidualPart A.N old A.E oi).zeroLocus := by
    rw [hJ,←hNi]
    exact hxi
  have hCert := native_prepared_row_unit_step_certificate hn hRecorded.1 hRecorded.2.1
    hRecorded.2.2.1 hRecorded.2.2.2.1 oi hOrd' hNC' hD' P B hPN hBE R C π hπ hTest hB x hXi hunit
  change ProtectedWindowAt (strictAlong R A.N) (strictAlong R (A.N ∩ (oldResidualPart A.N old A.E oi).zeroLocus))
    ((old.eraseIdx oi.val ++ A.E).map (strictAlong R) ++
      (geoTransformAlong (geometricTemplate A.N []) R).E) C x at hCert
  rw [hJ] at hCert
  exact hCert

end
end Hironaka.HironakaG4OriginalUnitStepProtection
