import Hironaka.Resolution.HironakaG34DefectEmptyOrder
import Hironaka.Resolution.HironakaG34DefectExitEquivariance

/-! # The protected carrier-preparation phase with an equivariance conclusion (ninth brick of EQ_d)

Lane G34 (run 0080, round 9).  Blueprint: `hironaka-g34-resume-carrier-phase-equivariance.tex`.

`HironakaG34DefectEmptyOrder.exists_actual_carrier_phase_protected` (the carrier phase of the sharp row loop) built from the
equivariant true-defect exit of `HironakaG34DefectExitEquivariance`: same outputs, plus "an equivariant prefix stays
equivariant".

* `exists_actual_carrier_phase_protected_equivariant`. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaG34CarrierPhaseEquivariance
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealOperationsAlong NormalCrossings HironakaActualDefectProfileWindows
  HironakaG4RecordedTowerResidualCompatibility HironakaG4CompactWholeMonomialMaskPhase HironakaG4SharpBadFootprint
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualFiniteMemberProduct HironakaSharpActualChronologicalDistinctDefect GermIdealOrder
  RestrictEmptyTower HironakaG34MaskFoldEquivariance HironakaSharpOriginalProductTraceOrder DivisorExponentAlong
open ResolutionInvariantExt (IsEmptyTower)
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- A compact current chronological defect admits a protected actual
carrier phase. Every prepared original row has a whole neighborhood
over which the chosen tail has only empty centres. -/
theorem exists_actual_carrier_phase_protected_equivariant_of_compact_defect (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hReg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (hCompact : IsCompact (chronologicalDistinctDefect W E T)) :
    ∃ (Z : CMfd.{u} n) (Q : BlowupTower Y Z),
      IsGeoTestTower (geometricTemplate W []) (T.append Q) ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append Q) ∧
      CurrentSharpCentres W E (T.append Q) ∧
      CentresOver (chronologicalDistinctDefect W E T) Q ∧
      chronologicalDistinctDefect W E (T.append Q) = ∅ ∧
      (∀ x ∈ (geoTransformAlong (geometricTemplate W []) (T.append Q)).N, ∀ a : Fin E.length,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append Q)).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) (T.append Q)).ideal x ≤ 1) ∧
      (IsEquivariant W E T → IsEquivariant W E (T.append Q)) ∧
      ∀ i : Fin E.length,
        (∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
          ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
            (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1) →
        (let A := geoTransformAlong (geometricTemplate W []) T
          let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
          HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E)) →
        (let A := geoTransformAlong (geometricTemplate W []) T
          let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
          S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H)) →
        ∃ U : Opens Y,
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
            (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus ⊆ U ∧
          IsEmptyTower (restrict U Q) := by
  obtain ⟨Z,Q,hTQ,hFullTQ,hSharpTQ,_hRows,_hFoot,hOver,hEquiv,hEmpty⟩ :=
    HironakaG34DefectExitEquivariance.exists_actual_global_original_distinct_defect_exit_equivariant_of_compact_defect
      hn hW hE hdense d hReg T hT hFull hSharp hCompact
  refine ⟨Z,Q,hTQ,hFullTQ,hSharpTQ,hOver,hEmpty,
    HironakaG34DefectEmptyOrder.ordinaryTraceOrder_le_one_of_distinctDefect_eq_empty hn hW hE hdense (T.append Q)
      hTQ hEmpty,
    hEquiv,fun i hOrd hNC hDenseS => ?_⟩
  obtain ⟨U,hUeq,hSU⟩ := HironakaG34PreparedRowDefectFree.actual_prepared_row_defect_free_near
    hn hW hE hdense d hReg i T hT hFull hOrd hNC hDenseS
  refine ⟨U,hSU,isEmptyTower_restrict_of_centresOver U ?_ Q hOver⟩
  rw [hUeq]
  exact disjoint_compl_left

/-- **The protected carrier-preparation phase, equivariant**: the outputs of
`HironakaG34DefectEmptyOrder.exists_actual_carrier_phase_protected`, plus: an equivariant prefix stays equivariant. -/
theorem exists_actual_carrier_phase_protected_equivariant (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hReg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T) :
    ∃ (Z : CMfd.{u} n) (Q : BlowupTower Y Z),
      IsGeoTestTower (geometricTemplate W []) (T.append Q) ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append Q) ∧
      CurrentSharpCentres W E (T.append Q) ∧
      CentresOver (chronologicalDistinctDefect W E T) Q ∧
      chronologicalDistinctDefect W E (T.append Q) = ∅ ∧
      (∀ x ∈ (geoTransformAlong (geometricTemplate W []) (T.append Q)).N, ∀ a : Fin E.length,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append Q)).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) (T.append Q)).ideal x ≤ 1) ∧
      (IsEquivariant W E T → IsEquivariant W E (T.append Q)) ∧
      ∀ i : Fin E.length,
        (∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
          ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
            (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1) →
        (let A := geoTransformAlong (geometricTemplate W []) T
          let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
          HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E)) →
        (let A := geoTransformAlong (geometricTemplate W []) T
          let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
          S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H)) →
        ∃ U : Opens Y,
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
            (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus ⊆ U ∧
          IsEmptyTower (restrict U Q) :=
  exists_actual_carrier_phase_protected_equivariant_of_compact_defect hn hW hE hdense d hReg T hT hFull hSharp
    (isCompact_actual_chronological_distinct_defect hn hW hE hdense d hReg hK T hT hFull hSharp)

end
end Hironaka.HironakaG34CarrierPhaseEquivariance
