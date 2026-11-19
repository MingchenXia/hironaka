import Hironaka.Resolution.HironakaG4LowerPreparedNeighborhood

/-! An unprocessed lower residual has its actual old-member trace locally. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4LocalLowerTrace
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers HomogenizedGlueingTower NormalCrossings NormalCrossingsComparison BlowupFlatCoordinates
  HironakaG4ProtectedResidualEndpoint HironakaG4RecordedTowerResidualCompatibility
  HironakaSharpActualAccumulatedTraceResidual HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpOriginalProductTraceOrder RelativePrincipalizationSpan RestrictedIdealExtension
  MonomialPartAlong MonomialCaseAlong MarkedIdeals MarkedIdeals.MarkedIdeal IdealWeightPowers

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Near a point of a prepared processed support, every different original
row's residual support equals the carrier intersected with its actual old
strict-transform member. This is a local statement, not a global equality. -/
theorem other_residual_support_eventually_old_member
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
    (j : Fin E.length) (hne : j ≠ i) {x : Y}
    (hx : x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let J := fun h : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get h)) T).ideal
    ∀ᶠ y in 𝓝 x, y ∈ A.N ∩ (J j).zeroLocus ↔ y ∈ A.N ∩ strictAlong T (E.get j) := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let old := E.map (strictAlong T)
  let J := fun h : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get h)) T).ideal
  let Si := A.N ∩ (J i).zeroLocus
  have hRecorded := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hNi := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i)) T).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N = A.N at hNi
  have hOrdA : ∀ y ∈ A.N, ordinaryTraceOrder A.N (J i) y ≤ 1 := by
    simpa only [hNi] using hOrd
  have hxi : x ∈ Si := by simpa only [hNi] using hx
  have hProtect := actual_original_selected_endpoint_protection hn hW hE hdense i T hT hFull
    hOrdA hNC hDenseS
  let oj : Fin old.length := ⟨j.val, by simpa only [old,List.length_map] using j.isLt⟩
  have hGet : old.get oj = strictAlong T (E.get j) := by simp [old,oj]
  have hOldSNC := isSNCDivisor_of_sublist hRecorded.2.1 (List.sublist_append_left old A.E)
  have hH : IsClosedSubmanifold n (strictAlong T (E.get j)) := by
    rw [←hGet]
    exact MonomialPart.isClosedSubmanifold_get hn hOldSNC oj
  exact support_near_of_whole_trace_germ hH
    ((hProtect.2.2.2.1 j hne x hxi).mono (fun _ hy => hy.2))

end
end Hironaka.HironakaG4LocalLowerTrace
