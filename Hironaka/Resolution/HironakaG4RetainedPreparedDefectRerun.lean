import Hironaka.Resolution.HironakaG4ProtectedRetainedDefectExit
import Hironaka.Resolution.HironakaG4RetainedPreparedOverlapStep

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4RetainedPreparedDefectRerun
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower MarkedIdeals.MarkedIdeal
  NormalCrossings HironakaActualRetainedBoundaryMaskBlock HironakaActualRetainedBornResidualSeed
  HironakaSharpOriginalProductTraceOrder
  HironakaSharpActualFiniteChronologicalHistory
  HironakaG4RetainedPreparedLocalSupport HironakaG4RetainedPreparedOverlapStep
  HironakaG4OrderedRetainedDefectTrace HironakaG4ProtectedRetainedDefectExit
  HironakaG4PreparedCentreCoordinates HironakaSharpActualChronologicalDistinctDefect
  HironakaG4CompactWholeMonomialMaskPhase RestrictEmptyTower

variable {n : ℕ} {X Y : CMfd.{u} n}

set_option maxHeartbeats 600000 in
/-- Preparation and support on an actual current tuple agree with those
on the concatenated history, at the same labelled row. -/
theorem retained_preparation_append_readback (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (g : NativeRetainedGeometry N old born) (i : Fin old.length)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate N born) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T)
    {Z : CMfd.{u} n} (R : BlowupTower Y Z) :
    let A := geoTransformAlong (geometricTemplate N born) T
    let O := old.map (strictAlong T)
    let j : Fin O.length := Fin.cast (List.length_map _).symm i
    (RetainedRowPrepared N old born i (T.append R) ↔
      RetainedRowPrepared A.N O A.E j R) ∧
    retainedRowSupport N old born i (T.append R) =
      retainedRowSupport A.N O A.E j R := by
  intro A O j
  let M := retainedResidualMarked A.N O A.E j
  let J := retainedResidualMarked N old born i
  have hSeed : M = chronologicalMarked J T :=
    retained_seed_eq_chronological_current hn g.carrier g.full g.born_transverse g.dense T hT hFull i
  have hEq : chronologicalMarked M R = chronologicalMarked J (T.append R) := by
    rw [hSeed]
    exact (HironakaG4OriginalSelectedResidualTail.chronological_append_native J T R).symm
  have hSupport : retainedRowSupport N old born i (T.append R) =
      retainedRowSupport A.N O A.E j R := by
    change (chronologicalMarked J (T.append R)).N ∩
      (chronologicalMarked J (T.append R)).ideal.zeroLocus =
      (chronologicalMarked M R).N ∩ (chronologicalMarked M R).ideal.zeroLocus
    rw [hEq]
  have hOld : O.map (strictAlong R) = old.map (strictAlong (T.append R)) := by
    change (old.map (strictAlong T)).map (strictAlong R) = _
    rw [List.map_map]
    exact congrArg (fun f : Set X → Set Z => old.map f)
      (funext fun D => (MemberInterLocusAlong.strictAlong_append T D R).symm)
  have hBoundary : retainedRowBoundary N old born i (T.append R) =
      retainedRowBoundary A.N O A.E j R := by
    change (old.map (strictAlong (T.append R))).eraseIdx i.val ++
      (geoTransformAlong (geometricTemplate N born) (T.append R)).E =
      (O.map (strictAlong R)).eraseIdx j.val ++
        (geoTransformAlong (geometricTemplate A.N A.E) R).E
    rw [hOld,show j.val = i.val from rfl,geoTransformAlong_append]
    exact congrArg (fun D => (old.map (strictAlong (T.append R))).eraseIdx i.val ++ D)
      (MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
        (𝔪 := A) (𝔫 := geometricTemplate A.N A.E) rfl R)
  refine ⟨?_,hSupport⟩
  unfold RetainedRowPrepared
  change ((∀ z ∈ (chronologicalMarked J (T.append R)).N,
      ordinaryTraceOrder (chronologicalMarked J (T.append R)).N
        (chronologicalMarked J (T.append R)).ideal z ≤ 1) ∧
      HasNormalCrossings n (retainedRowSupport N old born i (T.append R))
        (retainedRowBoundary N old born i (T.append R)) ∧ _) ↔
    ((∀ z ∈ (chronologicalMarked M R).N,
      ordinaryTraceOrder (chronologicalMarked M R).N (chronologicalMarked M R).ideal z ≤ 1) ∧
      HasNormalCrossings n (retainedRowSupport A.N O A.E j R) (retainedRowBoundary A.N O A.E j R) ∧ _)
  rw [hEq,hSupport,hBoundary]

set_option maxHeartbeats 600000 in
/-- Preparation and support can be read at the literal native current
tuple of the actual upper history, with the same original label. -/
theorem retained_preparation_current_readback (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (g : NativeRetainedGeometry N old born) (i : Fin old.length)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate N born) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T) :
    let A := geoTransformAlong (geometricTemplate N born) T
    let O := old.map (strictAlong T)
    let j : Fin O.length := Fin.cast (List.length_map _).symm i
    (RetainedRowPrepared N old born i T ↔
      RetainedRowPrepared A.N O A.E j (.refl : BlowupTower Y Y)) ∧
    retainedRowSupport N old born i T =
      retainedRowSupport A.N O A.E j (.refl : BlowupTower Y Y) := by
  exact retained_preparation_append_readback hn g i T hT hFull (.refl : BlowupTower Y Y)

/-- The actual finite ordered rerun preserves any initially prepared row
and pulls its support back along the whole tower. -/
theorem retained_prepared_row_of_ordered_defect_trace (hn : 0 < n)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    (i : Fin old.length) (hPrep : RetainedRowPrepared N old born i (.refl : BlowupTower X X))
    {μ : WithTop RetainedStampRank} {T : BlowupTower X Y}
    (hT : IsGeoTestTower (geometricTemplate N born) T)
    (R : OrderedRetainedDefectTrace hn N old born μ T) :
    RetainedRowPrepared N old born i T ∧
      retainedRowSupport N old born i T =
        T.proj ⁻¹' retainedRowSupport N old born i (.refl : BlowupTower X X) := by
  have hMiss := retained_prepared_support_disjoint_distinct_defect hn g.carrier g.full
    g.born_transverse g.dense i hPrep
  exact retained_prepared_row_of_disjoint_footprint hn g.carrier g.full g.born_transverse
    g.dense i hPrep hMiss T hT (ordered_retained_trace_centresOver_defect R g)

/-- Near any compact enclosure, an actual finite defect rerun retains
all specified prepared rows and their exact pulled-back supports. -/
theorem exists_ordered_retained_defect_exit_preserving_prepared (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    (P : Finset (Fin old.length))
    (hP : ∀ i ∈ P,RetainedRowPrepared N old born i (.refl : BlowupTower X X))
    {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X, K ⊆ U ∧ ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      let u := (Subtype.val : U → X)
      let NU := u ⁻¹' N
      let OU := old.map (u ⁻¹' ·)
      let BU := born.map (u ⁻¹' ·)
      let A := geoTransformAlong (geometricTemplate NU BU) T
      IsGeoTestTower (geometricTemplate NU BU) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set U) (OU ++ BU)) T ∧
      CurrentSharpCentres NU (OU ++ BU) T ∧
      CentresOver (u ⁻¹' actualFamilyDistinctDefect N (oldResidualPart N old born)) T ∧
      actualFamilyDistinctDefect A.N (oldResidualPart A.N (OU.map (strictAlong T)) A.E) = ∅ ∧
      Nonempty (OrderedRetainedDefectTrace hn NU OU BU ⊤ T) ∧
      ∀ i ∈ P,
        let iU : Fin OU.length := Fin.cast (List.length_map _).symm i
        RetainedRowPrepared NU OU BU iU T ∧
          retainedRowSupport NU OU BU iU T =
            (u ∘ T.proj) ⁻¹' retainedRowSupport N old born i (.refl : BlowupTower X X) :=
  exists_protected_ordered_retained_defect_exit_near_compact hn g P hP
    (fun i hi => retained_prepared_support_disjoint_distinct_defect hn g.carrier g.full
      g.born_transverse g.dense i (hP i hi)) hK

end
end Hironaka.HironakaG4RetainedPreparedDefectRerun
