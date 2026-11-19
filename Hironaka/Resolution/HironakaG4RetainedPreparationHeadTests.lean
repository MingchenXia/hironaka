import Hironaka.Resolution.HironakaG4RetainedLowerCompactWindow
import Hironaka.Resolution.HironakaG4RetainedPreparationTrace
import Hironaka.Resolution.HironakaG4SaturatedRetainedEquivariance
import Hironaka.Resolution.HironakaG4RetainedSelectedLowerLift
import Hironaka.Resolution.HironakaG34LowerTemplateBridge

/-! The two literal tests and current retained records of a preparation block. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4RetainedPreparationHeadTests
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerIsoTail
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  MarkedIdealTowerTransport HomogenizedGlueingTower IdealWeightPowers NormalCrossings
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaG4OrderedRetainedDefectTrace HironakaG4PreparedCentreCoordinates
  HironakaActualRetainedBornResidualHistory HironakaG4CompactWholeMonomialMaskPhase
  HironakaG4RetainedSelectedLowerLift HironakaG4RetainedLowerCompactWindow
  HironakaG4SharpTerminalAtlas HironakaG4ResidualInductionInputs HironakaG34LowerTemplateBridge
  HironakaG4SaturatedRetainedEquivariance HironakaG34NonPureLowDim MemberInterLocusAlong

variable {n : ℕ} {X Y Z : CMfd.{u} n} {N : Set X} {old born : List (Set X)}

/-- The carrier test uses the retained born boundary, while the ambient test
uses the entire ordered boundary on the same actual tower. -/
structure BlockTests (N : Set X) (old born : List (Set X)) (T : BlowupTower X Y) : Prop where
  carrier : IsGeoTestTower (geometricTemplate N born) T
  full : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T

theorem BlockTests.current_geometry {hn : 0 < n} (g : NativeRetainedGeometry N old born)
    {T : BlowupTower X Y} (hT : BlockTests N old born T) :
    NativeRetainedGeometry (geoTransformAlong (geometricTemplate N born) T).N
      (old.map (strictAlong T)) (geoTransformAlong (geometricTemplate N born) T).E := by
  have h := actual_retained_born_recorded_residual_dictionary hn g.carrier g.full
    g.born_transverse g.dense T hT.carrier hT.full
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

theorem carrier_template_current (N : Set X) (born : List (Set X)) (T : BlowupTower X Y) :
    geoTransformAlong (geometricTemplate N born) T =
      geometricTemplate (geoTransformAlong (geometricTemplate N born) T).N
        (geoTransformAlong (geometricTemplate N born) T).E := by
  conv_rhs => rw [N_geoTransformAlong]
  exact template_current N born T

/-- The literal retained tuple of a concatenation is computed on the actual
current source of the second block. -/
theorem current_retained_records_append (N : Set X) (old born : List (Set X))
    (T : BlowupTower X Y) (S : BlowupTower Y Z) :
    let A := geoTransformAlong (geometricTemplate N born) T
    geoTransformAlong (geometricTemplate N born) (T.append S) =
        geoTransformAlong (geometricTemplate A.N A.E) S ∧
      old.map (strictAlong (T.append S)) = (old.map (strictAlong T)).map (strictAlong S) := by
  intro A
  constructor
  · rw [geoTransformAlong_append,carrier_template_current N born T]
  · rw [List.map_map]
    exact List.map_congr_left (fun H _ => strictAlong_append T H S)

theorem blockTests_append_iff (T : BlowupTower X Y) (S : BlowupTower Y Z) :
    BlockTests N old born (T.append S) ↔
      BlockTests N old born T ∧
      BlockTests (geoTransformAlong (geometricTemplate N born) T).N
        (old.map (strictAlong T)) (geoTransformAlong (geometricTemplate N born) T).E S := by
  have hCarrier := carrier_template_current N born T
  have hFull : geoTransformAlong (geometricTemplate (univ : Set X) (old ++ born)) T =
      geometricTemplate (univ : Set Y)
        (old.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate N born) T).E) := by
    rw [template_current (univ : Set X) (old ++ born) T,strict_univ T,
      retained_born_full_boundary_ordered_dictionary N old born T]
  constructor
  · intro h
    obtain ⟨hT,hS⟩ := (isGeoTestTower_append_iff _ T S).mp h.carrier
    obtain ⟨hFullT,hFullS⟩ := (isGeoTestTower_append_iff _ T S).mp h.full
    rw [hCarrier] at hS
    rw [hFull] at hFullS
    exact ⟨⟨hT,hFullT⟩,⟨hS,hFullS⟩⟩
  · rintro ⟨⟨hT,hFullT⟩,⟨hS,hFullS⟩⟩
    rw [← hCarrier] at hS
    rw [← hFull] at hFullS
    exact ⟨(isGeoTestTower_append_iff _ T S).mpr ⟨hT,hS⟩,
      (isGeoTestTower_append_iff _ T S).mpr ⟨hFullT,hFullS⟩⟩

theorem BlockTests.restrictOpen {T : BlowupTower X Y} (hT : BlockTests N old born T)
    (g : NativeRetainedGeometry N old born) (O : Opens X) :
    let f := (Subtype.val : O → X)
    BlockTests (f ⁻¹' N) (old.map (f ⁻¹' ·)) (born.map (f ⁻¹' ·)) (restrict O T) := by
  have h := saturated_retained_restricted_head g T hT.carrier hT.full O
  exact ⟨h.1,h.2.1⟩

/-- Under an actual tower isomorphism the literal current triple pulls back,
including the possible empty slots in its full ordered boundary. -/
theorem blockTests_of_actualIso {X' Y' : CMfd.{u} n}
    (g : NativeRetainedGeometry N old born)
    {T : BlowupTower X Y} {T' : BlowupTower X' Y'}
    {e : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {τ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hIso : IsTowerIso e T' T τ) (hT : BlockTests N old born T) :
    let N' := e ⁻¹' N
    let old' := old.map (e ⁻¹' ·)
    let born' := born.map (e ⁻¹' ·)
    let A := geoTransformAlong (geometricTemplate N born) T
    let A' := geoTransformAlong (geometricTemplate N' born') T'
    BlockTests N' old' born' T' ∧
      A'.N = τ ⁻¹' A.N ∧ old'.map (strictAlong T') = (old.map (strictAlong T)).map (τ ⁻¹' ·) ∧
      A'.E = A.E.map (τ ⁻¹' ·) := by
  intro N' old' born' A A'
  have hCarrier := (IsTowerIso.isGeoTestTower_iff e g.carrier isCoherent_unitIdeal hIso).mpr hT.carrier
  rw [template_pullback (X := X) (Y := X')] at hCarrier
  have hFull := (IsTowerIso.isGeoTestTower_iff e isClosedSubmanifold_univ isCoherent_unitIdeal hIso).mpr hT.full
  rw [template_pullback (X := X) (Y := X'),preimage_univ,List.map_append] at hFull
  have hRec := IsTowerIso.geoTransformAlong_eq e g.carrier isCoherent_unitIdeal hIso hT.carrier
  rw [template_pullback (X := X) (Y := X')] at hRec
  have hOld : old'.map (strictAlong T') = (old.map (strictAlong T)).map (τ ⁻¹' ·) := by
    simp only [old',List.map_map]
    exact List.map_congr_left (fun H _ => hIso.strictAlong_eq H)
  exact ⟨⟨hCarrier,hFull⟩,congrArg MarkedIdeal.N hRec,hOld,congrArg MarkedIdeal.E hRec⟩

theorem BlockTests.rebase {X' : CMfd.{u} n} {T : BlowupTower X Y} (hT : BlockTests N old born T)
    (g : NativeRetainedGeometry N old born)
    (e : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) :
    BlockTests (e ⁻¹' N) (old.map (e ⁻¹' ·)) (born.map (e ⁻¹' ·)) (transport e T).tower :=
  (blockTests_of_actualIso g (transport_isTowerIso e T) hT).1

/-- A retained defect run is admissible on both actual upper records. -/
theorem ordered_defect_blockTests {hn : 0 < n} {μ : WithTop RetainedStampRank}
    {T : BlowupTower X Y} (trace : OrderedRetainedDefectTrace hn N old born μ T) :
    BlockTests N old born T := by
  induction trace with
  | done _ => exact ⟨trivial,trivial⟩
  | phase T S _ _ hT hFull _ ih =>
    exact (blockTests_append_iff T S).mpr ⟨⟨hT,hFull⟩,ih⟩
  | restrictOpen O g _ ih => exact ih.restrictOpen g O
  | rebase e g _ ih => exact ih.rebase g e

/-- The selected lower terminal certifies both actual upper tests. -/
theorem lower_blockTests (hn : 0 < n) (g : NativeRetainedGeometry N old born)
    (hEmpty : actualFamilyDistinctDefect N (oldResidualPart N old born) = ∅)
    (i : Fin old.length) {T : BlowupTower X Y}
    (hT : IsSharpTerminalTower (N ∩ (oldResidualPart N old born i).zeroLocus)
      (remainingBoundary old born i) T) : BlockTests N old born T := by
  have hOrd := (retained_row_conditions_of_empty_distinct_defect hn g.carrier g.full
    g.born_transverse g.dense hEmpty).1
  have hLower := lowerTemplate_test_of_two_tests _ _ T hT.carrierTest hT.boundaryTest
  have h := actual_retained_selected_lower_boundary_history hn g.carrier g.full
    g.born_transverse g.dense hOrd i T hLower
  exact ⟨h.1,h.2.1⟩

end
end Hironaka.HironakaG4RetainedPreparationHeadTests
