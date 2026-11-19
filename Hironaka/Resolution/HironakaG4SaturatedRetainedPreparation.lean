import Hironaka.Resolution.HironakaG4SaturatedRetainedContinuation
import Hironaka.Resolution.HironakaG4RetainedPreparationEmbedding

/-! The actual saturated retained append carries each specified prepared row. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4SaturatedRetainedPreparation
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerIsoTail
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  MarkedIdealTowerTransport MaxLocusLocal HomogenizedGlueingTower IdealWeightPowers
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance SimultaneousNormalCrossings
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaG4CompactWholeMonomialMaskPhase HironakaG4PreparedCentreCoordinates
  HironakaActualRetainedBornResidualHistory HironakaG4RetainedCurrentStamp
  HironakaSaturatedTowerAppend HironakaSaturatedMarkedPhase
  HironakaActualProtectedGammaOpenCompatibility HironakaCompactFootprintSharpExtension
  HironakaG4OrderedRetainedDefectTrace HironakaG4RetainedPreparedLocalSupport
  HironakaG4RetainedPreparedDefectRerun HironakaG4RetainedPreparationEmbedding
  HironakaG4SaturatedRetainedContinuation

variable {n : ℕ} {X Y Z : CMfd.{u} n}

set_option maxHeartbeats 900000 in
/-- A saturated append carries the resolved distinct defect and each of the
specified prepared rows on the actual suffix into the same composed
history, retaining their original positions in the old list. -/
theorem exists_saturated_retained_continuation_prepared (hn : 0 < n)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate N born) T)
    (hFullT : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T)
    (hSharpT : CurrentSharpCentres N (old ++ born) T)
    (K : Set X) (V : Opens Y) (hKV : T.proj ⁻¹' K ⊆ V)
    (S : BlowupTower (CMfd.of (n := n) V) Z) (P : Finset (Fin old.length)) :
    let A := geoTransformAlong (geometricTemplate N born) T
    let v := (Subtype.val : V → Y)
    let NV := v ⁻¹' A.N
    let OV := (old.map (strictAlong T)).map (v ⁻¹' ·)
    let BV := A.E.map (v ⁻¹' ·)
    let eV : Fin old.length ≃ Fin OV.length := finCongr (by simp [OV])
    IsGeoTestTower (geometricTemplate NV BV) S →
    IsGeoTestTower (geometricTemplate (univ : Set V) (OV ++ BV)) S →
    CurrentSharpCentres NV (OV ++ BV) S →
    (let AS := geoTransformAlong (geometricTemplate (X := CMfd.of (n := n) V) NV BV) S
     actualFamilyDistinctDefect AS.N
       (oldResidualPart AS.N (OV.map (strictAlong S)) AS.E) = ∅) →
    (∀ i ∈ P,RetainedRowPrepared NV OV BV (eV i) S) →
    ∃ O : Opens X, K ⊆ O ∧ ∃ (hOV : openPreimage T O ≤ V),
      let D := nestedOpens V (openPreimage T O)
      let tail := transport (nestedOpensDiffeo (n := n) hOV).symm (restrict D S)
      let Q := (restrict O T).append tail.tower
      let ν := (Subtype.val : O → X)
      let NO := ν ⁻¹' N
      let OO := old.map (ν ⁻¹' ·)
      let BO := born.map (ν ⁻¹' ·)
      let AQ := geoTransformAlong (geometricTemplate NO BO) Q
      let eO : Fin old.length ≃ Fin OO.length := finCongr (List.length_map _).symm
      IsGeoTestTower (geometricTemplate NO BO) Q ∧
      IsGeoTestTower (geometricTemplate (univ : Set O) (OO ++ BO)) Q ∧
      CurrentSharpCentres NO (OO ++ BO) Q ∧
      actualFamilyDistinctDefect AQ.N (oldResidualPart AQ.N (OO.map (strictAlong Q)) AQ.E) = ∅ ∧
      ∀ i ∈ P,RetainedRowPrepared NO OO BO (eO i) Q := by
  intro A v NV OV BV eV hS hFullS hSharpS hEnd hPrep
  obtain ⟨O,hKO,hOV,hQ,hFullQ,hSharpQ,hb,hFinal,hAQ,hO,hB⟩ :=
    exists_saturated_retained_continuation_native hn g.carrier g.full g.born_transverse g.dense
      T hT hFullT hSharpT K V hKV S hS hFullS hSharpS
  let D := nestedOpens V (openPreimage T O)
  let tail := transport (nestedOpensDiffeo (n := n) hOV).symm (restrict D S)
  let Q := (restrict O T).append tail.tower
  let ν := (Subtype.val : O → X)
  let NO := ν ⁻¹' N
  let OO := old.map (ν ⁻¹' ·)
  let BO := born.map (ν ⁻¹' ·)
  let AQ := geoTransformAlong (geometricTemplate NO BO) Q
  let OQ := OO.map (strictAlong Q)
  let eO : Fin old.length ≃ Fin OO.length := finCongr (List.length_map _).symm
  let AS := geoTransformAlong (geometricTemplate (X := CMfd.of (n := n) V) NV BV) S
  let OS := OV.map (strictAlong S)
  let b : tail.target → Z := fun z => (tail.back z).val
  have hG : NativeRetainedGeometry A.N (old.map (strictAlong T)) A.E := by
    have h := actual_retained_born_recorded_residual_dictionary hn g.carrier g.full
      g.born_transverse g.dense T hT hFullT
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩
  have hGV : NativeRetainedGeometry (X := CMfd.of (n := n) V) NV OV BV := hG.restrict V
  refine ⟨O,hKO,hOV,hQ,hFullQ,hSharpQ,?_,?_⟩
  · change actualFamilyDistinctDefect AQ.N (oldResidualPart AQ.N OQ AQ.E) = ∅
    change AQ.N = b ⁻¹' AS.N at hAQ
    change OQ = OS.map (b ⁻¹' ·) at hO
    change AQ.E = AS.E.map (b ⁻¹' ·) at hB
    rw [hAQ,hO,hB,actual_retained_defect_open_embedding hn hFinal.carrier hFinal.full
      hFinal.born_transverse hFinal.dense _ hb,hEnd,Set.preimage_empty]
  · intro i hi
    change RetainedRowPrepared NO OO BO (eO i) Q
    exact (retained_preparation_of_endpoint_open_embedding hn hGV (g.restrict O)
      S hS hFullS Q hQ hFullQ b hb (eV i) (eO i) rfl hAQ hO hB (hPrep i hi)).1

end
end Hironaka.HironakaG4SaturatedRetainedPreparation
