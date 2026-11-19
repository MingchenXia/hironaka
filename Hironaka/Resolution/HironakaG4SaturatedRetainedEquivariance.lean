import Hironaka.Resolution.HironakaG4SaturatedRetainedContinuation
import Hironaka.Resolution.HironakaG4RetainedDefectTraceEquivariance
import Hironaka.Resolution.HironakaG4RetainedPreparationLowerHistory

/-! Strict equivariance of the same literal saturated retained append. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4SaturatedRetainedEquivariance
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  MarkedIdealTowerTransport MaxLocusLocal HomogenizedGlueingTower IdealWeightPowers
  HironakaSharpActualFiniteChronologicalHistory HironakaG4OrderedRetainedDefectTrace
  HironakaG4RetainedDefectTraceEquivariance HironakaG34MaskFoldEquivariance
  HironakaG34NonPureLowDim NormalCrossings HironakaG4RetainedPreparationTrace
  HironakaActualRetainedBornResidualHistory HironakaG4RetainedPreparationLowerHistory

variable {n : ℕ} {X Y Z : CMfd.{u} n}

theorem saturated_retained_restricted_head {N : Set X} {old born : List (Set X)}
    (g : NativeRetainedGeometry N old born)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate N born) T)
    (hFullT : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T)
    (O : Opens X) :
    let u := (Subtype.val : openPreimage T O → Y)
    let ν := (Subtype.val : O → X)
    let NO := ν ⁻¹' N
    let OO := old.map (ν ⁻¹' ·)
    let BO := born.map (ν ⁻¹' ·)
    let A := geoTransformAlong (geometricTemplate N born) T
    let L := restrict O T
    let AL := geoTransformAlong (geometricTemplate NO BO) L
    IsGeoTestTower (geometricTemplate NO BO) L ∧
    IsGeoTestTower (geometricTemplate (univ : Set O) (OO ++ BO)) L ∧
    AL.N = u ⁻¹' A.N ∧ OO.map (strictAlong L) = (old.map (strictAlong T)).map (u ⁻¹' ·) ∧
    AL.E = A.E.map (u ⁻¹' ·) := by
  intro w ν NO OO BO A L AL
  let XO := CMfd.of (n := n) O
  let M := geometricTemplate N born
  let F := geometricTemplate (univ : Set X) (old ++ born)
  let MO := geometricTemplate (X := XO) NO BO
  let FO := geometricTemplate (X := XO) (univ : Set O) (OO ++ BO)
  have hM : MarkedIdeal.pullback ν M = MO := template_pullback (X := X) (Y := XO) ν N born
  have hF : MarkedIdeal.pullback ν F = FO := by
    rw [template_pullback (X := X) (Y := XO) ν,Set.preimage_univ,List.map_append]
  have hML := isGeoTestTower_restrict O g.carrier isCoherent_unitIdeal T hT
  have hFL := isGeoTestTower_restrict O isClosedSubmanifold_univ isCoherent_unitIdeal T hFullT
  have hMRec := geoTransformAlong_restrict O g.carrier isCoherent_unitIdeal T hT
  rw [hM] at hML hMRec
  rw [hF] at hFL
  have hOld : OO.map (strictAlong L) = (old.map (strictAlong T)).map (w ⁻¹' ·) := by
    simp only [OO,List.map_map]
    exact List.map_congr_left (fun H _ => strictAlong_restrict O T H)
  exact ⟨hML,hFL,congrArg MarkedIdeal.N hMRec,hOld,congrArg MarkedIdeal.E hMRec⟩

set_option maxHeartbeats 650000 in
/-- The literal saturated restriction and append preserve strict local
equivariance for the carrier and the full ordered original boundary. -/
theorem isEquivariant_saturated_retained_append {N : Set X} {old born : List (Set X)}
    (g : NativeRetainedGeometry N old born)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate N born) T)
    (hFullT : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T)
    (hEqT : IsEquivariant N (old ++ born) T)
    (V : Opens Y) (S : BlowupTower (CMfd.of (n := n) V) Z)
    (O : Opens X) (hOV : openPreimage T O ≤ V) :
    let A := geoTransformAlong (geometricTemplate N born) T
    let v := (Subtype.val : V → Y)
    let NV := v ⁻¹' A.N
    let OV := (old.map (strictAlong T)).map (v ⁻¹' ·)
    let BV := A.E.map (v ⁻¹' ·)
    IsEquivariant NV (OV ++ BV) S →
    let D := nestedOpens V (openPreimage T O)
    let tail := transport (nestedOpensDiffeo (n := n) hOV).symm (restrict D S)
    let Q := (restrict O T).append tail.tower
    let ν := (Subtype.val : O → X)
    let NO := ν ⁻¹' N
    let OO := old.map (ν ⁻¹' ·)
    let BO := born.map (ν ⁻¹' ·)
    IsEquivariant NO (OO ++ BO) Q := by
  intro A v NV OV BV hEqS D tail Q ν NO OO BO
  let U := openPreimage T O
  let w := (Subtype.val : U → Y)
  let d := (Subtype.val : D → V)
  let e := (nestedOpensDiffeo (n := n) hOV).symm
  let L := restrict O T
  obtain ⟨hML,hFL,hN,hOld,hBorn⟩ := saturated_retained_restricted_head g T hT hFullT O
  have hEqL : IsEquivariant NO (OO ++ BO) L := by
    simpa only [List.map_append] using isEquivariant_restrictOpen hEqT O
  have hEqTail := isEquivariant_of_actualIso (transport_isTowerIso e (restrict D S))
    (isEquivariant_restrictOpen hEqS D)
  have hCarrier : e ⁻¹' (d ⁻¹' NV) = w ⁻¹' A.N := rfl
  have hBoundary : ((OV ++ BV).map (d ⁻¹' ·)).map (e ⁻¹' ·) =
      ((old.map (strictAlong T)).map (w ⁻¹' ·)) ++ A.E.map (w ⁻¹' ·) := by
    simp only [OV,BV,List.map_append,List.map_map]
    rfl
  have hEqQ : IsEquivariant NO (OO ++ BO) Q := by
    apply IsEquivariant.append_of_current (g.restrict O).carrier L hML hFL hEqL tail.tower
    rw [hN,hOld,hBorn]
    change IsEquivariant (w ⁻¹' A.N) (((old.map (strictAlong T)).map (w ⁻¹' ·)) ++ A.E.map (w ⁻¹' ·)) tail.tower
    rw [hCarrier,hBoundary] at hEqTail
    exact hEqTail
  exact hEqQ


set_option maxHeartbeats 650000 in
/-- The same physical saturation retains both recorded groups and the
concatenation of their recorded phases. -/
theorem retained_trace_saturated_append_using (P : SharpHistoryPredicate.{u} n) (hn : 0 < n)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate N born) T)
    (hFullT : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T)
    {phases later : List RetainedPreparationPhase} (rT : RetainedPreparationTrace hn N old born phases T) (hTraceT : usesLowerHistory P rT)
    (V : Opens Y) (S : BlowupTower (CMfd.of (n := n) V) Z)
    (O : Opens X) (hOV : openPreimage T O ≤ V) :
    let A := geoTransformAlong (geometricTemplate N born) T
    let v := (Subtype.val : V → Y)
    let NV := v ⁻¹' A.N
    let OV := (old.map (strictAlong T)).map (v ⁻¹' ·)
    let BV := A.E.map (v ⁻¹' ·)
    ∀ (rS : RetainedPreparationTrace hn NV OV BV later S),usesLowerHistory P rS →
    let D := nestedOpens V (openPreimage T O)
    let tail := transport (nestedOpensDiffeo (n := n) hOV).symm (restrict D S)
    let Q := (restrict O T).append tail.tower
    let ν := (Subtype.val : O → X)
    let NO := ν ⁻¹' N
    let OO := old.map (ν ⁻¹' ·)
    let BO := born.map (ν ⁻¹' ·)
    ∃ r : RetainedPreparationTrace hn NO OO BO (phases ++ later) Q,usesLowerHistory P r := by
  intro A v NV OV BV rS hTraceS D tail Q ν NO OO BO
  let U := openPreimage T O
  let w := (Subtype.val : U → Y)
  let d := (Subtype.val : D → V)
  let e := (nestedOpensDiffeo (n := n) hOV).symm
  let L := restrict O T
  obtain ⟨hML,hFL,hN,hOld,hBorn⟩ := saturated_retained_restricted_head g T hT hFullT O
  have hRec := actual_retained_born_recorded_residual_dictionary hn g.carrier g.full
    g.born_transverse g.dense T hT hFullT
  have gY : NativeRetainedGeometry A.N (old.map (strictAlong T)) A.E :=
    ⟨hRec.1,hRec.2.1,hRec.2.2.1,hRec.2.2.2.1⟩
  have gV : NativeRetainedGeometry (X := CMfd.of (n := n) V) NV OV BV := gY.restrict V
  let rL := rT.restrictOpen O g
  let rD := (rS.restrictOpen D gV).rebase e (gV.restrict D)
  let AL := geoTransformAlong (geometricTemplate NO BO) L
  have hU : e ⁻¹' (d ⁻¹' NV) = w ⁻¹' A.N := rfl
  have hO : ((OV.map (d ⁻¹' ·)).map (e ⁻¹' ·)) = (old.map (strictAlong T)).map (w ⁻¹' ·) := by
    simp only [OV,List.map_map]
    rfl
  have hB : ((BV.map (d ⁻¹' ·)).map (e ⁻¹' ·)) = A.E.map (w ⁻¹' ·) := by
    simp only [BV,List.map_map]
    rfl
  have hD : ∃ r : RetainedPreparationTrace hn (e ⁻¹' (d ⁻¹' NV))
      ((OV.map (d ⁻¹' ·)).map (e ⁻¹' ·)) ((BV.map (d ⁻¹' ·)).map (e ⁻¹' ·)) later tail.tower,
      usesLowerHistory P r := by
    refine ⟨rD,?_⟩
    change usesLowerHistory P rS
    exact hTraceS
  have hTail : ∃ r : RetainedPreparationTrace hn AL.N (OO.map (strictAlong L)) AL.E later tail.tower,
      usesLowerHistory P r := by
    rw [hU,hO,hB] at hD
    change AL.N = w ⁻¹' A.N at hN
    change OO.map (strictAlong L) = (old.map (strictAlong T)).map (w ⁻¹' ·) at hOld
    change AL.E = A.E.map (w ⁻¹' ·) at hBorn
    rw [hN,hOld,hBorn]
    exact hD
  obtain ⟨rTail,hTraceTail⟩ := hTail
  refine ⟨RetainedPreparationTrace.append L tail.tower (g.restrict O) hML hFL rL rTail,?_⟩
  change usesLowerHistory P rT ∧ usesLowerHistory P rTail
  exact ⟨hTraceT,hTraceTail⟩

/-- Physical saturation retains the two actual preparation histories. -/
theorem retained_trace_saturated_append (hn : 0 < n)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate N born) T)
    (hFullT : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T)
    {phases later : List RetainedPreparationPhase} (rT : RetainedPreparationTrace hn N old born phases T)
    (V : Opens Y) (S : BlowupTower (CMfd.of (n := n) V) Z)
    (O : Opens X) (hOV : openPreimage T O ≤ V) :
    let A := geoTransformAlong (geometricTemplate N born) T
    let v := (Subtype.val : V → Y)
    let NV := v ⁻¹' A.N
    let OV := (old.map (strictAlong T)).map (v ⁻¹' ·)
    let BV := A.E.map (v ⁻¹' ·)
    RetainedPreparationTrace hn NV OV BV later S →
    let D := nestedOpens V (openPreimage T O)
    let tail := transport (nestedOpensDiffeo (n := n) hOV).symm (restrict D S)
    let Q := (restrict O T).append tail.tower
    let ν := (Subtype.val : O → X)
    let NO := ν ⁻¹' N
    let OO := old.map (ν ⁻¹' ·)
    let BO := born.map (ν ⁻¹' ·)
    Nonempty (RetainedPreparationTrace hn NO OO BO (phases ++ later) Q) := by
  intro A v NV OV BV rS D tail Q ν NO OO BO
  obtain ⟨r,_⟩ := retained_trace_saturated_append_using (fun {_ _} _ _ _ => True)
    hn g T hT hFullT rT (usesLowerHistory_unrestricted rT) V S O hOV rS (usesLowerHistory_unrestricted rS)
  exact ⟨r⟩

end
end Hironaka.HironakaG4SaturatedRetainedEquivariance
