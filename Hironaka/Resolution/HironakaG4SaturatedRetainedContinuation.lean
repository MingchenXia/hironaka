import Hironaka.Resolution.HironakaG4RetainedCurrentStamp
import Hironaka.Resolution.HironakaSaturatedTowerAppend
import Hironaka.Resolution.HironakaSaturatedMarkedPhase
import Hironaka.Resolution.HironakaActualProtectedGammaOpenCompatibility
import Hironaka.Resolution.HironakaCompactFootprintSharpExtension
import Hironaka.Resolution.HironakaG4OrderedRetainedDefectTrace

/-! Continue a sharp retained history on a saturated smaller source open.
Both physical tests and the exact terminal native defect are preserved. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4SaturatedRetainedContinuation
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
  HironakaG4OrderedRetainedDefectTrace

variable {n : ℕ} {X Y Z : CMfd.{u} n}

set_option maxHeartbeats 700000 in
/-- The actual saturated append preserves both geometric tests, sharpness,
and the literal current carrier and old/born lists under its actual
endpoint open embedding. -/
theorem exists_saturated_retained_continuation_native (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate N born) T)
    (hFullT : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T)
    (hSharpT : CurrentSharpCentres N (old ++ born) T)
    (K : Set X) (V : Opens Y) (hKV : T.proj ⁻¹' K ⊆ V)
    (S : BlowupTower (CMfd.of (n := n) V) Z) :
    let A := geoTransformAlong (geometricTemplate N born) T
    let v := (Subtype.val : V → Y)
    let NV := v ⁻¹' A.N
    let OV := (old.map (strictAlong T)).map (v ⁻¹' ·)
    let BV := A.E.map (v ⁻¹' ·)
    IsGeoTestTower (geometricTemplate NV BV) S →
    IsGeoTestTower (geometricTemplate (univ : Set V) (OV ++ BV)) S →
    CurrentSharpCentres NV (OV ++ BV) S →
    ∃ O : Opens X, K ⊆ O ∧ ∃ (hOV : openPreimage T O ≤ V),
      let D := nestedOpens V (openPreimage T O)
      let tail := transport (nestedOpensDiffeo (n := n) hOV).symm (restrict D S)
      let Q := (restrict O T).append tail.tower
      let ν := (Subtype.val : O → X)
      let NO := ν ⁻¹' N
      let OO := old.map (ν ⁻¹' ·)
      let BO := born.map (ν ⁻¹' ·)
      let AQ := geoTransformAlong (geometricTemplate NO BO) Q
      let AS := geoTransformAlong (geometricTemplate NV BV) S
      let OS := OV.map (strictAlong S)
      let b : tail.target → Z := fun z => (tail.back z).val
      IsGeoTestTower (geometricTemplate NO BO) Q ∧
      IsGeoTestTower (geometricTemplate (univ : Set O) (OO ++ BO)) Q ∧
      CurrentSharpCentres NO (OO ++ BO) Q ∧
      HironakaBaseChange.IsOpenHoloEmbedding n b ∧
      NativeRetainedGeometry AS.N OS AS.E ∧
      AQ.N = b ⁻¹' AS.N ∧ OO.map (strictAlong Q) = OS.map (b ⁻¹' ·) ∧
      AQ.E = AS.E.map (b ⁻¹' ·) := by
  intro A v NV OV BV hS hFullS hSharpS
  let M := geometricTemplate N born
  let F := geometricTemplate (univ : Set X) (old ++ born)
  let AFull := geoTransformAlong F T
  let OY := old.map (strictAlong T)
  have hWF : M.IsWellFormed :=
    ⟨hN,isCoherent_unitIdeal,isSNCDivisor_of_sublist hE (List.sublist_append_right _ _),hTr⟩
  have hWFF : F.IsWellFormed :=
    ⟨isClosedSubmanifold_univ,isCoherent_unitIdeal,hE,isTransverse_univ_of_isSNCDivisor hE⟩
  have hWA := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hWF T hT
  have hWAF := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hWFF T hFullT
  have hTemplate : A = geometricTemplate A.N A.E := by
    rw [show A.N = strictAlong T N from N_geoTransformAlong _ T]
    exact template_current N born T
  have hFullTemplate : AFull = geometricTemplate (univ : Set Y) (OY ++ A.E) := by
    rw [show AFull = geometricTemplate (strictAlong T (univ : Set X)) AFull.E from
      template_current (univ : Set X) (old ++ born) T,strict_univ]
    rw [show AFull.E = OY ++ A.E from retained_born_full_boundary_ordered_dictionary N old born T]
  have hSP : IsGeoTestTower (MarkedIdeal.pullback v A) S := by
    rw [hTemplate,HironakaG34NonPureLowDim.template_pullback (X := Y)
      (Y := CMfd.of (n := n) V) v]
    exact hS
  have hSFP : IsGeoTestTower (MarkedIdeal.pullback v AFull) S := by
    rw [hFullTemplate,HironakaG34NonPureLowDim.template_pullback (X := Y)
      (Y := CMfd.of (n := n) V) v,Set.preimage_univ,List.map_append]
    exact hFullS
  obtain ⟨O,hKO,hOV,hIso,_hProj,_hTotal,_hRange,hStrict,_hGeometric⟩ :=
    exists_saturated_tower_append T K V hKV S
  let U := openPreimage T O
  let D := nestedOpens V U
  let e := (nestedOpensDiffeo (n := n) hOV).symm
  let tail := transport e (restrict D S)
  let L := restrict O T
  let Q := L.append tail.tower
  let b : tail.target → Z := fun z => (tail.back z).val
  let XO := CMfd.of (n := n) O
  let XU := CMfd.of (n := n) U
  let ν := (Subtype.val : O → X)
  let u := (Subtype.val : U → Y)
  let NO := ν ⁻¹' N
  let OO := old.map (ν ⁻¹' ·)
  let BO := born.map (ν ⁻¹' ·)
  let MO := geometricTemplate (X := XO) NO BO
  let FO := geometricTemplate (X := XO) (univ : Set O) (OO ++ BO)
  let FU := (OY ++ A.E).map (u ⁻¹' ·)
  let NU := u ⁻¹' A.N
  obtain ⟨hML,hMT,_hME,hMEnd⟩ :=
    saturated_marked_phase_restrict M hWF T hT A hWA rfl V S hSP O hOV
  obtain ⟨hFL,hFT,hFE,hFEnd⟩ :=
    saturated_marked_phase_restrict F hWFF T hFullT AFull hWAF rfl V S hSFP O hOV
  have hMHead : MarkedIdeal.pullback ν M = MO :=
    HironakaG34NonPureLowDim.template_pullback (X := X) (Y := XO) ν N born
  have hFHead : MarkedIdeal.pullback ν F = FO := by
    rw [HironakaG34NonPureLowDim.template_pullback (X := X) (Y := XO) ν,Set.preimage_univ,List.map_append]
  have hMRec := geoTransformAlong_restrict O hWF.isClosedSubmanifold_N hWF.isCoherent T hT
  have hFRec := geoTransformAlong_restrict O hWFF.isClosedSubmanifold_N hWFF.isCoherent T hFullT
  rw [hMHead] at hML hMRec hMEnd
  rw [hFHead] at hFL hFRec hFE
  have hQ : IsGeoTestTower MO Q := (isGeoTestTower_append_iff _ _ _).mpr
    ⟨hML,hMRec.symm ▸ hMT⟩
  have hQF : IsGeoTestTower FO Q := (isGeoTestTower_append_iff _ _ _).mpr
    ⟨hFL,hFRec.symm ▸ hFT⟩
  have hSharpL := currentSharp_restrict O T hFullT hSharpT
  rw [List.map_append] at hSharpL
  have hSharpD := currentSharp_restrict D S hFullS hSharpS
  have hFullU : IsGeoTestTower (geometricTemplate (X := XU) (univ : Set U) FU) tail.tower := by
    rw [hFullTemplate,HironakaG34NonPureLowDim.template_pullback (X := Y) (Y := XU) u,
      Set.preimage_univ] at hFT
    exact hFT
  have hSharpU : CurrentSharpCentres NU FU tail.tower := by
    apply currentSharp_of_isTowerIso NU FU e.symm hIso.symm hFullU
    have hList : FU.map (e.symm ⁻¹' ·) = (OV ++ BV).map ((Subtype.val : D → V) ⁻¹' ·) := by
      simp only [FU,OV,BV,OY,List.map_append,List.map_map]
      rfl
    rw [hList]
    exact hSharpD
  have hSU : strictAlong L NO = NU := by
    rw [strictAlong_restrict]
    change u ⁻¹' strictAlong T N = u ⁻¹' A.N
    rw [show A.N = strictAlong T N from N_geoTransformAlong _ T]
  have hFE' : (geoTransformAlong FO L).E = FU := by
    rw [hFE,hFullTemplate]
    rfl
  have hQSharp : CurrentSharpCentres NO (OO ++ BO) Q := by
    apply currentSharp_append NO (OO ++ BO) L tail.tower hSharpL
    rw [show geometricTemplate (univ : Set O) (OO ++ BO) = FO from rfl,hSU,hFE']
    exact hSharpU
  let AS := geoTransformAlong (geometricTemplate (X := CMfd.of (n := n) V) NV BV) S
  let OS := OV.map (strictAlong S)
  let AQ := geoTransformAlong MO Q
  let OQ := OO.map (strictAlong Q)
  have hAQ : AQ.N = b ⁻¹' AS.N := by
    rw [show AQ.N = strictAlong Q NO from N_geoTransformAlong _ _,
      show AS.N = strictAlong S NV from N_geoTransformAlong _ _]
    have h := hStrict N
    rw [←show A.N = strictAlong T N from N_geoTransformAlong _ T] at h
    exact h
  have hB : AQ.E = AS.E.map (b ⁻¹' ·) := by
    rw [hTemplate,HironakaG34NonPureLowDim.template_pullback (X := Y)
      (Y := CMfd.of (n := n) V) v] at hMEnd
    exact hMEnd
  have hO : OQ = OS.map (b ⁻¹' ·) := by
    simp only [OQ,OO,OS,OV,List.map_map]
    apply List.map_congr_left
    intro H _hH
    exact hStrict H
  have hRec := actual_retained_born_recorded_residual_dictionary hn hN hE hTr hdense T hT hFullT
  have hNV := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hRec.1 V
  have hEV : IsSNCDivisor n (OV ++ BV) := by
    simpa only [List.map_append] using isSNCDivisor_map_preimage
      (pullsBackCoordinates_val (n := n) V) continuous_subtype_val hRec.2.1
  have hTV : IsTransverse n NV BV := isTransverse_preimage (pullsBackCoordinates_val V) hRec.2.2.1
  have hDenseV : NV ⊆ closure (NV \ ⋃ H ∈ OV ++ BV,H) := by
    simpa only [List.map_append] using HironakaG34NonPureLowDim.open_full_density hRec.2.2.2.1 V
  have hFinal := actual_retained_born_recorded_residual_dictionary (X := CMfd.of (n := n) V)
    hn hNV hEV hTV hDenseV S hS hFullS
  have hb : HironakaBaseChange.IsOpenHoloEmbedding n b := ⟨openPreimage S D,tail.back,fun _ => rfl⟩
  exact ⟨O,hKO,hOV,hQ,hQF,hQSharp,hb,⟨hFinal.1,hFinal.2.1,hFinal.2.2.1,hFinal.2.2.2.1⟩,
    hAQ,hO,hB⟩

set_option maxHeartbeats 700000 in
/-- If a native sharp tail resolves the retained distinct defect on an
open containing the whole compact-enclosure fibre, the actual saturated
composition resolves that defect on a neighbourhood of the base enclosure. -/
theorem exists_saturated_retained_continuation_literal (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate N born) T)
    (hFullT : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T)
    (hSharpT : CurrentSharpCentres N (old ++ born) T)
    (K : Set X) (V : Opens Y) (hKV : T.proj ⁻¹' K ⊆ V)
    (S : BlowupTower (CMfd.of (n := n) V) Z) :
    let A := geoTransformAlong (geometricTemplate N born) T
    let v := (Subtype.val : V → Y)
    let NV := v ⁻¹' A.N
    let OV := (old.map (strictAlong T)).map (v ⁻¹' ·)
    let BV := A.E.map (v ⁻¹' ·)
    IsGeoTestTower (geometricTemplate NV BV) S →
    IsGeoTestTower (geometricTemplate (univ : Set V) (OV ++ BV)) S →
    CurrentSharpCentres NV (OV ++ BV) S →
    (let AS := geoTransformAlong (geometricTemplate (X := CMfd.of (n := n) V) NV BV) S
     actualFamilyDistinctDefect AS.N
       (oldResidualPart AS.N (OV.map (strictAlong S)) AS.E) = ∅) →
    ∃ O : Opens X, K ⊆ O ∧ ∃ (hOV : openPreimage T O ≤ V),
      let D := nestedOpens V (openPreimage T O)
      let tail := transport (nestedOpensDiffeo (n := n) hOV).symm (restrict D S)
      let Q := (restrict O T).append tail.tower
      let ν := (Subtype.val : O → X)
      let NO := ν ⁻¹' N
      let OO := old.map (ν ⁻¹' ·)
      let BO := born.map (ν ⁻¹' ·)
      let AQ := geoTransformAlong (geometricTemplate NO BO) Q
      IsGeoTestTower (geometricTemplate NO BO) Q ∧
      IsGeoTestTower (geometricTemplate (univ : Set O) (OO ++ BO)) Q ∧
      CurrentSharpCentres NO (OO ++ BO) Q ∧
      actualFamilyDistinctDefect AQ.N (oldResidualPart AQ.N (OO.map (strictAlong Q)) AQ.E) = ∅ := by
  intro A v NV OV BV hS hFullS hSharpS hEnd
  obtain ⟨O,hKO,hOV,hQ,hFullQ,hSharpQ,hb,hNative,hAQ,hO,hB⟩ :=
    exists_saturated_retained_continuation_native hn hN hE hTr hdense T hT hFullT hSharpT
      K V hKV S hS hFullS hSharpS
  refine ⟨O,hKO,hOV,hQ,hFullQ,hSharpQ,?_⟩
  rw [hAQ,hO,hB]
  have hDef := actual_retained_defect_open_embedding hn hNative.carrier hNative.full
    hNative.born_transverse hNative.dense _ hb
  rw [hDef,hEnd,Set.preimage_empty]

/-- If a native sharp tail resolves the retained distinct defect on an
open containing the whole compact-enclosure fibre, the actual saturated
composition resolves that defect on a neighbourhood of the base enclosure. -/
theorem exists_saturated_retained_continuation (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate N born) T)
    (hFullT : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T)
    (hSharpT : CurrentSharpCentres N (old ++ born) T)
    (K : Set X) (V : Opens Y) (hKV : T.proj ⁻¹' K ⊆ V)
    (S : BlowupTower (CMfd.of (n := n) V) Z) :
    let A := geoTransformAlong (geometricTemplate N born) T
    let v := (Subtype.val : V → Y)
    let NV := v ⁻¹' A.N
    let OV := (old.map (strictAlong T)).map (v ⁻¹' ·)
    let BV := A.E.map (v ⁻¹' ·)
    IsGeoTestTower (geometricTemplate NV BV) S →
    IsGeoTestTower (geometricTemplate (univ : Set V) (OV ++ BV)) S →
    CurrentSharpCentres NV (OV ++ BV) S →
    (let AS := geoTransformAlong (geometricTemplate (X := CMfd.of (n := n) V) NV BV) S
     actualFamilyDistinctDefect AS.N
       (oldResidualPart AS.N (OV.map (strictAlong S)) AS.E) = ∅) →
    ∃ O : Opens X, K ⊆ O ∧ ∃ (P : CMfd.{u} n) (Q : BlowupTower (CMfd.of (n := n) O) P),
      let ν := (Subtype.val : O → X)
      let NO := ν ⁻¹' N
      let OO := old.map (ν ⁻¹' ·)
      let BO := born.map (ν ⁻¹' ·)
      let AQ := geoTransformAlong (geometricTemplate NO BO) Q
      IsGeoTestTower (geometricTemplate NO BO) Q ∧
      IsGeoTestTower (geometricTemplate (univ : Set O) (OO ++ BO)) Q ∧
      CurrentSharpCentres NO (OO ++ BO) Q ∧
      actualFamilyDistinctDefect AQ.N (oldResidualPart AQ.N (OO.map (strictAlong Q)) AQ.E) = ∅ := by
  intro A v NV OV BV hS hFullS hSharpS hEnd
  obtain ⟨O,hKO,hOV,hQ,hFullQ,hSharpQ,hEndQ⟩ :=
    exists_saturated_retained_continuation_literal hn hN hE hTr hdense T hT hFullT hSharpT
      K V hKV S hS hFullS hSharpS hEnd
  exact ⟨O,hKO,_,_,hQ,hFullQ,hSharpQ,hEndQ⟩

end
end Hironaka.HironakaG4SaturatedRetainedContinuation
