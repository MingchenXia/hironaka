import Hironaka.Resolution.HironakaG4SaturatedRetainedPreparation
import Hironaka.Resolution.HironakaG4RetainedRelativeLowerService
import Hironaka.Resolution.HironakaG4SaturatedRetainedEquivariance
import Hironaka.Resolution.HironakaG4RetainedCrestEquivariance

/-! Restore the true retained distinct defect after a prepared sharp prefix. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4RetainedPreparedContinuation
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdealTowerTransport HomogenizedGlueingTower MaxLocusLocal
  MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaActualRetainedBornResidualHistory HironakaG4OrderedRetainedDefectTrace
  HironakaG4RetainedPreparedLocalSupport HironakaG4RetainedPreparedDefectRerun
  HironakaG4RetainedCurrentStamp HironakaG4SaturatedRetainedPreparation HironakaG4RetainedRankTowerIso
  HironakaG4RetainedPreparationEmbedding HironakaG4RetainedDefectRelativeExit
  HironakaG4RetainedRelativeLowerService HironakaG34NonPureLowDim HironakaBaseChange
  HironakaG4PreparedCentreCoordinates HironakaG4CompactWholeMonomialMaskPhase
  HironakaG34MaskFoldEquivariance HironakaG4RetainedDefectTraceEquivariance
  HironakaG4RetainedCrestEquivariance HironakaG4SaturatedRetainedEquivariance
  HironakaG4RetainedPreparationTrace HironakaG4RetainedPreparationLowerHistory
  NormalCrossingsComparison NormalCrossingsInvariance
  RegularPointDimension AnalyticIrreducibleComponents

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- One actual sharp tower on a neighbourhood of the enclosure ends with
empty true retained defect and the specified original rows prepared. -/
def HasPreparedRetainedDefectExitNear (N : Set X) (old born : List (Set X))
    (K : Set X) (P : Finset (Fin old.length)) (requireEquivariance : Bool := false) (phases : List RetainedPreparationPhase := [.defect]) : Prop :=
  ∃ U : Opens X, K ⊆ U ∧ ∃ (Y : CMfd.{u} n) (R : BlowupTower (CMfd.of (n := n) U) Y),
    let u := (Subtype.val : U → X)
    let NU := u ⁻¹' N
    let OU := old.map (u ⁻¹' ·)
    let BU := born.map (u ⁻¹' ·)
    let A := geoTransformAlong (geometricTemplate NU BU) R
    let e : Fin old.length ≃ Fin OU.length := finCongr (List.length_map _).symm
    IsGeoTestTower (geometricTemplate NU BU) R ∧
    IsGeoTestTower (geometricTemplate (univ : Set U) (OU ++ BU)) R ∧
    CurrentSharpCentres NU (OU ++ BU) R ∧
    actualFamilyDistinctDefect A.N (oldResidualPart A.N (OU.map (strictAlong R)) A.E) = ∅ ∧
    (∀ i ∈ P, RetainedRowPrepared NU OU BU (e i) R) ∧
    (requireEquivariance = true → IsEquivariant NU (OU ++ BU) R ∧
      ∀ (hn : 0 < n),Nonempty (RetainedPreparationTrace hn NU OU BU phases R))

/-- The same prepared endpoint, together with admissibility of its recorded lower leaves. -/
def HasPreparedRetainedDefectExitNearUsing (lower : SharpHistoryPredicate.{u} n) (N : Set X) (old born : List (Set X))
    (K : Set X) (P : Finset (Fin old.length)) (requireEquivariance : Bool := false) (phases : List RetainedPreparationPhase := [.defect]) : Prop :=
  ∃ U : Opens X, K ⊆ U ∧ ∃ (Y : CMfd.{u} n) (R : BlowupTower (CMfd.of (n := n) U) Y),
    let u := (Subtype.val : U → X)
    let NU := u ⁻¹' N
    let OU := old.map (u ⁻¹' ·)
    let BU := born.map (u ⁻¹' ·)
    let A := geoTransformAlong (geometricTemplate NU BU) R
    let e : Fin old.length ≃ Fin OU.length := finCongr (List.length_map _).symm
    IsGeoTestTower (geometricTemplate NU BU) R ∧
    IsGeoTestTower (geometricTemplate (univ : Set U) (OU ++ BU)) R ∧
    CurrentSharpCentres NU (OU ++ BU) R ∧
    actualFamilyDistinctDefect A.N (oldResidualPart A.N (OU.map (strictAlong R)) A.E) = ∅ ∧
    (∀ i ∈ P, RetainedRowPrepared NU OU BU (e i) R) ∧
    (requireEquivariance = true → IsEquivariant NU (OU ++ BU) R ∧
      ∀ (hn : 0 < n),∃ tape : RetainedPreparationTrace hn NU OU BU phases R,usesLowerHistory lower tape)

theorem HasPreparedRetainedDefectExitNearUsing.forget
    {lower : SharpHistoryPredicate.{u} n} {N : Set X} {old born : List (Set X)}
    {K : Set X} {P : Finset (Fin old.length)} {required : Bool} {phases : List RetainedPreparationPhase}
    (h : HasPreparedRetainedDefectExitNearUsing lower N old born K P required phases) :
    HasPreparedRetainedDefectExitNear N old born K P required phases := by
  obtain ⟨U,hKU,Y,R,hT,hF,hS,hEnd,hRows,hRec⟩ := h
  refine ⟨U,hKU,Y,R,hT,hF,hS,hEnd,hRows,fun hr => ⟨(hRec hr).1,fun hn => ?_⟩⟩
  obtain ⟨tape,_⟩ := (hRec hr).2 hn
  exact ⟨tape⟩

theorem HasPreparedRetainedDefectExitNear.usingUnrestricted
    {N : Set X} {old born : List (Set X)} {K : Set X} {P : Finset (Fin old.length)}
    {required : Bool} {phases : List RetainedPreparationPhase}
    (h : HasPreparedRetainedDefectExitNear N old born K P required phases) :
    HasPreparedRetainedDefectExitNearUsing (fun {_ _} _ _ _ => True) N old born K P required phases := by
  obtain ⟨U,hKU,Y,R,hT,hF,hS,hEnd,hRows,hRec⟩ := h
  refine ⟨U,hKU,Y,R,hT,hF,hS,hEnd,hRows,fun hr => ⟨(hRec hr).1,fun hn => ?_⟩⟩
  obtain ⟨tape⟩ := (hRec hr).2 hn
  exact ⟨tape,usesLowerHistory_unrestricted tape⟩

/-- Properness keeps the entire enclosure fibre compact. The actual
current native tuple retains the geometry and preparation of each named
original row. -/
theorem prepared_retained_current_on_compact_fibre (hn : 0 < n)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    {K : Set X} (hK : IsCompact K) (U : Opens X) (hKU : K ⊆ U)
    (T : BlowupTower (CMfd.of (n := n) U) Y) (P : Finset (Fin old.length)) :
    let ν := (Subtype.val : U → X)
    let NU := ν ⁻¹' N
    let OU := old.map (ν ⁻¹' ·)
    let BU := born.map (ν ⁻¹' ·)
    let eU : Fin old.length ≃ Fin OU.length := finCongr (List.length_map _).symm
    IsGeoTestTower (geometricTemplate NU BU) T →
    IsGeoTestTower (geometricTemplate (univ : Set U) (OU ++ BU)) T →
    (∀ i ∈ P,RetainedRowPrepared NU OU BU (eU i) T) →
    let A := geoTransformAlong (geometricTemplate NU BU) T
    let OY := OU.map (strictAlong T)
    let eY : Fin old.length ≃ Fin OY.length := finCongr (by simp [OY,OU])
    let PY := P.map eY.toEmbedding
    IsCompact (T.proj ⁻¹' (ν ⁻¹' K)) ∧ NativeRetainedGeometry A.N OY A.E ∧
      ∀ j ∈ PY,RetainedRowPrepared A.N OY A.E j (.refl : BlowupTower Y Y) := by
  intro ν NU OU BU eU hT hFullT hPrep
  let A := geoTransformAlong (geometricTemplate NU BU) T
  let OY := OU.map (strictAlong T)
  let eY : Fin old.length ≃ Fin OY.length := finCongr (by simp [OY,OU])
  let PY := P.map eY.toEmbedding
  let KU := ν ⁻¹' K
  let KY := T.proj ⁻¹' KU
  have hKUcomp : IsCompact KU :=
    (Topology.IsInducing.subtypeVal.isCompact_preimage_iff
      (fun x hx => ⟨⟨x,hKU hx⟩,rfl⟩)).mpr hK
  have hKYcomp : IsCompact KY := (HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hKUcomp
  have gU : NativeRetainedGeometry (X := CMfd.of (n := n) U) NU OU BU := g.restrict U
  have hR := actual_retained_born_recorded_residual_dictionary hn gU.carrier gU.full gU.born_transverse
    gU.dense T hT hFullT
  have gY : NativeRetainedGeometry A.N OY A.E := ⟨hR.1,hR.2.1,hR.2.2.1,hR.2.2.2.1⟩
  have hPY : ∀ j ∈ PY,RetainedRowPrepared A.N OY A.E j (.refl : BlowupTower Y Y) := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
    exact (retained_preparation_current_readback hn gU (eU i) T hT hFullT).1.mp (hPrep i hi)
  exact ⟨hKYcomp,gY,hPY⟩

set_option maxHeartbeats 1200000 in
/-- Append a finite actual prepared retained endpoint over the full fibre of
a base enclosure. The composed history is defined on a literal original
open and preserves the specified ordered phases. -/
theorem exists_prepared_retained_exit_after_near_using (lower : SharpHistoryPredicate.{u} n) (hn : 0 < n)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    {K : Set X} (U : Opens X) (hKU : K ⊆ U)
    (T : BlowupTower (CMfd.of (n := n) U) Y) (P : Finset (Fin old.length))
    (requireEquivariance : Bool) (phases later : List RetainedPreparationPhase) :
    let ν := (Subtype.val : U → X)
    let NU := ν ⁻¹' N
    let OU := old.map (ν ⁻¹' ·)
    let BU := born.map (ν ⁻¹' ·)
    let _eU : Fin old.length ≃ Fin OU.length := finCongr (List.length_map _).symm
    IsGeoTestTower (geometricTemplate NU BU) T →
    IsGeoTestTower (geometricTemplate (univ : Set U) (OU ++ BU)) T →
    CurrentSharpCentres NU (OU ++ BU) T →
    (requireEquivariance = true → IsEquivariant NU (OU ++ BU) T ∧
      (∃ tape : RetainedPreparationTrace hn NU OU BU phases T,usesLowerHistory lower tape)) →
    (let A := geoTransformAlong (geometricTemplate NU BU) T
     let OY := OU.map (strictAlong T)
     let eY : Fin old.length ≃ Fin OY.length := finCongr (by simp [OY,OU])
     HasPreparedRetainedDefectExitNearUsing lower A.N OY A.E (T.proj ⁻¹' (ν ⁻¹' K)) (P.map eY.toEmbedding) requireEquivariance later) →
    HasPreparedRetainedDefectExitNearUsing lower N old born K P requireEquivariance (phases ++ later) := by
  intro ν NU OU BU eU hT hFullT hSharpT hCertT hTail
  let A := geoTransformAlong (geometricTemplate NU BU) T
  let OY := OU.map (strictAlong T)
  let eY : Fin old.length ≃ Fin OY.length := finCongr (by simp [OY,OU])
  let PU := P.map eU.toEmbedding
  let KU := ν ⁻¹' K
  have gU : NativeRetainedGeometry (X := CMfd.of (n := n) U) NU OU BU := g.restrict U
  obtain ⟨V,hKV,Z,S,hS,hFullS,hSharpS,hEndS,hPreparedS,hCertS⟩ := hTail
  obtain ⟨W,hKW,hWV,hQ,hFullQ,hSharpQ,hEndQ,hPreparedQ⟩ :=
    exists_saturated_retained_continuation_prepared hn gU T hT hFullT hSharpT KU V hKV S PU
      hS hFullS hSharpS hEndS (by
        intro j hj
        obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
        exact hPreparedS (eY i) (Finset.mem_map.mpr ⟨i,hi,rfl⟩))
  let D := nestedOpens V (openPreimage T W)
  let tail := transport (nestedOpensDiffeo (n := n) hWV).symm (restrict D S)
  let Q := (restrict W T).append tail.tower
  obtain ⟨U',hKU',hWU',hU'U,hL,hFullL,hSharpL,gQ,hLN,hLO,hLB⟩ :=
    exists_flattened_retained_history_native hn g U hKU W hKW Q hQ hFullQ hSharpQ
  let w := (Subtype.val : W → U)
  let NW := w ⁻¹' NU
  let OW := OU.map (w ⁻¹' ·)
  let BW := BU.map (w ⁻¹' ·)
  let φ := (nestedDiffeo (n := n) U W U' hWU' hU'U).symm
  let L := transport φ Q
  let u' := (Subtype.val : U' → X)
  let NL := u' ⁻¹' N
  let OL := old.map (u' ⁻¹' ·)
  let BL := born.map (u' ⁻¹' ·)
  let AQ := geoTransformAlong (geometricTemplate NW BW) Q
  let AL := geoTransformAlong (geometricTemplate NL BL) L.tower
  let β : L.target → tail.target := L.back
  have hβ : IsOpenHoloEmbedding n β := isOpenHoloEmbedding_diffeomorph L.back
  refine ⟨U',hKU',L.target,L.tower,hL,hFullL,hSharpL,?_,?_,?_⟩
  · change actualFamilyDistinctDefect AL.N (oldResidualPart AL.N (OL.map (strictAlong L.tower)) AL.E) = ∅
    change AL.N = β ⁻¹' AQ.N at hLN
    change OL.map (strictAlong L.tower) = (OW.map (strictAlong Q)).map (β ⁻¹' ·) at hLO
    change AL.E = AQ.E.map (β ⁻¹' ·) at hLB
    rw [hLN,hLO,hLB,actual_retained_defect_open_embedding hn gQ.carrier gQ.full
      gQ.born_transverse gQ.dense β hβ,hEndQ,Set.preimage_empty]
  · intro i hi
    let iW : Fin OW.length := Fin.cast (by simp [OW,OU]) i
    let iL : Fin OL.length := Fin.cast (List.length_map _).symm i
    change RetainedRowPrepared NL OL BL iL L.tower
    have hRow : RetainedRowPrepared NW OW BW iW Q :=
      hPreparedQ (eU i) (Finset.mem_map.mpr ⟨i,hi,rfl⟩)
    exact (retained_preparation_of_endpoint_open_embedding hn (gU.restrict W) (g.restrict U')
      Q hQ hFullQ L.tower hL hFullL β hβ iW iL rfl hLN hLO hLB hRow).1

  · intro hEq
    obtain ⟨hEqT,⟨rT,hLowerT⟩⟩ := hCertT hEq
    obtain ⟨hEqS,hTraceS⟩ := hCertS hEq
    obtain ⟨rS,hLowerS⟩ := hTraceS hn
    have hEqQ : IsEquivariant NW (OW ++ BW) Q :=
      isEquivariant_saturated_retained_append gU T hT hFullT hEqT V S W hWV hEqS
    have hEqL := isEquivariant_of_actualIso (transport_isTowerIso φ Q) hEqQ
    have hCarrier : φ ⁻¹' NW = NL := rfl
    have hO : OW.map (φ ⁻¹' ·) = OL := by
      simp only [OW,OU,OL,List.map_map]
      rfl
    have hB : BW.map (φ ⁻¹' ·) = BL := by
      simp only [BW,BU,BL,List.map_map]
      rfl
    rw [hCarrier,List.map_append,hO,hB] at hEqL
    refine ⟨hEqL,?_⟩
    intro hPos
    obtain ⟨rQ,hLowerQ⟩ := retained_trace_saturated_append_using lower hn gU T hT hFullT
      rT hLowerT V S W hWV rS hLowerS
    have hL : ∃ rL : RetainedPreparationTrace hn (φ ⁻¹' NW) (OW.map (φ ⁻¹' ·)) (BW.map (φ ⁻¹' ·))
        (phases ++ later) L.tower,usesLowerHistory lower rL :=
      ⟨rQ.rebase φ (gU.restrict W),hLowerQ⟩
    rw [hCarrier,hO,hB] at hL
    exact hL

/-- The same service with unrestricted lower history. -/
theorem exists_prepared_retained_exit_after_near (hn : 0 < n)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    {K : Set X} (U : Opens X) (hKU : K ⊆ U)
    (T : BlowupTower (CMfd.of (n := n) U) Y) (P : Finset (Fin old.length))
    (requireEquivariance : Bool) (phases later : List RetainedPreparationPhase) :
    let ν := (Subtype.val : U → X)
    let NU := ν ⁻¹' N
    let OU := old.map (ν ⁻¹' ·)
    let BU := born.map (ν ⁻¹' ·)
    let _eU : Fin old.length ≃ Fin OU.length := finCongr (List.length_map _).symm
    IsGeoTestTower (geometricTemplate NU BU) T →
    IsGeoTestTower (geometricTemplate (univ : Set U) (OU ++ BU)) T →
    CurrentSharpCentres NU (OU ++ BU) T →
    (requireEquivariance = true → IsEquivariant NU (OU ++ BU) T ∧
      Nonempty (RetainedPreparationTrace hn NU OU BU phases T)) →
    (let A := geoTransformAlong (geometricTemplate NU BU) T
     let OY := OU.map (strictAlong T)
     let eY : Fin old.length ≃ Fin OY.length := finCongr (by simp [OY,OU])
     HasPreparedRetainedDefectExitNear A.N OY A.E (T.proj ⁻¹' (ν ⁻¹' K)) (P.map eY.toEmbedding) requireEquivariance later) →
    HasPreparedRetainedDefectExitNear N old born K P requireEquivariance (phases ++ later) := by
  intro ν NU OU BU _e hT hFull hSharp hCert hTail
  apply HasPreparedRetainedDefectExitNearUsing.forget
    (exists_prepared_retained_exit_after_near_using (fun {_ _} _ _ _ => True) hn g U hKU T P
      requireEquivariance phases later hT hFull hSharp ?_ hTail.usingUnrestricted)
  intro hr
  obtain ⟨hEq,⟨tape⟩⟩ := hCert hr
  exact ⟨hEq,tape,usesLowerHistory_unrestricted tape⟩

/-- Run the true retained-defect phase near a compact enclosure and retain
all the specified already prepared native rows. -/
theorem exists_prepared_retained_defect_exit_near_using (lower : SharpHistoryPredicate.{u} n) (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    (P : Finset (Fin old.length))
    (hP : ∀ i ∈ P,RetainedRowPrepared N old born i (.refl : BlowupTower X X))
    {K : Set X} (hK : IsCompact K) (requireEquivariance : Bool) :
    HasPreparedRetainedDefectExitNearUsing lower N old born K P requireEquivariance [.defect] := by
  obtain ⟨U,hKU,Y,T,hT,hFull,hSharp,_hOver,hEnd,⟨trace⟩,hPrep⟩ :=
    exists_ordered_retained_defect_exit_preserving_prepared hn g P hP hK
  refine ⟨U,hKU,Y,T,hT,hFull,hSharp,hEnd,(fun i hi => (hPrep i hi).1),?_⟩
  intro _
  exact ⟨orderedRetainedDefectTrace_isEquivariant
    (fun hGeometry phase => retained_crest_isEquivariant hn hGeometry phase) trace (g.restrict U),
    fun _ => ⟨.defect trace,trivial⟩⟩

/-- The same service with unrestricted lower history. -/
theorem exists_prepared_retained_defect_exit_near (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    (P : Finset (Fin old.length))
    (hP : ∀ i ∈ P,RetainedRowPrepared N old born i (.refl : BlowupTower X X))
    {K : Set X} (hK : IsCompact K) (requireEquivariance : Bool) :
    HasPreparedRetainedDefectExitNear N old born K P requireEquivariance [.defect] := by
  exact (exists_prepared_retained_defect_exit_near_using (fun {_ _} _ _ _ => True)
    hn g P hP hK requireEquivariance).forget

set_option maxHeartbeats 1200000 in
/-- After any actual sharp prefix preserving specified preparation, a
defect rerun on the full compact fibre gives a true defect-free prepared
endpoint on a literal smaller original neighbourhood. -/
theorem exists_prepared_retained_defect_rerun_after_near_using (lower : SharpHistoryPredicate.{u} n) (hn : 0 < n)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    {K : Set X} (hK : IsCompact K) (U : Opens X) (hKU : K ⊆ U)
    (T : BlowupTower (CMfd.of (n := n) U) Y) (P : Finset (Fin old.length))
    (requireEquivariance : Bool) (phases : List RetainedPreparationPhase) :
    let ν := (Subtype.val : U → X)
    let NU := ν ⁻¹' N
    let OU := old.map (ν ⁻¹' ·)
    let BU := born.map (ν ⁻¹' ·)
    let eU : Fin old.length ≃ Fin OU.length := finCongr (List.length_map _).symm
    IsGeoTestTower (geometricTemplate NU BU) T →
    IsGeoTestTower (geometricTemplate (univ : Set U) (OU ++ BU)) T →
    CurrentSharpCentres NU (OU ++ BU) T →
    (requireEquivariance = true → IsEquivariant NU (OU ++ BU) T ∧
      (∃ tape : RetainedPreparationTrace hn NU OU BU phases T,usesLowerHistory lower tape)) →
    (∀ i ∈ P,RetainedRowPrepared NU OU BU (eU i) T) →
    HasPreparedRetainedDefectExitNearUsing lower N old born K P requireEquivariance (phases ++ [.defect]) := by
  intro ν NU OU BU eU hT hFullT hSharpT hEqT hPrep
  obtain ⟨hKYcomp,gY,hPY⟩ := prepared_retained_current_on_compact_fibre hn g hK U hKU T P hT hFullT hPrep
  exact exists_prepared_retained_exit_after_near_using lower hn g U hKU T P requireEquivariance phases [.defect] hT hFullT hSharpT hEqT
      (exists_prepared_retained_defect_exit_near_using lower hn gY _ hPY hKYcomp requireEquivariance)

/-- The same service with unrestricted lower history. -/
theorem exists_prepared_retained_defect_rerun_after_near (hn : 0 < n)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    {K : Set X} (hK : IsCompact K) (U : Opens X) (hKU : K ⊆ U)
    (T : BlowupTower (CMfd.of (n := n) U) Y) (P : Finset (Fin old.length))
    (requireEquivariance : Bool) (phases : List RetainedPreparationPhase) :
    let ν := (Subtype.val : U → X)
    let NU := ν ⁻¹' N
    let OU := old.map (ν ⁻¹' ·)
    let BU := born.map (ν ⁻¹' ·)
    let eU : Fin old.length ≃ Fin OU.length := finCongr (List.length_map _).symm
    IsGeoTestTower (geometricTemplate NU BU) T →
    IsGeoTestTower (geometricTemplate (univ : Set U) (OU ++ BU)) T →
    CurrentSharpCentres NU (OU ++ BU) T →
    (requireEquivariance = true → IsEquivariant NU (OU ++ BU) T ∧
      Nonempty (RetainedPreparationTrace hn NU OU BU phases T)) →
    (∀ i ∈ P,RetainedRowPrepared NU OU BU (eU i) T) →
    HasPreparedRetainedDefectExitNear N old born K P requireEquivariance (phases ++ [.defect]) := by
  intro ν NU OU BU eU hT hFull hSharp hCert hPrep
  apply HasPreparedRetainedDefectExitNearUsing.forget
    (exists_prepared_retained_defect_rerun_after_near_using (fun {_ _} _ _ _ => True)
      hn g hK U hKU T P requireEquivariance phases hT hFull hSharp ?_ hPrep)
  intro hr
  obtain ⟨hEq,⟨tape⟩⟩ := hCert hr
  exact ⟨hEq,tape,usesLowerHistory_unrestricted tape⟩

set_option maxHeartbeats 500000 in
/-- A disjoint protected family and the selected row are prepared after
the lower service and the subsequent restoration of the true defect. -/
theorem exists_retained_selected_row_and_defect_restore_near_compact (hn : 0 < n) (d : ℕ)
    (hLower : CompactRelativeSharpCleanupsExist.{u} n d)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    (hDim : ∀ x ∈ N,∃ e ≤ d+1,RegularAtDim (n := n) N x e)
    (hEmpty : actualFamilyDistinctDefect N (oldResidualPart N old born) = ∅)
    (i : Fin old.length) (P : Finset (Fin old.length))
    (hP : ∀ j ∈ P,RetainedRowPrepared N old born j (.refl : BlowupTower X X))
    {K : Set X} (hK : IsCompact K) :
    let L := N ∩ (oldResidualPart N old born i).zeroLocus
    let F := HironakaG4ResidualInductionInputs.remainingBoundary old born i
    let D := HironakaSharpOriginalMultiBoundaryBadLocus.originalSharpBadLocus (n := n) L F
    (∀ j ∈ P,Disjoint D (retainedRowSupport N old born j (.refl : BlowupTower X X))) →
    HasPreparedRetainedDefectExitNear N old born K (insert i P) false [.lower i.val,.defect] := by
  intro L F D hSep
  obtain ⟨U,hKU,Y,T,hT,hFull,hSharp,_hOver,hSelected,_hSupport,hPrior⟩ :=
    exists_retained_selected_row_service_near_compact hn d hLower g hDim hEmpty i P hP hK hSep
  apply exists_prepared_retained_defect_rerun_after_near hn g hK U hKU T (insert i P) false [.lower i.val] hT hFull hSharp (by simp)
  intro j hj
  rcases Finset.mem_insert.mp hj with rfl | hj
  · exact hSelected
  · exact (hPrior j hj).1

end
end Hironaka.HironakaG4RetainedPreparedContinuation
