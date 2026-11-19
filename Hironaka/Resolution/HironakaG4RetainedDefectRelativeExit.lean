import Hironaka.Resolution.HironakaG4RetainedDefectRelativeDecrease
import Hironaka.Resolution.HironakaG4SaturatedRetainedContinuation
import Hironaka.Resolution.HironakaG4RetainedCrestPhaseRestriction
import Hironaka.Resolution.HironakaG4OrderedRetainedDefectTrace

/-! Finite actual retained-defect cleanup near an arbitrary compact enclosure. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4RetainedDefectRelativeExit
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism BlowupTowerIsoTail
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealTowerTransport MarkedIdealRestrictOpen
  MaxLocusLocal HomogenizedGlueingTower IdealWeightPowers
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance SimultaneousNormalCrossings
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaActualRetainedBornResidualHistory HironakaActualRetainedBoundaryMaskBlock
  HironakaG4OrderedDefectStamp HironakaG4RetainedCurrentStamp HironakaG4RetainedRankTowerIso
  HironakaG4RetainedDefectRelativeDecrease HironakaG4SaturatedRetainedContinuation
  HironakaCompactFootprintSharpExtension HironakaG4RetainedCrestPhaseRestriction
  HironakaG4OrderedRetainedDefectTrace
  HironakaG4PreparedCentreCoordinates HironakaG4CompactWholeMonomialMaskPhase

variable {n : ℕ} {X : CMfd.{u} n}

/-- The whole literal source neighbourhood has a sharp finite history whose
actual retained chronological rows no longer have a distinct-germ defect. -/
def HasRetainedDefectExitNear (N : Set X) (old born : List (Set X)) (K : Set X) : Prop :=
  ∃ O : Opens X, K ⊆ O ∧ ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) O) Y),
    let ν := (Subtype.val : O → X)
    let NO := ν ⁻¹' N
    let OO := old.map (ν ⁻¹' ·)
    let BO := born.map (ν ⁻¹' ·)
    let A := geoTransformAlong (geometricTemplate NO BO) T
    IsGeoTestTower (geometricTemplate NO BO) T ∧
    IsGeoTestTower (geometricTemplate (univ : Set O) (OO ++ BO)) T ∧
    CurrentSharpCentres NO (OO ++ BO) T ∧
    actualFamilyDistinctDefect A.N (oldResidualPart A.N (OO.map (strictAlong T)) A.E) = ∅

/-- The same local exit retains each physically selected ordered phase,
its active marked record and the exact operations used to shrink it. -/
def HasOrderedRetainedDefectExitNear (hn : 0 < n) (N : Set X) (old born : List (Set X))
    (K : Set X) (μ : WithTop RetainedStampRank) : Prop :=
  ∃ O : Opens X, K ⊆ O ∧ ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) O) Y),
    let ν := (Subtype.val : O → X)
    let NO := ν ⁻¹' N
    let OO := old.map (ν ⁻¹' ·)
    let BO := born.map (ν ⁻¹' ·)
    let A := geoTransformAlong (geometricTemplate NO BO) T
    IsGeoTestTower (geometricTemplate NO BO) T ∧
    IsGeoTestTower (geometricTemplate (univ : Set O) (OO ++ BO)) T ∧
    CurrentSharpCentres NO (OO ++ BO) T ∧
    actualFamilyDistinctDefect A.N (oldResidualPart A.N (OO.map (strictAlong T)) A.E) = ∅ ∧
    Nonempty (OrderedRetainedDefectTrace hn NO OO BO μ T)

set_option maxHeartbeats 650000 in
/-- Flattening a nested source open transports the same actual retained
history. The current carrier and both ordered boundary lists pull back
through the physical endpoint biholomorphism. -/
theorem exists_flattened_retained_history_native (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    {K : Set X} (O : Opens X) (hKO : K ⊆ O)
    (W : Opens (CMfd.of (n := n) O)) (hKW : (Subtype.val : O → X) ⁻¹' K ⊆ W)
    {Y : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) W) Y) :
    let ν := (Subtype.val : O → X)
    let w := (Subtype.val : W → O)
    let NW := w ⁻¹' (ν ⁻¹' N)
    let OW := (old.map (ν ⁻¹' ·)).map (w ⁻¹' ·)
    let BW := (born.map (ν ⁻¹' ·)).map (w ⁻¹' ·)
    let AW := geoTransformAlong (geometricTemplate NW BW) T
    IsGeoTestTower (geometricTemplate NW BW) T →
    IsGeoTestTower (geometricTemplate (univ : Set W) (OW ++ BW)) T →
    CurrentSharpCentres NW (OW ++ BW) T →
    ∃ U : Opens X, K ⊆ U ∧ ∃ (hWU : ∀ q : O,q ∈ W ↔ ν q ∈ U) (hUO : U ≤ O),
      let u := (Subtype.val : U → X)
      let NU := u ⁻¹' N
      let OU := old.map (u ⁻¹' ·)
      let BU := born.map (u ⁻¹' ·)
      let φ := (nestedDiffeo (n := n) O W U hWU hUO).symm
      let R := transport φ T
      let AR := geoTransformAlong (geometricTemplate NU BU) R.tower
      let b : R.target → Y := R.back
      IsGeoTestTower (geometricTemplate NU BU) R.tower ∧
      IsGeoTestTower (geometricTemplate (univ : Set U) (OU ++ BU)) R.tower ∧
      CurrentSharpCentres NU (OU ++ BU) R.tower ∧
      NativeRetainedGeometry AW.N (OW.map (strictAlong T)) AW.E ∧
      AR.N = b ⁻¹' AW.N ∧ OU.map (strictAlong R.tower) = (OW.map (strictAlong T)).map (b ⁻¹' ·) ∧
      AR.E = AW.E.map (b ⁻¹' ·) := by
  intro ν w NW OW BW AW hT hFull hSharp
  let U : Opens X := ⟨ν '' (W : Set O),O.isOpen.isOpenMap_subtype_val _ W.isOpen⟩
  have hWU : ∀ q : O,q ∈ W ↔ ν q ∈ U := fun q =>
    ⟨fun hq => ⟨q,hq,rfl⟩,fun ⟨q',hq',heq⟩ => (Subtype.ext heq : q'=q) ▸ hq'⟩
  have hUO : U ≤ O := by
    intro x hx
    obtain ⟨q,_,hq⟩ := hx
    exact hq ▸ q.property
  have hKU : K ⊆ U := fun x hx => (hWU ⟨x,hKO hx⟩).mp (hKW hx)
  let XU := CMfd.of (n := n) U
  let XW := CMfd.of (n := n) W
  let u := (Subtype.val : U → X)
  let φ := (nestedDiffeo (n := n) O W U hWU hUO).symm
  let R := transport φ T
  have hIso := transport_isTowerIso φ T
  let NU := u ⁻¹' N
  let OU := old.map (u ⁻¹' ·)
  let BU := born.map (u ⁻¹' ·)
  let MW := geometricTemplate (X := XW) NW BW
  let FW := geometricTemplate (X := XW) (univ : Set W) (OW ++ BW)
  let MU := geometricTemplate (X := XU) NU BU
  let FU := geometricTemplate (X := XU) (univ : Set U) (OU ++ BU)
  have hGW : NativeRetainedGeometry (X := XW) NW OW BW := (g.restrict O).restrict W
  have hNW := hGW.carrier
  have hPM : MarkedIdeal.pullback φ MW = MU := by
    rw [HironakaG34NonPureLowDim.template_pullback (X := XW) (Y := XU)]
    unfold MU NU BU NW BW
    rw [List.map_map,List.map_map]
    rfl
  have hPF : MarkedIdeal.pullback φ FW = FU := by
    rw [HironakaG34NonPureLowDim.template_pullback (X := XW) (Y := XU),Set.preimage_univ,List.map_append]
    simp only [FU,OU,BU,OW,BW,List.map_map]
    rfl
  have hRT : IsGeoTestTower MU R.tower := by
    rw [←hPM]
    exact (IsTowerIso.isGeoTestTower_iff φ hNW isCoherent_unitIdeal hIso).mpr hT
  have hRF : IsGeoTestTower FU R.tower := by
    rw [←hPF]
    exact (IsTowerIso.isGeoTestTower_iff φ isClosedSubmanifold_univ isCoherent_unitIdeal hIso).mpr hFull
  have hRS : CurrentSharpCentres NU (OU ++ BU) R.tower := by
    apply currentSharp_of_isTowerIso NU (OU ++ BU) φ.symm hIso.symm hRF
    have hN' : φ.symm ⁻¹' NU = NW := rfl
    have hE' : (OU ++ BU).map (φ.symm ⁻¹' ·) = OW ++ BW := by
      simp only [OU,BU,OW,BW,List.map_append,List.map_map]
      rfl
    rw [hN',hE']
    exact hSharp
  let AR := geoTransformAlong MU R.tower
  let b : R.target → Y := R.back
  have hRec := actual_retained_born_recorded_residual_dictionary (X := XW)
    hn hNW hGW.full hGW.born_transverse hGW.dense T hT hFull
  have hAR : AR = MarkedIdeal.pullback b AW := by
    change geoTransformAlong MU R.tower = _
    rw [←hPM]
    exact IsTowerIso.geoTransformAlong_eq φ hNW isCoherent_unitIdeal hIso hT
  have hOld : OU.map (strictAlong R.tower) = (OW.map (strictAlong T)).map (b ⁻¹' ·) := by
    simp only [OU,OW,List.map_map]
    apply List.map_congr_left
    intro H _hH
    exact hIso.strictAlong_eq (w ⁻¹' (ν ⁻¹' H))
  exact ⟨U,hKU,hWU,hUO,hRT,hRF,hRS,⟨hRec.1,hRec.2.1,hRec.2.2.1,hRec.2.2.2.1⟩,
    congrArg MarkedIdeal.N hAR,hOld,congrArg MarkedIdeal.E hAR⟩

set_option maxHeartbeats 650000 in
private theorem retained_exit_flatten (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    {K : Set X} (O : Opens X) (hKO : K ⊆ O) {μ : WithTop RetainedStampRank} :
    let XO := CMfd.of (n := n) O
    let ν := (Subtype.val : O → X)
    HasOrderedRetainedDefectExitNear (X := XO) hn (ν ⁻¹' N) (old.map (ν ⁻¹' ·))
      (born.map (ν ⁻¹' ·)) (ν ⁻¹' K) μ →
    HasOrderedRetainedDefectExitNear hn N old born K μ := by
  intro XO ν hExit
  obtain ⟨W,hKW,Y,T,hT,hFull,hSharp,hEnd,⟨history⟩⟩ := hExit
  let g : NativeRetainedGeometry N old born := ⟨hN,hE,hTr,hdense⟩
  obtain ⟨U,hKU,hWU,hUO,hRT,hRF,hRS,hCurrent,hAR,hOld,hBorn⟩ :=
    exists_flattened_retained_history_native hn g O hKO W hKW T hT hFull hSharp
  let XU := CMfd.of (n := n) U
  let u := (Subtype.val : U → X)
  let w := (Subtype.val : W → O)
  let φ := (nestedDiffeo (n := n) O W U hWU hUO).symm
  let R := transport φ T
  let NW := w ⁻¹' (ν ⁻¹' N)
  let OW := (old.map (ν ⁻¹' ·)).map (w ⁻¹' ·)
  let BW := (born.map (ν ⁻¹' ·)).map (w ⁻¹' ·)
  let NU := u ⁻¹' N
  let OU := old.map (u ⁻¹' ·)
  let BU := born.map (u ⁻¹' ·)
  let MU := geometricTemplate (X := XU) NU BU
  have hHist : OrderedRetainedDefectTrace hn NU OU BU μ R.tower := by
    have h := history.rebase φ ((g.restrict O).restrict W)
    change OrderedRetainedDefectTrace hn (φ ⁻¹' NW) (OW.map (φ ⁻¹' ·)) (BW.map (φ ⁻¹' ·))
      μ R.tower at h
    have hOldW : OW.map (φ ⁻¹' ·) = OU := by
      simp only [OW,OU,List.map_map]
      rfl
    have hBornW : BW.map (φ ⁻¹' ·) = BU := by
      simp only [BW,BU,List.map_map]
      rfl
    rw [hOldW,hBornW] at h
    exact h
  refine ⟨U,hKU,R.target,R.tower,hRT,hRF,hRS,?_,⟨hHist⟩⟩
  let AR := geoTransformAlong MU R.tower
  let b : R.target → Y := R.back
  have hDef := actual_retained_defect_open_embedding hn hCurrent.carrier hCurrent.full
    hCurrent.born_transverse hCurrent.dense b (isOpenHoloEmbedding_diffeomorph R.back)
  change actualFamilyDistinctDefect AR.N (oldResidualPart AR.N (OU.map (strictAlong R.tower)) AR.E) = ∅
  rw [hAR,hOld,hBorn,hDef,hEnd,Set.preimage_empty]

private theorem retained_exit_without_defect_near (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    {K : Set X} {μ : WithTop RetainedStampRank} (hClosed : IsClosed (actualFamilyDistinctDefect N (oldResidualPart N old born)))
    (hDisjoint : ¬ (K ∩ actualFamilyDistinctDefect N (oldResidualPart N old born)).Nonempty) :
    HasOrderedRetainedDefectExitNear hn N old born K μ := by
  let D := actualFamilyDistinctDefect N (oldResidualPart N old born)
  let O : Opens X := ⟨Dᶜ,hClosed.isOpen_compl⟩
  have hKO : K ⊆ O := fun x hx hxD => hDisjoint ⟨x,hx,hxD⟩
  let XO := CMfd.of (n := n) O
  let ν := (Subtype.val : O → X)
  have hDef : actualFamilyDistinctDefect (ν ⁻¹' N)
      (oldResidualPart (X := XO) (ν ⁻¹' N) (old.map (ν ⁻¹' ·)) (born.map (ν ⁻¹' ·))) = ∅ := by
    rw [(actual_retained_defect_and_rank_open hn hN hE hTr hdense O).1]
    exact Set.eq_empty_of_forall_notMem fun x hx => x.property hx
  refine ⟨O,hKO,XO,.refl,trivial,trivial,trivial,?_,⟨.done hDef⟩⟩
  change actualFamilyDistinctDefect (ν ⁻¹' N)
    (oldResidualPart (X := XO) (ν ⁻¹' N) ((old.map (ν ⁻¹' ·)).map id) (born.map (ν ⁻¹' ·))) = ∅
  rw [List.map_id]
  exact hDef

set_option maxHeartbeats 1400000 in
private theorem retained_exit_of_rank_lt (hn : 0 < n) (μ : WithTop ((ℕ ×ₗ ℕ) ×ₗ ℕ)) :
    ∀ {X : CMfd.{u} n} {N : Set X} {old born : List (Set X)},
      IsClosedSubmanifold n N → IsSNCDivisor n (old ++ born) → IsTransverse n N born →
      N ⊆ closure (N \ ⋃ G ∈ old ++ born,G) → ∀ {K : Set X}, IsCompact K →
      (∀ x ∈ K ∩ actualFamilyDistinctDefect N (oldResidualPart N old born),
        (retainedDefectOrderedRank N old born x : WithTop ((ℕ ×ₗ ℕ) ×ₗ ℕ)) < μ) →
      HasOrderedRetainedDefectExitNear hn N old born K μ := by
  induction μ using WellFoundedLT.induction with
  | _ μ ih =>
    intro X N old born hN hE hTr hdense K hK hRank
    have hClosed := isClosed_current_retained_distinct_defect hn hN hE hTr hdense
      (.refl : BlowupTower X X) trivial trivial
    change IsClosed (actualFamilyDistinctDefect N (oldResidualPart N (old.map id) born)) at hClosed
    rw [List.map_id] at hClosed
    by_cases hNonempty : (K ∩ actualFamilyDistinctDefect N (oldResidualPart N old born)).Nonempty
    · obtain ⟨x,hx,O,hKO,Y,T,hT,hFull,hSharp,phase,hPhaseRank,hDrop⟩ :=
        exists_retained_defect_strict_decrease_near_compact_with_phase hn hN hE hTr hdense
          hK hClosed hNonempty
      let XO := CMfd.of (n := n) O
      let ν := (Subtype.val : O → X)
      let NO := ν ⁻¹' N
      let OO := old.map (ν ⁻¹' ·)
      let BO := born.map (ν ⁻¹' ·)
      let A := geoTransformAlong (geometricTemplate (X := XO) NO BO) T
      let OY := OO.map (strictAlong T)
      let K₀ := ν ⁻¹' K
      let K' := T.proj ⁻¹' K₀
      have hK₀ : IsCompact K₀ :=
        (Topology.IsInducing.subtypeVal.isCompact_preimage_iff
          (fun x hx => ⟨⟨x,hKO hx⟩,rfl⟩)).mpr hK
      have hK' : IsCompact K' := (HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hK₀
      have hNO := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN O
      have hEO : IsSNCDivisor n (OO ++ BO) := by
        simpa only [List.map_append] using isSNCDivisor_map_preimage
          (pullsBackCoordinates_val (n := n) O) continuous_subtype_val hE
      have hTrO : IsTransverse n NO BO := isTransverse_preimage (pullsBackCoordinates_val O) hTr
      have hDenseO : NO ⊆ closure (NO \ ⋃ H ∈ OO ++ BO,H) := by
        simpa only [List.map_append] using HironakaG34NonPureLowDim.open_full_density hdense O
      have hRec := actual_retained_born_recorded_residual_dictionary (X := XO)
        hn hNO hEO hTrO hDenseO T hT hFull
      obtain ⟨V,hKV,Z,S,hS,hFullS,hSharpS,hEnd,⟨history⟩⟩ :=
        ih _ (hRank x hx) hRec.1 hRec.2.1 hRec.2.2.1 hRec.2.2.2.1 hK'
          (fun y hy => WithTop.coe_lt_coe.mpr (hDrop y hy.2).2)
      obtain ⟨W,hKW,hWV,hQ,hFullQ,hSharpQ,hEndQ⟩ :=
        exists_saturated_retained_continuation_literal (X := XO)
          hn hNO hEO hTrO hDenseO T hT hFull hSharp K₀ V hKV S hS hFullS hSharpS hEnd
      let XW := CMfd.of (n := n) W
      let w := (Subtype.val : W → O)
      let NW := w ⁻¹' NO
      let OW := OO.map (w ⁻¹' ·)
      let BW := BO.map (w ⁻¹' ·)
      let U := openPreimage T W
      let D := nestedOpens V U
      let e := (nestedOpensDiffeo (n := n) hWV).symm
      let v := (Subtype.val : V → Y)
      let d := (Subtype.val : D → V)
      let u := (Subtype.val : U → Y)
      let L := restrict W T
      let tail := transport e (restrict D S)
      let Q := L.append tail.tower
      let AW := geoTransformAlong (geometricTemplate (X := XW) NW BW) L
      let phaseW := restrictRetainedCrestPhase (X := XO) hn hNO hEO hTrO hDenseO phase W
      have hPW : phaseW.rank = retainedDefectOrderedRank N old born x :=
        (restrictRetainedCrestPhase_rank hn hNO hEO hTrO hDenseO phase W).trans hPhaseRank
      have hGeom : NativeRetainedGeometry A.N OY A.E :=
        ⟨hRec.1,hRec.2.1,hRec.2.2.1,hRec.2.2.2.1⟩
      have hGeomV := hGeom.restrict V
      have hChild := (history.restrictOpen D hGeomV).rebase e (hGeomV.restrict D)
      have hCurrent := geoTransformAlong_restrict W hNO isCoherent_unitIdeal T hT
      rw [HironakaG34NonPureLowDim.template_pullback (X := XO) (Y := XW)] at hCurrent
      have hNextN : e ⁻¹' (d ⁻¹' (v ⁻¹' A.N)) = AW.N :=
        (congrArg (fun M : MarkedIdeal n U => M.N) hCurrent).symm
      have hNextOld :
          (((OY.map (v ⁻¹' ·)).map (d ⁻¹' ·)).map (e ⁻¹' ·)) = OW.map (strictAlong L) := by
        simp only [OY,OW,List.map_map]
        apply List.map_congr_left
        intro H _hH
        exact (strictAlong_restrict W T H).symm
      have hNextBorn : ((A.E.map (v ⁻¹' ·)).map (d ⁻¹' ·)).map (e ⁻¹' ·) = AW.E := by
        simp only [List.map_map]
        exact (congrArg (fun M : MarkedIdeal n U => M.E) hCurrent).symm
      change OrderedRetainedDefectTrace hn _ _ _ (retainedDefectOrderedRank N old born x : RetainedStampRank)
        tail.tower at hChild
      rw [hNextN,hNextOld,hNextBorn,←hPW] at hChild
      have hPhaseBound : (phaseW.rank : WithTop RetainedStampRank) < μ := by
        rw [hPW]
        exact hRank x hx
      have hL : IsGeoTestTower (geometricTemplate (X := XW) NW BW) L := by
        have h := isGeoTestTower_restrict W hNO isCoherent_unitIdeal T hT
        rw [HironakaG34NonPureLowDim.template_pullback (X := XO) (Y := XW)] at h
        exact h
      have hFullL : IsGeoTestTower (geometricTemplate (X := XW) (univ : Set W) (OW ++ BW)) L := by
        have h := isGeoTestTower_restrict W isClosedSubmanifold_univ isCoherent_unitIdeal T hFull
        rw [HironakaG34NonPureLowDim.template_pullback (X := XO) (Y := XW),Set.preimage_univ,List.map_append] at h
        exact h
      let hTrace : OrderedRetainedDefectTrace hn NW OW BW μ Q :=
        .phase L tail.tower phaseW hPhaseBound hL hFullL hChild
      have hOut : HasOrderedRetainedDefectExitNear (X := XO) hn NO OO BO K₀ μ :=
        ⟨W,hKW,tail.target,Q,hQ,hFullQ,hSharpQ,hEndQ,⟨hTrace⟩⟩
      exact retained_exit_flatten hn hN hE hTr hdense O hKO hOut
    · exact retained_exit_without_defect_near hn hN hE hTr hdense hClosed hNonempty

/-- The finite actual sharp tower near a compact enclosure comes with
the surviving ordered crest selections and their actual source changes. -/
theorem exists_ordered_retained_defect_exit_near_compact (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    {K : Set X} (hK : IsCompact K) : HasOrderedRetainedDefectExitNear hn N old born K ⊤ :=
  retained_exit_of_rank_lt hn ⊤ hN hE hTr hdense hK (fun _ _ => WithTop.coe_lt_top _)

/-- On a neighbourhood of any compact enclosure, a finite actual sharp
tower eliminates the true retained distinct-germ defect everywhere. The
initial defect may be noncompact and the compact set may meet it. -/
theorem exists_retained_defect_exit_near_compact (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    {K : Set X} (hK : IsCompact K) : HasRetainedDefectExitNear N old born K := by
  obtain ⟨O,hKO,Y,T,hT,hFull,hSharp,hDef,_trace⟩ :=
    exists_ordered_retained_defect_exit_near_compact hn hN hE hTr hdense hK
  exact ⟨O,hKO,Y,T,hT,hFull,hSharp,hDef⟩

end
end Hironaka.HironakaG4RetainedDefectRelativeExit
