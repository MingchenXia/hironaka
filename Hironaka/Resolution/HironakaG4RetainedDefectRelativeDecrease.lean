import Hironaka.Resolution.HironakaG4RetainedCurrentStamp
import Hironaka.Resolution.HironakaG4RetainedDefectFirstCrest

/-! A selected ordered retained crest gives strict progress across the
whole new native defect on the shrunken ambient. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
universe u

namespace Hironaka.HironakaG4RetainedDefectRelativeDecrease
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower MaxLocusLocal RestrictEmptyTower
  BlowupTowerIsomorphism HironakaEmbeddedResolutionLocal HironakaG4LocalJointProfileMask
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpOriginalProductTraceOrder HironakaActualRetainedBoundaryMaskBlock
  HironakaActualRetainedBoundaryJointStep HironakaActualFiniteMarkedSumHistories
  HironakaG4PreparedCentreCoordinates HironakaG4CompactWholeMonomialMaskPhase HironakaG34JointMaskEquivariance
  HironakaG4RetainedDefectCompactRank HironakaG4OrderedDefectStamp HironakaG4RetainedCurrentStamp
  HironakaG4RetainedDefectFirstCrest HironakaG4RetainedFactorOpenComparison
  HironakaG4RetainedRankOpenComparison HironakaG4RetainedRankTowerIso

open ResolutionInvariantSpec (IsCanonical IsInvDomain)

variable {n : ℕ} {X Y : CMfd.{u} n}

set_option maxHeartbeats 500000 in
/-- The marked record, closed support and physical canonical solution used
by one actual retained phase. The exact crest test still makes sense when
an open restriction removes every point attaining the phase stamp. -/
structure RetainedDefectCrestPhase (hn : 0 < n) (N : Set X) (old born : List (Set X))
    (T : BlowupTower X Y) where
  profile : Fin old.length → ℕ
  inactive : Finset (Fin old.length)
  footprint : Set X
  isClosed_footprint : IsClosed footprint
  active : Opens X
  footprint_subset : footprint ⊆ active
  centresOver : CentresOver footprint T
  rank_bound : ∀ y ∈ actualFamilyDistinctDefect N (oldResidualPart N old born),
    retainedDefectOrderedRank N old born y ≤ orderedDefectStampRank profile inactive
  footprint_iff : ∀ y, y ∈ footprint ↔ y ∈ actualFamilyDistinctDefect N (oldResidualPart N old born) ∧
    retainedDefectOrderedRank N old born y = orderedDefectStampRank profile inactive
  active_record :
    let M := jointProfileMarked N old born (∑ i,profile i) inactive
    let L := MarkedIdeal.pullback (Subtype.val : active → X) M
    L.cosupp = (Subtype.val : active → X) ⁻¹' footprint ∧
    IsInvDomain (n+1) L ∧
    IsCanonical L ((CanonicalCentres.invFamily hn (n+1)).inv L) (restrict active T) ∧
    IsGeoResolution L (restrict active T)

def RetainedDefectCrestPhase.rank {hn : 0 < n} {N : Set X} {old born : List (Set X)}
    {T : BlowupTower X Y} (P : RetainedDefectCrestPhase hn N old born T) : (ℕ ×ₗ ℕ) ×ₗ ℕ :=
  orderedDefectStampRank P.profile P.inactive



set_option maxHeartbeats 1200000 in
/-- The first actual sharp crest lowers the refined rank of every point of
the new true distinct defect below the attained old maximum. Every new
defect point still lies over an old one. The proof keeps genuine native
current residual seeds and every ordered old boundary position. -/
theorem exists_retained_defect_strict_decrease_near_compact_with_phase (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    {K : Set X} (hK : IsCompact K)
    (hClosed : IsClosed (actualFamilyDistinctDefect N (oldResidualPart N old born)))
    (hNonempty : (K ∩ actualFamilyDistinctDefect N (oldResidualPart N old born)).Nonempty) :
    ∃ x ∈ K ∩ actualFamilyDistinctDefect N (oldResidualPart N old born),
      ∃ O : Opens X, K ⊆ O ∧ ∃ (Y : CMfd.{u} n) (Q : BlowupTower (CMfd.of (n := n) O) Y),
        let ν := (Subtype.val : O → X)
        let NO := ν ⁻¹' N
        let OO := old.map (ν ⁻¹' ·)
        let BO := born.map (ν ⁻¹' ·)
        let A := geoTransformAlong (geometricTemplate NO BO) Q
        let E' := OO.map (strictAlong Q)
        IsGeoTestTower (geometricTemplate NO BO) Q ∧
        IsGeoTestTower (geometricTemplate (univ : Set O) (OO ++ BO)) Q ∧
        CurrentSharpCentres NO (OO ++ BO) Q ∧
        ∃ phase : RetainedDefectCrestPhase hn NO OO BO Q,
        phase.rank = retainedDefectOrderedRank N old born x ∧
        ∀ y ∈ actualFamilyDistinctDefect A.N (oldResidualPart A.N E' A.E),
          ν (Q.proj y) ∈ actualFamilyDistinctDefect N (oldResidualPart N old born) ∧
          retainedDefectOrderedRank A.N E' A.E y < retainedDefectOrderedRank N old born x := by
  classical
  obtain ⟨x,hx,O,V,hKO,hCV,_hBound,hMax,hVO,B,Y,Z,ψ,T,Q,hDom,hFoot,hCos,hCan,hRes,hFull,
    hMark,hSharp,hOver,hDrop,χ,hχ⟩ :=
    exists_ordered_retained_defect_first_closed_crest_with_domain hn hN hE hTr hdense hK hClosed hNonempty
  let r := fun i => ordinaryTraceOrder N (oldResidualPart N old born i) x
  let q := ∑ i,r i
  let P := inactiveCanonicalRows N old born r x
  let C := retainedDefectCrest N old born r P
  let M := jointProfileMarked N old born q P
  let XO := CMfd.of (n := n) O
  let ν := (Subtype.val : O → X)
  let NO := ν ⁻¹' N
  let OO := old.map (ν ⁻¹' ·)
  let BO := born.map (ν ⁻¹' ·)
  let A := geoTransformAlong (geometricTemplate NO BO) Q
  let E' := OO.map (strictAlong Q)
  have hMFields : M.N=N ∧ M.E=born := by
    unfold M jointProfileMarked
    cases P.toList.map (canonicalFactorMarked N old born) <;> exact ⟨rfl,rfl⟩
  have hMarkO := isGeoTestTower_geometricTemplate_of_actual_test (MarkedIdeal.pullback ν M) Q hMark
  have hMarkerN : (MarkedIdeal.pullback ν M).N=NO := congrArg (ν ⁻¹' ·) hMFields.1
  have hMarkerE : (MarkedIdeal.pullback ν M).E=BO := congrArg (List.map (ν ⁻¹' ·)) hMFields.2
  rw [hMarkerN,hMarkerE] at hMarkO
  have hFullO : IsGeoTestTower (geometricTemplate (X := XO) (univ : Set O) (OO ++ BO)) Q := by
    simpa only [List.map_append] using hFull
  have hSharpO : CurrentSharpCentres NO (OO ++ BO) Q := by
    simpa only [List.map_append] using hSharp
  have hNO := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN O
  have hEO : IsSNCDivisor n (OO ++ BO) := by
    simpa only [List.map_append] using isSNCDivisor_map_preimage
      (pullsBackCoordinates_val (n := n) O) continuous_subtype_val hE
  have hTrO : IsTransverse n NO BO := isTransverse_preimage (pullsBackCoordinates_val O) hTr
  have hDenseO : NO ⊆ closure (NO \ ⋃ H ∈ OO ++ BO,H) := by
    simpa only [List.map_append] using HironakaG34NonPureLowDim.open_full_density hdense O
  have hCurrent := actual_retained_defect_and_rank_current_tuple (X := XO) hn hNO hEO hTrO hDenseO
    Q hMarkO hFullO
  have hOpen := actual_retained_defect_and_rank_open hn hN hE hTr hdense O
  have hC : IsClosed C := isClosed_retainedDefectCrest hn hN hE hTr hdense hClosed r P
  have hCO : IsClosed (ν ⁻¹' C) := hC.preimage continuous_subtype_val
  let e : Fin old.length ≃ Fin OO.length := finCongr (List.length_map _).symm
  let rO := fun j => r (e.symm j)
  let PO := P.map e.toEmbedding
  let CO := ν ⁻¹' C
  let U := nestedOpens O V
  let v := (Subtype.val : U → O)
  let β := (nestedOpensDiffeo (n := n) hVO).trans ψ.symm
  let f := ((Subtype.val : V → X) ∘ ψ)
  let L := MarkedIdeal.pullback f M
  let MO := jointProfileMarked (X := XO) NO OO BO (∑ i,rO i) PO
  let MU := MarkedIdeal.pullback v MO
  have hRankCast : orderedDefectStampRank rO PO = retainedDefectOrderedRank N old born x := by
    exact orderedDefectStampRank_eq_of_ordered_cast (List.length_map (as := old) _).symm r rO P PO
      (fun i => congrArg r (e.symm_apply_apply i)) rfl
  have hSum : (∑ i,rO i) = q := e.symm.sum_comp r
  have hMO : MarkedIdeal.pullback ν M = MO := by
    change MarkedIdeal.pullback ν M = jointProfileMarked (X := XO) NO OO BO (∑ i,rO i) PO
    rw [hSum]
    exact jointProfileMarked_pullback_open_embedding
      (Y := XO) hn hN hE hTr hdense ν (HironakaBaseChange.isOpenHoloEmbedding_val O) q P
  have hMI := isCoherent_jointProfileMarked hn hN hE hTr hdense q P
  have hF : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ f :=
    contMDiff_subtype_val.comp ψ.contMDiff
  have hPull : MarkedIdeal.pullback β L = MU := by
    change MarkedIdeal.pullback β (MarkedIdeal.pullback f M) = MarkedIdeal.pullback v MO
    rw [←hMO,StepOneTangentChange.pullback_pullback_of_comp hMI hF β.contMDiff
      (d := ν ∘ v) (fun z => by
        simpa only [f,β,Function.comp_apply,Diffeomorph.coe_trans,Diffeomorph.apply_symm_apply]
          using (nestedOpensDiffeo_apply (n := n) hVO z)),StepOneTangentChange.pullback_pullback_of_comp
        hMI (a := ν) (b := v) (d := ν ∘ v) contMDiff_subtype_val contMDiff_subtype_val (fun _ => rfl)]
  have hCanon := isCanonical_of_isTowerIso
    (HironakaFromSeqInvariant.embeddingFields_of_seq (CanonicalCentres.invFamily hn (n+1)))
    hDom β hχ hCan
  have hResolution := (IsTowerIso.isGeoResolution_iff β hDom.isWellFormed.isClosedSubmanifold_N
    hDom.isWellFormed.isCoherent hχ).mpr hRes
  have hDomain := InvDomainTowerAlong.isInvDomain_pullback β hDom
  rw [hPull] at hCanon hResolution hDomain
  have hCosU : MU.cosupp = v ⁻¹' CO := by
    change (MarkedIdeal.pullback v MO).cosupp = v ⁻¹' CO
    rw [←hMO,StepOneTangentChange.pullback_pullback_of_comp hMI (a := ν) (b := v)
      (d := ν ∘ v) contMDiff_subtype_val contMDiff_subtype_val (fun _ => rfl)]
    have hCosV := cosupp_pullback_val M (fun _ _ h => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      hMI h) V
    let g := nestedOpensDiffeo (n := n) hVO
    have hPullV : MarkedIdeal.pullback (ν ∘ v) M =
        MarkedIdeal.pullback g (MarkedIdeal.pullback (Subtype.val : V → X) M) :=
      (StepOneTangentChange.pullback_pullback_of_comp hMI contMDiff_subtype_val g.contMDiff
        (fun _ => rfl)).symm
    have hCohV : (MarkedIdeal.pullback (Subtype.val : V → X) M).ideal.IsCoherent :=
      GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hMI
    rw [hPullV,MarkedIdealTowerTransport.cosupp_pullback_eq (Φ := g) hCohV,hCosV]
    exact Set.ext (fun z => hCos (g z).val (g z).property)
  let hPhase : RetainedDefectCrestPhase hn NO OO BO Q :=
    { profile := rO
      inactive := PO
      footprint := CO
      isClosed_footprint := hCO
      active := U
      footprint_subset := fun z hz => hCV ⟨hz,z.property⟩
      centresOver := hOver
      rank_bound := fun y hy => by
        rw [hOpen.2 y,hRankCast]
        exact hMax y.val y.property (by rwa [hOpen.1] at hy)
      footprint_iff := fun y => by
        change ν y ∈ C ↔ y ∈ actualFamilyDistinctDefect NO (oldResidualPart (X := XO) NO OO BO) ∧
          retainedDefectOrderedRank NO OO BO y = orderedDefectStampRank rO PO
        rw [hOpen.1,hOpen.2 y,hRankCast]
        exact hFoot y.val y.property
      active_record := ⟨hCosU,hDomain,hCanon,hResolution⟩ }
  refine ⟨x,hx,O,hKO,Y,Q,hMarkO,hFullO,hSharpO,hPhase,hRankCast,?_⟩
  intro y hy
  have hyD : y ∈ retainedDistinctDefect NO OO BO Q := hCurrent.1 ▸ hy
  let z := Q.proj y
  have hRank : retainedDefectOrderedRank A.N E' A.E y = retainedDefectOrderedRankAlong NO OO BO Q y :=
    hCurrent.2 y
  by_cases hzC : ν z ∈ C
  · have hzD : ν z ∈ actualFamilyDistinctDefect N (oldResidualPart N old born) := hzC.1.1
    have hyN : y ∈ strictAlong Q NO := by
      rw [←show A.N = strictAlong Q NO from N_geoTransformAlong _ Q]
      exact hyD.1
    let rY := retainedProfileAlong NO OO BO Q y
    let PY := retainedInactiveRows NO OO BO rY Q y
    have hPair : toLex ((∑ i,rY i),PY.card) < toLex ((∑ i,r i),P.card) := hDrop y hyN hzC
    refine ⟨hzD,hRank.trans_lt ?_⟩
    exact orderedDefectStampRank_lt_of_pair_lt r rY P PY hPair
  · have hzOff : z ∉ ν ⁻¹' C := hzC
    have hzD₀ := (actual_retained_defect_unchanged_off_closed_footprint (X := XO)
      hn hNO hEO hTrO hDenseO Q hMarkO hFullO hCO hOver y hzOff).mp hyD
    have hzD : ν z ∈ actualFamilyDistinctDefect N (oldResidualPart N old born) := by
      change z ∈ ν ⁻¹' actualFamilyDistinctDefect N (oldResidualPart N old born)
      rw [←hOpen.1]
      exact hzD₀
    have hStamp := actual_retained_stamp_unchanged_off_closed_footprint (X := XO)
      hn hNO hEO hTrO hDenseO Q hMarkO hFullO hCO hOver y hzOff
    have hRankZ : retainedDefectOrderedRankAlong NO OO BO Q y = retainedDefectOrderedRank NO OO BO z := by
      unfold retainedDefectOrderedRankAlong retainedDefectOrderedRank retainedDefectStamp
      dsimp only
      rw [hStamp.2.1,funext hStamp.1]
    have hlt : retainedDefectOrderedRank N old born (ν z) < retainedDefectOrderedRank N old born x := by
      apply lt_of_le_of_ne (hMax (ν z) z.property hzD)
      intro he
      have hEq := retainedDefectStamp_eq_of_orderedRank_eq N old born he
      have hRows : (fun i => ordinaryTraceOrder N (oldResidualPart N old born i) (ν z)) = r :=
        congrArg Prod.fst hEq
      have hMask := congrArg Prod.snd hEq
      change inactiveCanonicalRows N old born
        (fun i => ordinaryTraceOrder N (oldResidualPart N old born i) (ν z)) (ν z) = P at hMask
      rw [hRows] at hMask
      exact hzC (mem_retainedDefectCrest_of_profile_mask_eq hn hN hE hTr hdense r P hzD
        (congrFun hRows) hMask)
    exact ⟨hzD,((hRank.trans hRankZ).trans (hOpen.2 z)).trans_lt hlt⟩

set_option maxHeartbeats 700000 in
/-- The first actual sharp crest lowers the refined rank of every point of
the new true distinct defect below the attained old maximum. Every new
defect point still lies over an old one. The proof keeps genuine native
current residual seeds and every ordered old boundary position. -/
theorem exists_retained_defect_strict_decrease_near_compact (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    {K : Set X} (hK : IsCompact K)
    (hClosed : IsClosed (actualFamilyDistinctDefect N (oldResidualPart N old born)))
    (hNonempty : (K ∩ actualFamilyDistinctDefect N (oldResidualPart N old born)).Nonempty) :
    ∃ x ∈ K ∩ actualFamilyDistinctDefect N (oldResidualPart N old born),
      ∃ O : Opens X, K ⊆ O ∧ ∃ (Y : CMfd.{u} n) (Q : BlowupTower (CMfd.of (n := n) O) Y),
        let ν := (Subtype.val : O → X)
        let NO := ν ⁻¹' N
        let OO := old.map (ν ⁻¹' ·)
        let BO := born.map (ν ⁻¹' ·)
        let A := geoTransformAlong (geometricTemplate NO BO) Q
        let E' := OO.map (strictAlong Q)
        IsGeoTestTower (geometricTemplate NO BO) Q ∧
        IsGeoTestTower (geometricTemplate (univ : Set O) (OO ++ BO)) Q ∧
        CurrentSharpCentres NO (OO ++ BO) Q ∧
        ∀ y ∈ actualFamilyDistinctDefect A.N (oldResidualPart A.N E' A.E),
          ν (Q.proj y) ∈ actualFamilyDistinctDefect N (oldResidualPart N old born) ∧
          retainedDefectOrderedRank A.N E' A.E y < retainedDefectOrderedRank N old born x := by
  obtain ⟨x,hx,O,hKO,Y,Q,hMark,hFull,hSharp,_phase,_hRank,hDrop⟩ :=
    exists_retained_defect_strict_decrease_near_compact_with_phase hn hN hE hTr hdense
      hK hClosed hNonempty
  exact ⟨x,hx,O,hKO,Y,Q,hMark,hFull,hSharp,hDrop⟩

end
end Hironaka.HironakaG4RetainedDefectRelativeDecrease
