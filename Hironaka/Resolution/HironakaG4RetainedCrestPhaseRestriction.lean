import Hironaka.Resolution.HironakaG4RetainedDefectRelativeDecrease
import Hironaka.Resolution.HironakaG3CentresOverGenericFactor

/-! Actual restriction of a certified retained crest, including absent phases. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
universe u

namespace Hironaka.HironakaG4RetainedCrestPhaseRestriction
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MaxLocusLocal
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealRestrictOpen MarkedIdealBiholomorphism
  NormalCrossings SimultaneousNormalCrossings HironakaG3CentresOverGenericFactor
  HironakaG4PreparedCentreCoordinates HironakaActualRetainedBoundaryJointStep
  HironakaG4LocalJointProfileMask HironakaG4RetainedCurrentStamp HironakaG4OrderedDefectStamp HironakaG34JointMaskEquivariance
  HironakaG4RetainedDefectRelativeDecrease HironakaEmbeddedResolutionLocal
open ResolutionInvariantSpec (IsCanonical IsInvDomain)

variable {n : ℕ} {X Y : CMfd.{u} n}

set_option maxHeartbeats 950000 in
/-- Restrict both the actual phase tower and its full marked record. The
restricted footprint may be empty. The phase stamp remains its original
ordered stamp under the canonical old-boundary index cast. -/
def restrictRetainedCrestPhase (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    {T : BlowupTower X Y} (P : RetainedDefectCrestPhase hn N old born T) (O : Opens X) :
    let ν := (Subtype.val : O → X)
    RetainedDefectCrestPhase hn (ν ⁻¹' N) (old.map (ν ⁻¹' ·)) (born.map (ν ⁻¹' ·)) (restrict O T) := by
  intro ν
  let XO := CMfd.of (n := n) O
  let NO := ν ⁻¹' N
  let OO := old.map (ν ⁻¹' ·)
  let BO := born.map (ν ⁻¹' ·)
  let e : Fin old.length ≃ Fin OO.length := finCongr (List.length_map _).symm
  let r := fun i => P.profile (e.symm i)
  let p := P.inactive.map e.toEmbedding
  let V := P.active
  let W := O ⊓ V
  have hWO : W ≤ O := inf_le_left
  have hWV : W ≤ V := inf_le_right
  let A := nestedOpens O W
  let B := nestedOpens V W
  let a := (Subtype.val : A → O)
  let b := (Subtype.val : B → V)
  let v := (Subtype.val : V → X)
  let γ := nestedOpensDiffeo (n := n) hWO
  let δ := nestedOpensDiffeo (n := n) hWV
  let φ := γ.trans δ.symm
  let q := ∑ i,P.profile i
  let M := jointProfileMarked N old born q P.inactive
  let MV := MarkedIdeal.pullback v M
  let MO := jointProfileMarked (X := XO) NO OO BO (∑ i,r i) p
  let L := MarkedIdeal.pullback b MV
  let R := MarkedIdeal.pullback a MO
  have hMI := isCoherent_jointProfileMarked hn hN hE hTr hdense q P.inactive
  have hSum : (∑ i,r i) = q := e.symm.sum_comp P.profile
  have hMO : MarkedIdeal.pullback ν M = MO := by
    change MarkedIdeal.pullback ν M = jointProfileMarked (X := XO) NO OO BO (∑ i,r i) p
    rw [hSum]
    exact jointProfileMarked_pullback_open_embedding
      (Y := XO) hn hN hE hTr hdense ν (HironakaBaseChange.isOpenHoloEmbedding_val O) q P.inactive
  have hRank : orderedDefectStampRank r p = P.rank :=
    orderedDefectStampRank_eq_of_ordered_cast (List.length_map (as := old) _).symm P.profile r
      P.inactive p (fun i => congrArg P.profile (e.symm_apply_apply i)) rfl
  have hCos := P.active_record.1
  have hDom := P.active_record.2.1
  have hCanon := P.active_record.2.2.1
  have hRes := P.active_record.2.2.2
  have hEq : MarkedIdeal.pullback φ L = R := by
    change MarkedIdeal.pullback φ (MarkedIdeal.pullback b (MarkedIdeal.pullback v M)) =
      MarkedIdeal.pullback a MO
    rw [←hMO,pullback_val_pullback_val hMI hWV,pullback_val_pullback_val hMI hWO]
    apply StepOneTangentChange.pullback_pullback_of_comp
      (GermIdealPullbackCalculus.isCoherent_pullback
        (f := (Subtype.val : W → X)) contMDiff_subtype_val hMI)
      δ.contMDiff φ.contMDiff
    intro z
    exact δ.apply_symm_apply (γ z)
  have hT := (isTowerIso_restrict_nestedOpens hWO T).trans
    (isTowerIso_restrict_nestedOpens hWV T).symm
  let inv := CanonicalCentres.invFamily hn (n+1)
  have hFields := HironakaFromSeqInvariant.embeddingFields_of_seq inv
  have hLDomain := InvDomainTowerAlong.isInvDomain_pullback_val B hDom
  have hLCanon := HironakaLocalPrincipalization.isCanonical_restrict hFields hDom B (restrict V T) hCanon
  have hLRes := isGeoResolution_restrict B hDom.isWellFormed.isClosedSubmanifold_N
    hDom.isWellFormed.isCoherent hRes
  have hRDom := InvDomainTowerAlong.isInvDomain_pullback φ hLDomain
  have hRCanon := isCanonical_of_isTowerIso hFields hLDomain φ hT hLCanon
  have hRRes := (IsTowerIso.isGeoResolution_iff φ hLDomain.isWellFormed.isClosedSubmanifold_N
    hLDomain.isWellFormed.isCoherent hT).mpr hLRes
  change IsInvDomain (n+1) (MarkedIdeal.pullback φ L) at hRDom
  change IsCanonical (MarkedIdeal.pullback φ L) (inv.inv (MarkedIdeal.pullback φ L)) _ at hRCanon
  change IsGeoResolution (MarkedIdeal.pullback φ L) _ at hRRes
  rw [hEq] at hRDom hRCanon hRRes
  have hRCos : R.cosupp = a ⁻¹' (ν ⁻¹' P.footprint) := by
    rw [←hEq,MarkedIdealTowerTransport.cosupp_pullback_eq (Φ := φ) hLDomain.isWellFormed.isCoherent]
    change φ ⁻¹' (MarkedIdeal.pullback b MV).cosupp = _
    rw [cosupp_pullback_val MV (fun _ _ h =>
      RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hDom.isWellFormed.isCoherent h) B]
    change φ ⁻¹' (b ⁻¹' (MarkedIdeal.pullback v M).cosupp) = _
    rw [hCos]
    rfl
  have hOpen := actual_retained_defect_and_rank_open hn hN hE hTr hdense O
  exact
    { profile := r
      inactive := p
      footprint := ν ⁻¹' P.footprint
      isClosed_footprint := P.isClosed_footprint.preimage continuous_subtype_val
      active := A
      footprint_subset := fun z hz => ⟨z.property,P.footprint_subset hz⟩
      centresOver := centresOver_restrict O P.footprint T P.centresOver
      rank_bound := fun z hz => by
        rw [hOpen.2 z,hRank]
        exact P.rank_bound z.val (by rwa [hOpen.1] at hz)
      footprint_iff := fun z => by
        rw [hOpen.1,hOpen.2 z,hRank]
        exact P.footprint_iff z.val
      active_record := ⟨hRCos,hRDom,hRCanon,hRRes⟩ }

/-- The proof-relevant restriction keeps the numerical ordered stamp. -/
theorem restrictRetainedCrestPhase_rank (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    {T : BlowupTower X Y} (P : RetainedDefectCrestPhase hn N old born T) (O : Opens X) :
    (restrictRetainedCrestPhase hn hN hE hTr hdense P O).rank = P.rank := by
  let e : Fin old.length ≃ Fin (old.map ((Subtype.val : O → X) ⁻¹' ·)).length :=
    finCongr (List.length_map _).symm
  change orderedDefectStampRank (fun i => P.profile (e.symm i)) (P.inactive.map e.toEmbedding) =
    orderedDefectStampRank P.profile P.inactive
  exact orderedDefectStampRank_eq_of_ordered_cast (List.length_map (as := old) _).symm P.profile _
    P.inactive _ (fun i => congrArg P.profile (e.symm_apply_apply i)) rfl

end
end Hironaka.HironakaG4RetainedCrestPhaseRestriction
