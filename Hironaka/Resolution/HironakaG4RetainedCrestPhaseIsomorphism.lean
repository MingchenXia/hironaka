import Hironaka.Resolution.HironakaG4RetainedCrestPhaseRestriction

/-! Actual change of base of a certified retained crest. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
universe u

namespace Hironaka.HironakaG4RetainedCrestPhaseIsomorphism
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  NormalCrossings SimultaneousNormalCrossings HironakaG3CentresOverGenericFactor
  HironakaG4PreparedCentreCoordinates HironakaActualRetainedBoundaryJointStep
  HironakaG4LocalJointProfileMask HironakaG4RetainedCurrentStamp HironakaG4OrderedDefectStamp
  HironakaG34JointMaskEquivariance HironakaG4RetainedRankTowerIso
  HironakaG4RetainedDefectRelativeDecrease HironakaEmbeddedResolutionLocal StepOneTangentChange
open ResolutionInvariantSpec (IsCanonical IsInvDomain)

variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

set_option maxHeartbeats 850000 in
/-- The actual tower comparison on a new base transports the full crest
certificate, including its active terminal marked test. -/
def rebaseRetainedCrestPhase (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    (φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {T : BlowupTower X Y} {T' : BlowupTower X' Y'}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hIso : IsTowerIso φ T' T χ) (P : RetainedDefectCrestPhase hn N old born T) :
    RetainedDefectCrestPhase hn (φ ⁻¹' N) (old.map (φ ⁻¹' ·)) (born.map (φ ⁻¹' ·)) T' := by
  let N' := φ ⁻¹' N
  let O' := old.map (φ ⁻¹' ·)
  let B' := born.map (φ ⁻¹' ·)
  let e : Fin old.length ≃ Fin O'.length := finCongr (List.length_map _).symm
  let r := fun i => P.profile (e.symm i)
  let p := P.inactive.map e.toEmbedding
  let V := P.active
  let V' : Opens X' := ⟨φ ⁻¹' (V : Set X),V.isOpen.preimage φ.continuous⟩
  have hVV : ∀ z : X',z ∈ V' ↔ φ z ∈ V := fun _ => Iff.rfl
  let ψ := diffeoOpens φ V' V hVV
  let v := (Subtype.val : V → X)
  let v' := (Subtype.val : V' → X')
  let q := ∑ i,P.profile i
  let M := jointProfileMarked N old born q P.inactive
  let M' := jointProfileMarked (X := X') N' O' B' (∑ i,r i) p
  let L := MarkedIdeal.pullback v M
  let L' := MarkedIdeal.pullback v' M'
  have hCoh := isCoherent_jointProfileMarked hn hN hE hTr hdense q P.inactive
  have hSum : (∑ i,r i) = q := e.symm.sum_comp P.profile
  have hM : MarkedIdeal.pullback φ M = M' := by
    change MarkedIdeal.pullback φ M = jointProfileMarked (X := X') N' O' B' (∑ i,r i) p
    rw [hSum]
    exact jointProfileMarked_pullback_open_embedding hn hN hE hTr hdense φ
      (isOpenHoloEmbedding_diffeomorph φ) q P.inactive
  have hL : MarkedIdeal.pullback ψ L = L' := by
    change MarkedIdeal.pullback ψ (MarkedIdeal.pullback v M) = MarkedIdeal.pullback v' M'
    rw [←hM,
      pullback_pullback_of_comp hCoh contMDiff_subtype_val ψ.contMDiff
        (d := φ ∘ v') (fun _ => rfl),
      pullback_pullback_of_comp hCoh φ.contMDiff contMDiff_subtype_val
        (d := φ ∘ v') (fun _ => rfl)]
  have hI := isTowerIso_restrictOpens hVV hIso (isTowerIso_mem_openPreimage_iff hIso hVV)
  have hDom := P.active_record.2.1
  have hDom' := InvDomainTowerAlong.isInvDomain_pullback ψ hDom
  have hCanon := isCanonical_of_isTowerIso
    (HironakaFromSeqInvariant.embeddingFields_of_seq (CanonicalCentres.invFamily hn (n+1)))
    hDom ψ hI P.active_record.2.2.1
  have hRes := (IsTowerIso.isGeoResolution_iff ψ hDom.isWellFormed.isClosedSubmanifold_N
    hDom.isWellFormed.isCoherent hI).mpr P.active_record.2.2.2
  rw [hL] at hDom' hCanon hRes
  have hCos : L'.cosupp = v' ⁻¹' (φ ⁻¹' P.footprint) := by
    rw [←hL,MarkedIdealTowerTransport.cosupp_pullback_eq (Φ := ψ) hDom.isWellFormed.isCoherent]
    change ψ ⁻¹' L.cosupp = _
    rw [P.active_record.1]
    rfl
  have hRank : orderedDefectStampRank r p = P.rank :=
    orderedDefectStampRank_eq_of_ordered_cast (List.length_map (as := old) _).symm P.profile r
      P.inactive p (fun i => congrArg P.profile (e.symm_apply_apply i)) rfl
  have hGeo := actual_retained_defect_and_rank_biholomorph hn hN hE hTr hdense φ
  exact
    { profile := r
      inactive := p
      footprint := φ ⁻¹' P.footprint
      isClosed_footprint := P.isClosed_footprint.preimage φ.continuous
      active := V'
      footprint_subset := fun _ hz => P.footprint_subset hz
      centresOver := centresOver_of_isTowerIso hIso P.footprint P.centresOver
      rank_bound := fun z hz => by
        rw [hGeo.2 z,hRank]
        exact P.rank_bound (φ z) (by rwa [hGeo.1] at hz)
      footprint_iff := fun z => by
        rw [hGeo.1,hGeo.2 z,hRank]
        exact P.footprint_iff (φ z)
      active_record := ⟨hCos,hDom',hCanon,hRes⟩ }

/-- Changing a phase's physical base preserves its numerical stamp. -/
theorem rebaseRetainedCrestPhase_rank (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    (φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {T : BlowupTower X Y} {T' : BlowupTower X' Y'}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hIso : IsTowerIso φ T' T χ) (P : RetainedDefectCrestPhase hn N old born T) :
    (rebaseRetainedCrestPhase hn hN hE hTr hdense φ hIso P).rank = P.rank := by
  let e : Fin old.length ≃ Fin (old.map (φ ⁻¹' ·)).length := finCongr (List.length_map _).symm
  change orderedDefectStampRank (fun i => P.profile (e.symm i)) (P.inactive.map e.toEmbedding) =
    orderedDefectStampRank P.profile P.inactive
  exact orderedDefectStampRank_eq_of_ordered_cast (List.length_map (as := old) _).symm P.profile _
    P.inactive _ (fun i => congrArg P.profile (e.symm_apply_apply i)) rfl

end
end Hironaka.HironakaG4RetainedCrestPhaseIsomorphism
