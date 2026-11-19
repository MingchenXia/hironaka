import Hironaka.Resolution.HironakaG4RetainedCrestPhaseRestriction
import Hironaka.Resolution.HironakaG4OrderedCrestEmptyBorn
import Hironaka.Resolution.HironakaOriginalTerminalPhysicalComparison
import Hironaka.Resolution.HironakaSupportedTowerPhysicalExtension

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
universe u

namespace Hironaka.HironakaG4RetainedCrestPhysicalComparison

noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MaxLocusLocal
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  NormalCrossings SimultaneousNormalCrossings HironakaG4PreparedCentreCoordinates
  HironakaG4OrderedDefectStamp HironakaG4RetainedDefectRelativeDecrease
  HironakaG4OrderedCrestEmptyBorn HironakaActualRetainedBoundaryJointStep
  HironakaG4JointProfileEmptyBorn HironakaOriginalBoundaryEmptyFilterComparison
  HironakaOriginalTerminalPhysicalComparison HironakaSupportedTowerPhysicalExtension
  HironakaG34JointMaskEquivariance HironakaG3EmptyAwareHistory HironakaEmbeddedResolutionLocal
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {n : ℕ} {X Y Z : CMfd.{u} n}

private theorem normalized_pullback_eq (O : Opens X) {M L : MarkedIdeal n X}
    (h : nonemptyBoundary M = nonemptyBoundary L) :
    nonemptyBoundary (X := CMfd.of (n := n) O) (MarkedIdeal.pullback (Subtype.val : O → X) M) =
      nonemptyBoundary (X := CMfd.of (n := n) O) (MarkedIdeal.pullback (Subtype.val : O → X) L) := by
  let f := (Subtype.val : O → X)
  let p (H : Set X) := decide (f ⁻¹' H).Nonempty
  have hLists (E : List (Set X)) :
      E.filter p = (E.filter (fun H => decide H.Nonempty)).filter p := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro H _
    by_cases hH : (f ⁻¹' H).Nonempty
    · have hImage : H.Nonempty := ⟨f hH.some,hH.some_mem⟩
      simp [p,hH,hImage]
    · simp [p,hH]
  have hN := congrArg (fun V : MarkedIdeal n X => V.N) h
  have hI := congrArg (fun V : MarkedIdeal n X => V.ideal) h
  have hd := congrArg (fun V : MarkedIdeal n X => V.d) h
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · exact congrArg (f ⁻¹' ·) hN
  · change (M.E.map (f ⁻¹' ·)).filter _ = (L.E.map (f ⁻¹' ·)).filter _
    rw [List.filter_map,List.filter_map]
    change (M.E.filter p).map _ = (L.E.filter p).map _
    rw [hLists M.E,hLists L.E]
    exact congrArg (fun V : MarkedIdeal n X => (V.E.filter p).map (f ⁻¹' ·)) h
  · exact congrArg (GermIdeal.pullback (m := n) f) hI
  · exact hd

private theorem phase_on_smaller_active (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hDense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G))
    {T : BlowupTower X Y} (P : RetainedDefectCrestPhase hn N old born T)
    (O : Opens X) (hO : O ≤ P.active) :
    let M := jointProfileMarked N old born (∑ i,P.profile i) P.inactive
    let L := MarkedIdeal.pullback (Subtype.val : O → X) M
    IsInvDomain (n+1) L ∧ IsCanonical L ((CanonicalCentres.invFamily hn (n+1)).inv L) (restrict O T) ∧
      IsGeoResolution L (restrict O T) := by
  intro M L
  let V := P.active
  let R := MarkedIdeal.pullback (Subtype.val : V → X) M
  let S := nestedOpens V O
  let B := MarkedIdeal.pullback (Subtype.val : S → V) R
  have hCoh : M.ideal.IsCoherent := isCoherent_jointProfileMarked hn hN hE hTr hDense _ _
  have hDom : IsInvDomain (n+1) R := P.active_record.2.1
  have hCan := P.active_record.2.2.1
  have hRes : IsGeoResolution R (restrict V T) := P.active_record.2.2.2
  let inv := CanonicalCentres.invFamily hn (n+1)
  have hFields := HironakaFromSeqInvariant.embeddingFields_of_seq inv
  have hB : IsInvDomain (n+1) B := InvDomainTowerAlong.isInvDomain_pullback_val S hDom
  have hBC := HironakaLocalPrincipalization.isCanonical_restrict hFields hDom S (restrict V T) hCan
  have hBR := isGeoResolution_restrict S hDom.isWellFormed.isClosedSubmanifold_N
    hDom.isWellFormed.isCoherent hRes
  let e := (nestedOpensDiffeo (n := n) hO).symm
  have hIso := (isTowerIso_restrict_nestedOpens hO T).symm
  have hLD := InvDomainTowerAlong.isInvDomain_pullback e hB
  have hLC := isCanonical_of_isTowerIso hFields hB e hIso hBC
  have hLR := (IsTowerIso.isGeoResolution_iff e hB.isWellFormed.isClosedSubmanifold_N
    hB.isWellFormed.isCoherent hIso).mpr hBR
  change IsInvDomain (n+1) (MarkedIdeal.pullback e B) at hLD
  change IsCanonical (MarkedIdeal.pullback e B) (inv.inv (MarkedIdeal.pullback e B))
    (restrict O T) at hLC
  change IsGeoResolution (MarkedIdeal.pullback e B) (restrict O T) at hLR
  rw [pullback_symm_nestedOpensDiffeo hCoh hO] at hLD hLC hLR
  exact ⟨hLD,hLC,hLR⟩

set_option maxHeartbeats 950000 in
/-- Two retained phases with the same normalized marked record and exact
crest footprint have physically matching supported histories. The literal
old and born lists may be different in each phase. -/
theorem retained_crest_emptyAware_of_matching_marked_and_footprints (hn : 0 < n) {N : Set X}
    {old₁ old₂ born₁ born₂ : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE₁ : IsSNCDivisor n (old₁ ++ born₁)) (hE₂ : IsSNCDivisor n (old₂ ++ born₂))
    (hTr₁ : IsTransverse n N born₁) (hTr₂ : IsTransverse n N born₂)
    (hDense₁ : N ⊆ closure (N \ ⋃ G ∈ old₁ ++ born₁,G))
    (hDense₂ : N ⊆ closure (N \ ⋃ G ∈ old₂ ++ born₂,G))
    {T : BlowupTower X Y} {S : BlowupTower X Z}
    (P : RetainedDefectCrestPhase hn N old₁ born₁ T)
    (Q : RetainedDefectCrestPhase hn N old₂ born₂ S)
    (hM : nonemptyBoundary (jointProfileMarked N old₁ born₁ (∑ i,P.profile i) P.inactive) =
      nonemptyBoundary (jointProfileMarked N old₂ born₂ (∑ i,Q.profile i) Q.inactive))
    (hFoot : P.footprint = Q.footprint) :
    ∃ Ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T S Ψ := by
  let M := jointProfileMarked N old₁ born₁ (∑ i,P.profile i) P.inactive
  let L := jointProfileMarked N old₂ born₂ (∑ i,Q.profile i) Q.inactive
  let O := P.active ⊓ Q.active
  have hO : P.footprint ⊆ O := fun x hx =>
    ⟨P.footprint_subset hx,Q.footprint_subset (hFoot ▸ hx)⟩
  obtain ⟨hD₁,hC₁,hR₁⟩ := phase_on_smaller_active hn hN hE₁ hTr₁ hDense₁ P O inf_le_left
  obtain ⟨_hD₂,hC₂,hR₂⟩ := phase_on_smaller_active hn hN hE₂ hTr₂ hDense₂ Q O inf_le_right
  let A := MarkedIdeal.pullback (Subtype.val : O → X) M
  let B := MarkedIdeal.pullback (Subtype.val : O → X) L
  have hAB := normalized_pullback_eq O hM
  have hCA := (isCanonical_invFamily_nonemptyBoundary_iff hn (n+1) A (restrict O T)).mpr hC₁
  have hCB := (isCanonical_invFamily_nonemptyBoundary_iff hn (n+1) B (restrict O S)).mpr hC₂
  have hRA := (isGeoResolution_nonemptyBoundary_iff A (restrict O T)).mpr hR₁
  have hRB := (isGeoResolution_nonemptyBoundary_iff B (restrict O S)).mpr hR₂
  rw [←hAB] at hCB hRB
  let XO := CMfd.of (n := n) O
  let A₀ := nonemptyBoundary (X := XO) A
  have hD₀ : IsInvDomain (n+1) A₀ := isInvDomain_nonemptyBoundary (X := XO) A hD₁
  obtain ⟨ψ,hψ⟩ := original_terminal_histories_emptyAware_same_record
    (X := XO) hn A₀ hD₀ (restrict O T) (restrict O S) hCA hCB hRA hRB
  obtain ⟨Ψ,hΨ,-⟩ := emptyAware_extends_of_centresOver O hO T S P.centresOver
    (hFoot.symm ▸ Q.centresOver) hψ
  exact ⟨Ψ,hΨ⟩

set_option maxHeartbeats 950000 in
/-- Equal ordered retained crests on the same actual tuple give the same
physical phase, including when the born histories differ by empty slots. -/
theorem retained_crest_emptyAware_of_rank_eq (hn : 0 < n) {N : Set X}
    {old born₁ born₂ : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE₁ : IsSNCDivisor n (old ++ born₁)) (hE₂ : IsSNCDivisor n (old ++ born₂))
    (hTr₁ : IsTransverse n N born₁) (hTr₂ : IsTransverse n N born₂)
    (hDense₁ : N ⊆ closure (N \ ⋃ G ∈ old ++ born₁,G))
    (hDense₂ : N ⊆ closure (N \ ⋃ G ∈ old ++ born₂,G))
    (hBorn : (born₁.filter fun H => decide H.Nonempty) = born₂.filter (fun H => decide H.Nonempty))
    {T : BlowupTower X Y} {S : BlowupTower X Z}
    (P : RetainedDefectCrestPhase hn N old born₁ T)
    (Q : RetainedDefectCrestPhase hn N old born₂ S) (hRank : P.rank = Q.rank) :
    ∃ Ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z,
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T S Ψ := by
  let M := jointProfileMarked N old born₁ (∑ i,P.profile i) P.inactive
  let L := jointProfileMarked N old born₂ (∑ i,Q.profile i) Q.inactive
  have hStamp : (P.profile, P.inactive) = (Q.profile, Q.inactive) := by
    exact orderedDefectStamp_eq_of_rank_eq hRank
  have hM : nonemptyBoundary M = nonemptyBoundary L := by
    dsimp only [M,L]
    rw [← jointProfileMarked_filter_empty_born N old born₁,
      ← jointProfileMarked_filter_empty_born N old born₂, hBorn]
    exact congrArg (fun stamp : (Fin old.length → ℕ) × Finset (Fin old.length) =>
      jointProfileMarked N old (born₂.filter fun H => decide H.Nonempty)
        (∑ i,stamp.1 i) stamp.2) hStamp
  have hDefect := (retainedDefect_and_rank_filter_empty_born N old born₁).1.symm.trans
    ((congrArg (fun B => HironakaSharpActualChronologicalDistinctDefect.actualFamilyDistinctDefect
      N (oldResidualPart N old B)) hBorn).trans
      (retainedDefect_and_rank_filter_empty_born N old born₂).1)
  have hRanks := (retainedDefect_and_rank_filter_empty_born N old born₁).2.symm.trans
    ((congrArg (retainedDefectOrderedRank N old) hBorn).trans
      (retainedDefect_and_rank_filter_empty_born N old born₂).2)
  have hFoot : P.footprint = Q.footprint := by
    ext x
    rw [P.footprint_iff,Q.footprint_iff,hDefect,hRanks]
    change (_ ∧ _ = P.rank) ↔ (_ ∧ _ = Q.rank)
    rw [hRank]
  exact retained_crest_emptyAware_of_matching_marked_and_footprints
    hn hN hE₁ hE₂ hTr₁ hTr₂ hDense₁ hDense₂ P Q hM hFoot

end
end Hironaka.HironakaG4RetainedCrestPhysicalComparison
