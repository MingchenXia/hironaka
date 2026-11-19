import Hironaka.Resolution.HironakaG4ProcessedStateRestriction
import Hironaka.Resolution.HironakaEmbeddedResolutionLocal
import Hironaka.Resolution.HironakaSaturatedTowerAppend

/-! A literal processed-mask block over a compact enclosure. Its support may
be noncompact. The relative canonical resolver acts on the actual coherent
sum, and the physical stage law comes from the held processed mask proof. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4ProcessedMaskNearCompact

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen MarkedIdealTowerTransport
  MarkedIdealOpenBiholomorphism
  NormalCrossings NormalCrossingsInvariance HironakaG34NonPureLowDim
  HironakaG4ProcessedMaskRestriction HironakaG4ProcessedStateRestriction
  HironakaActualProcessedAllMasksDrop HironakaActualProcessedMaskFiniteBlock
  HironakaActualProcessedMaskControlledSum
  HironakaSharpActualFiniteChronologicalHistory HironakaG4MonomialFamilyInvariant
  HironakaSaturatedTowerAppend HironakaEmbeddedResolutionLocal MaxLocusLocal
  HironakaLocalPrincipalization

variable {n : ℕ} {X Y : CMfd.{u} n}

set_option maxHeartbeats 650000 in
/-- On one literal neighbourhood of the enclosure, erase the selected
original mask using an actual tail of the restricted original prefix. Both
tests and all residual rows are recorded on every actual tail prefix. -/
theorem exists_processed_mask_canonical_block_near_compact (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (P : Finset (Fin E.length)) (hP : 2 ≤ P.card)
    (hAt : At W E P.card T) (K : Set X) (hK : IsCompact K) :
    ∃ O : Opens X, K ⊆ O ∧ ∃ (Z : CMfd.{u} n) (Q : BlowupTower (CMfd.of (n := n) (openPreimage T O)) Z),
      let v := (Subtype.val : O → X)
      let WO := v ⁻¹' W
      let EO := E.map (v ⁻¹' ·)
      let e : Fin E.length ≃ Fin EO.length := finCongr (List.length_map _).symm
      let PO := P.map e.toEmbedding
      let R := restrict O T
      let M := processedMaskMarked WO EO R PO
      ResolutionInvariantSpec.IsInvDomain (n+1) M ∧
      ResolutionInvariantSpec.IsCanonical M ((CanonicalCentres.invFamily hn (n+1)).inv M) Q ∧
      IsGeoResolution M Q ∧
      (∀ k : ℕ,Forward WO EO P.card R (BlowupTowerSplit.head Q k)) ∧
      Erased WO EO (R.append Q) PO := by
  let M := processedMaskMarked W E T P
  have hDom := (actual_processed_mask_controlled_record (Z := Y) hn hW hE hdense
    T hAt.1 hAt.2.1 hAt.2.2.2.1 hAt.2.2.2.2.1 hAt.2.2.2.2.2.1 P hP hAt.2.2.2.2.2.2.2).1
  have hMW : M.IsWellFormed := hDom.isWellFormed
  have hKY : IsCompact (T.proj ⁻¹' K) := (isProperMap_proj T).isCompact_preimage hK
  obtain ⟨V,hKV,Z,S,hCan,hS⟩ := exists_local_resolution_isCanonical
    (CanonicalCentres.invFamily hn (n+1)) hDom hKY
  obtain ⟨O,hKO,hOV,hIso,_hProj,_hTotal,_hImage,_hStrict,_hST⟩ :=
    exists_saturated_tower_append T K V hKV S
  let U := openPreimage T O
  let D := nestedOpens V U
  let a := (nestedOpensDiffeo (n := n) hOV).symm
  let tail := transport a (restrict D S)
  let R := restrict O T
  let v := (Subtype.val : O → X)
  let WO := v ⁻¹' W
  let EO := E.map (v ⁻¹' ·)
  let e : Fin E.length ≃ Fin EO.length := finCongr (List.length_map _).symm
  let PO := P.map e.toEmbedding
  let M₀ := processedMaskMarked WO EO R PO
  let I := CanonicalCentres.invFamily hn (n+1)
  have hDomV := InvDomainTowerAlong.isInvDomain_pullback_val V hDom
  have hDomD := InvDomainTowerAlong.isInvDomain_pullback_val D hDomV
  have hDomU := InvDomainTowerAlong.isInvDomain_pullback_val U hDom
  have hCanD := Seq.ResolutionInvariantExt.isCanonical_restrict I hDomV D S hCan
  have hCanU := Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso I hDomD a hIso hCanD
  have hMV := IsWellFormed.pullback_val hMW V
  have hTail := isGeoResolution_transport_restrict D a hMV.isClosedSubmanifold_N hMV.isCoherent hS
  change IsGeoResolution
    (MarkedIdeal.pullback a (MarkedIdeal.pullback (Subtype.val : D → V)
      (MarkedIdeal.pullback (Subtype.val : V → Y) M))) tail.tower at hTail
  have hDD : MarkedIdeal.pullback a (MarkedIdeal.pullback (Subtype.val : D → V)
      (MarkedIdeal.pullback (Subtype.val : V → Y) M)) =
      MarkedIdeal.pullback (Subtype.val : U → Y) M :=
    pullback_symm_nestedOpensDiffeo hMW.isCoherent hOV
  rw [hDD] at hTail hCanU
  have hMask : M₀ = MarkedIdeal.pullback (Subtype.val : U → Y) M :=
    (processed_mask_matrix_restrict hn hW hE hdense T hAt.1 hAt.2.1 O).1 P
  rw [←hMask] at hTail hCanU hDomU
  have hWO : IsClosedSubmanifold n WO :=
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW O
  have hEO : IsSNCDivisor n EO :=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val (n := n) O) continuous_subtype_val hE
  have hDenseO : WO ⊆ closure (WO \ ⋃ H ∈ EO,H) := open_full_density hdense O
  have hState := (processed_at_restrict hn hW hE hdense T P.card hAt O).1
  have hCard : PO.card = P.card := Finset.card_map _
  have hAtO : processedAt WO EO PO R := by
    unfold processedAt
    rw [hCard]
    exact hState
  have hPO : 2 ≤ PO.card := hCard ▸ hP
  refine ⟨O,hKO,tail.target,tail.tower,hDomU,hCanU,hTail,?_,?_⟩
  · intro k
    let S₀ := BlowupTowerSplit.head tail.tower k
    have hTest : IsGeoTestTower M₀ S₀ :=
      ((BlowupTowerSplit.isGeoTestTower_iff_head_tail M₀ tail.tower k).mp hTail.1).1
    obtain ⟨hS₀,_hEq,hRows,hActivity⟩ :=
      actual_processed_mask_test_history hn hWO hEO hDenseO R PO hPO hAtO S₀ hTest
    change Forward WO EO P.card R S₀
    unfold processedAt at hS₀
    rw [hCard] at hS₀
    exact ⟨hS₀,hRows,hActivity⟩
  · obtain ⟨hEnd,hEq,_hRows,_hAct⟩ :=
      actual_processed_mask_test_history hn hWO hEO hDenseO R PO hPO hAtO tail.tower hTail.1
    intro z hz hMaskAt
    have hzM := (mem_processed_mask_cosupport_iff hn hWO hEO hDenseO
      (R.append tail.tower) hEnd.1 hEnd.2.1 PO z).mpr ⟨hz,hMaskAt⟩
    rw [←hEq,hTail.2] at hzM
    exact Set.notMem_empty z hzM

/-- The processed mask block, with the recorded forward and terminal laws. -/
theorem exists_processed_mask_block_near_compact (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (P : Finset (Fin E.length)) (hP : 2 ≤ P.card)
    (hAt : At W E P.card T) (K : Set X) (hK : IsCompact K) :
    ∃ O : Opens X, K ⊆ O ∧ ∃ (Z : CMfd.{u} n) (Q : BlowupTower (CMfd.of (n := n) (openPreimage T O)) Z),
      let v := (Subtype.val : O → X)
      let WO := v ⁻¹' W
      let EO := E.map (v ⁻¹' ·)
      let e : Fin E.length ≃ Fin EO.length := finCongr (List.length_map _).symm
      let PO := P.map e.toEmbedding
      let R := restrict O T
      IsGeoResolution (processedMaskMarked WO EO R PO) Q ∧
      (∀ k : ℕ,Forward WO EO P.card R (BlowupTowerSplit.head Q k)) ∧
      Erased WO EO (R.append Q) PO := by
  obtain ⟨O,hKO,Z,S,_hDom,_hCan,hRes,hForward,hErase⟩ :=
    exists_processed_mask_canonical_block_near_compact hn hW hE hdense T P hP hAt K hK
  exact ⟨O,hKO,Z,S,hRes,hForward,hErase⟩

end
end Hironaka.HironakaG4ProcessedMaskNearCompact
