import Hironaka.Resolution.HironakaG34ProcessedMaskEquivariance
import Hironaka.Resolution.HironakaG4ProcessedMaskNearCompact
import Hironaka.Resolution.HironakaG4NativeProcessedMaskCanonical
import Hironaka.Resolution.HironakaG4RetainedDefectTraceEquivariance

/-! Strict equivariance of the actual compact-relative processed mask tails. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4StrictRelativeMaskEquivariance

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealRestrictOpen NormalCrossings NormalCrossingsInvariance
  MaxLocusLocal HironakaG34MaskFoldEquivariance HironakaG34CanonicalLocalEquivariance
  HironakaG34ProcessedMaskEquivariance HironakaG4ProcessedMaskNearCompact
  HironakaG4NativeProcessedMaskCanonical HironakaActualProcessedAllMasksDrop
  HironakaActualProcessedMaskControlledSum HironakaG4ProcessedStateRestriction
  HironakaG34NonPureLowDim HironakaSharpActualFiniteChronologicalHistory
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Canonicality of the actual processed mask on the whole current stage gives strict
equivariance of the same appended tower, for any fixed selected original rows. -/
theorem isEquivariant_append_processed_mask (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hEq : IsEquivariant W E T) (P : Finset (Fin E.length)) (R : BlowupTower Y Z) :
    let M := processedMaskMarked W E T P
    IsInvDomain (n + 1) M → IsCanonical M ((CanonicalCentres.invFamily hn (n + 1)).inv M) R →
      IsEquivariant W E (T.append R) := by
  intro M hDom hCan U U' φ hφW hφE
  obtain ⟨χ, hχ⟩ := hEq U U' φ hφW hφE
  exact exists_isTowerIso_restrict_append_of_isCanonical φ (CanonicalCentres.invFamily hn (n + 1)) T hχ hDom
    (pullback_restrict_processedMaskMarked hn hW hE hDense T hT hFull P hDom φ hφW hφE hχ) R hCan

/-- The same strict comparison applies to the processed mask calculated on a literal compact
window and appends the very same canonical suffix on the restricted original prefix. -/
theorem isEquivariant_restricted_append_processed_mask (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hEq : IsEquivariant W E T) (P : Finset (Fin E.length)) (O : Opens X)
    (Q : BlowupTower (CMfd.of (n := n) (openPreimage T O)) Z) :
    let v := (Subtype.val : O → X)
    let WO := v ⁻¹' W
    let EO := E.map (v ⁻¹' ·)
    let e : Fin E.length ≃ Fin EO.length := finCongr (List.length_map _).symm
    let PO := P.map e.toEmbedding
    let L := restrict O T
    let M := processedMaskMarked WO EO L PO
    IsInvDomain (n + 1) M → IsCanonical M ((CanonicalCentres.invFamily hn (n + 1)).inv M) Q →
      IsEquivariant WO EO (L.append Q) := by
  intro v WO EO e PO L M hDom hCan
  have hWO : IsClosedSubmanifold n WO := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW O
  have hEO : IsSNCDivisor n EO := isSNCDivisor_map_preimage
    (pullsBackCoordinates_val (n := n) O) continuous_subtype_val hE
  have hDenseO : WO ⊆ closure (WO \ ⋃ H ∈ EO, H) := open_full_density hDense O
  have hLO := isGeoTestTower_restrict O hW IdealWeightPowers.isCoherent_unitIdeal T hT
  rw [template_pullback (X := X) (Y := CMfd.of (n := n) O), List.map_nil] at hLO
  have hFullO := isGeoTestTower_restrict O HomogenizedGlueingTower.isClosedSubmanifold_univ
    IdealWeightPowers.isCoherent_unitIdeal T hFull
  rw [template_pullback (X := X) (Y := CMfd.of (n := n) O), preimage_univ] at hFullO
  exact isEquivariant_append_processed_mask hn hWO hEO hDenseO L hLO hFullO
    (HironakaG4RetainedDefectTraceEquivariance.isEquivariant_restrictOpen hEq O) PO Q hDom hCan

/-- The compact-relative high-count producer keeps its actual geometry and admits strict
equivariance of the appended tower on the returned literal neighbourhood. -/
theorem exists_equivariant_processed_mask_block_near_compact (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (T : BlowupTower X Y) (P : Finset (Fin E.length)) (hP : 2 ≤ P.card)
    (hAt : At W E P.card T) (hEq : IsEquivariant W E T) (K : Set X) (hK : IsCompact K) :
    ∃ O : Opens X, K ⊆ O ∧ ∃ (Z : CMfd.{u} n)
      (Q : BlowupTower (CMfd.of (n := n) (openPreimage T O)) Z),
      let v := (Subtype.val : O → X)
      let WO := v ⁻¹' W
      let EO := E.map (v ⁻¹' ·)
      let e : Fin E.length ≃ Fin EO.length := finCongr (List.length_map _).symm
      let PO := P.map e.toEmbedding
      let L := restrict O T
      let M := processedMaskMarked WO EO L PO
      IsInvDomain (n + 1) M ∧
      IsCanonical M ((CanonicalCentres.invFamily hn (n + 1)).inv M) Q ∧
      IsGeoResolution M Q ∧
      (∀ k : ℕ, Forward WO EO P.card L (BlowupTowerSplit.head Q k)) ∧
      Erased WO EO (L.append Q) PO ∧ IsEquivariant WO EO (L.append Q) := by
  obtain ⟨O, hKO, Z, Q, hDom, hCan, hRes, hForward, hErased⟩ :=
    exists_processed_mask_canonical_block_near_compact hn hW hE hDense T P hP hAt K hK
  exact ⟨O, hKO, Z, Q, hDom, hCan, hRes, hForward, hErased,
    isEquivariant_restricted_append_processed_mask hn hW hE hDense T hAt.1 hAt.2.1 hEq P O Q hDom hCan⟩

/-- The native singleton producer on a prescribed compact-enclosed open carries strict equivariance
of the same appended original tower, together with both full geometric tests. -/
theorem exists_equivariant_count_one_processed_mask_on_compact_open (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (T : BlowupTower X Y) (P : Finset (Fin E.length)) (hP : P.card = 1)
    (hAt : At W E 1 T) (hEq : IsEquivariant W E T)
    (O : Opens X) (hCl : IsCompact (closure (O : Set X))) :
    ∃ (Z : CMfd.{u} n) (Q : BlowupTower (CMfd.of (n := n) (openPreimage T O)) Z),
      let v := (Subtype.val : O → X)
      let WO := v ⁻¹' W
      let EO := E.map (v ⁻¹' ·)
      let e : Fin E.length ≃ Fin EO.length := finCongr (List.length_map _).symm
      let PO := P.map e.toEmbedding
      let L := restrict O T
      let M := processedMaskMarked WO EO L PO
      IsInvDomain (n + 1) M ∧
      IsCanonical M ((CanonicalCentres.invFamily hn (n + 1)).inv M) Q ∧
      IsGeoResolution M Q ∧
      IsGeoTestTower (geometricTemplate WO []) (L.append Q) ∧
      IsGeoTestTower (geometricTemplate (univ : Set O) EO) (L.append Q) ∧
      HironakaG4CompactWholeMonomialMaskPhase.CurrentSharpCentres WO EO (L.append Q) ∧
      (∀ k : ℕ, let M₀ := geoTransformAlong M (BlowupTowerSplit.head Q k)
        MonomialPartAlong.IsMonomialAlong n M₀.N M₀.ideal M₀.E) ∧
      IsEquivariant WO EO (L.append Q) := by
  obtain ⟨Z, Q, hDom, hCan, hRes, hT, hFull, hSharp, hMono⟩ :=
    exists_count_one_native_processed_mask_on_compact_open hn hW hE hDense T P hP hAt O hCl
  exact ⟨Z, Q, hDom, hCan, hRes, hT, hFull, hSharp, hMono,
    isEquivariant_restricted_append_processed_mask hn hW hE hDense T hAt.1 hAt.2.1 hEq P O Q hDom hCan⟩

end
end Hironaka.HironakaG4StrictRelativeMaskEquivariance
