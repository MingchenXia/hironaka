import Hironaka.Resolution.HironakaSaturatedMarkedPhase
import Hironaka.Resolution.HironakaG8CompactLexInduction
import Hironaka.Resolution.HironakaG8FiniteSingularTowerMerge
import Hironaka.Resolution.HironakaEmbeddedBoundary
import Hironaka.Resolution.HironakaG10FlatProperShrinking

/-! A singular-centred phase on a neighbourhood of an entire inverse image
extends the original test after a saturated shrinking of the source open. -/

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8SaturatedPrefixAppend

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen MarkedIdealTowerTransport MaxLocusLocal
  HironakaEmbeddedAnalytic HironakaStageCenters NormalCrossings HironakaEmbeddedBoundary
  HironakaG8CompactLexInduction HironakaG8FiniteSingularTowerMerge
  HironakaG8SingularFootprintExtension HironakaCoherentTransformExtension
  HironakaNormalCrossingsSeparationChoiceComparison HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaSaturatedTowerAppend HironakaSaturatedMarkedPhase

private abbrev carrierRecord {n : ℕ} {X : CMfd.{0} n} (W : Set X) (E : List (Set X)) :
    MarkedIdeal n X := ⟨univ, E, vanishingIdeal (n := n) W, 1⟩

set_option maxHeartbeats 800000 in
/-- After shrinking the base around `K`, the literal restriction of the
supplied phase appends to the literal restriction of the original prefix.
The appended boundary, strict transform and projection are read back along
the actual endpoint map of the restricted phase. -/
theorem exists_saturated_singular_phase_append {n : ℕ} {X Y : CMfd.{0} n}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (carrierRecord W E) T)
    (hTStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T)
    (K : Set X) (V : Opens Y) (hKV : T.proj ⁻¹' K ⊆ V)
    {Z : CMfd.{0} n} (S : BlowupTower (CMfd.of (n := n) V) Z)
    (hS : IsGeoTestTower (carrierRecord
      ((Subtype.val : V → Y) ⁻¹' strictTransform n T.proj W)
      ((geoTransformAlong (carrierRecord W E) T).E.map ((Subtype.val : V → Y) ⁻¹' ·))) S)
    (hSStage : StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj ((Subtype.val : V → Y) ⁻¹' strictTransform n T.proj W))) S) :
    ∃ (O : Opens X), K ⊆ O ∧ ∃ (hOV : openPreimage T O ≤ V),
      let U := openPreimage T O
      let D := nestedOpens V U
      let e := (nestedOpensDiffeo (n := n) hOV).symm
      let tail := transport e (restrict D S)
      let A := (restrict O T).append tail.tower
      let WO := (Subtype.val : O → X) ⁻¹' W
      let EO := E.map ((Subtype.val : O → X) ⁻¹' ·)
      let WV := (Subtype.val : V → Y) ⁻¹' strictTransform n T.proj W
      let EV := (geoTransformAlong (carrierRecord W E) T).E.map ((Subtype.val : V → Y) ⁻¹' ·)
      let b : tail.target → Z := fun z => (tail.back z).val
      IsGeoTestTower (carrierRecord WO EO) A ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj WO)) A ∧
      IsTowerIso e tail.tower (restrict D S) tail.back ∧
      (∀ z, (A.proj z).val = T.proj (S.proj (b z)).val) ∧
      strictTransform n A.proj WO = b ⁻¹' strictTransform n S.proj WV ∧
      (geoTransformAlong (carrierRecord WO EO) A).E =
        (geoTransformAlong (carrierRecord WV EV) S).E.map (b ⁻¹' ·) := by
  obtain ⟨O, hKO, hOV, hGeom⟩ := exists_saturated_tower_append T K V hKV S
  let U := openPreimage T O
  let D := nestedOpens V U
  let e := (nestedOpensDiffeo (n := n) hOV).symm
  let L := restrict O T
  let R := restrict D S
  let tail := transport e R
  let M := carrierRecord W E
  let WO := (Subtype.val : O → X) ⁻¹' W
  let EO := E.map ((Subtype.val : O → X) ⁻¹' ·)
  let MO := carrierRecord (X := CMfd.of (n := n) O) WO EO
  let WT := strictTransform n T.proj W
  let ET := (geoTransformAlong M T).E
  let N := carrierRecord WT ET
  let WV := (Subtype.val : V → Y) ⁻¹' WT
  let EV := ET.map ((Subtype.val : V → Y) ⁻¹' ·)
  let NV := carrierRecord (X := CMfd.of (n := n) V) WV EV
  let NL := carrierRecord (strictTransform n L.proj WO) (geoTransformAlong MO L).E
  obtain ⟨hIso, _, hProj, _, _, hStrict⟩ := hGeom
  have hM : M.IsWellFormed := ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,
    CartanIrreducible.cartanCoherence W hW, hE, SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hET := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM T hT).isSNCDivisor
  have hWT := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW T
  have hN : N.IsWellFormed := ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,
    CartanIrreducible.cartanCoherence WT hWT, hET, SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hET⟩
  have hMO : MarkedIdeal.pullback (Subtype.val : O → X) M = MO := pullback_val_mk_vanishingIdeal O E W
  have hNV : MarkedIdeal.pullback (Subtype.val : V → Y) N = NV := pullback_val_mk_vanishingIdeal V ET WT
  obtain ⟨hL, hTail, hBoundary, hFinalE⟩ := saturated_marked_phase_restrict M hM T hT N hN rfl V S
    (hNV.symm ▸ hS) O hOV
  rw [hMO] at hL hBoundary hFinalE
  rw [hNV] at hFinalE
  have hCarrier : strictTransform n L.proj WO = (Subtype.val : U → Y) ⁻¹' WT :=
    strictTransform_restricted_tower O T W
  have hNU : MarkedIdeal.pullback (Subtype.val : U → Y) N = NL := by
    have hEeq : (geoTransformAlong MO L).E = ET.map ((Subtype.val : U → Y) ⁻¹' ·) := hBoundary
    rw [pullback_val_mk_vanishingIdeal, ← hCarrier, ← hEeq]
  rw [hNU] at hTail
  have hPhaseCarrier : e ⁻¹' ((Subtype.val : D → V) ⁻¹' WV) = strictTransform n L.proj WO := by
    rw [hCarrier]
    rfl
  have hWV := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hWT V
  have hTailStage : StageCentres (fun P C => C ⊆ singularSet (n := n)
        (strictTransform n P.proj (strictTransform n L.proj WO))) tail.tower := by
    rw [← hPhaseCarrier]
    have hClosed : IsClosed (e ⁻¹' ((Subtype.val : D → V) ⁻¹' WV)) :=
      (hWV.isClosed.preimage continuous_subtype_val).preimage e.continuous
    apply singular_stages_of_tower_iso _ hClosed e.symm hIso.symm
    have hDouble : e.symm ⁻¹' (e ⁻¹' ((Subtype.val : D → V) ⁻¹' WV)) =
        (Subtype.val : D → V) ⁻¹' WV := by
      ext x
      change (e (e.symm x)).val ∈ WV ↔ x.val ∈ WV
      rw [e.apply_symm_apply]
    rw [hDouble]
    exact singular_stages_restrict WV D S hSStage
  have hWO := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW O
  have hMOwf := MarkedIdealRestrictOpen.IsWellFormed.pullback_val hM O
  rw [hMO] at hMOwf
  obtain ⟨hTest, hStage⟩ := original_test_and_singular_stages_append hWO hMOwf.isSNCDivisor L tail.tower
    hL (singular_stages_restrict W O T hTStage) hTail hTailStage
  exact ⟨O, hKO, hOV, hTest, hStage, hIso, hProj, hStrict W, hFinalE⟩

end
end Hironaka.HironakaG8SaturatedPrefixAppend
