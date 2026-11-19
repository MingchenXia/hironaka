import Hironaka.Resolution.HironakaG8NativePhaseCertificate
import Hironaka.Resolution.HironakaSaturatedMarkedPhase
import Hironaka.Resolution.HironakaSaturatedTowerAppend

/-! Exact native terminal certificates on a saturated appended phase. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8SaturatedNativePhase

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealTowerTransport NormalCrossings
  HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance HironakaEmbeddedBoundary
  HironakaNormalCrossingsOpenRestrictionSeparation HomogenizedGlueingTower MaxLocusLocal
  HironakaG8NativePhaseCertificate HironakaSaturatedMarkedPhase HironakaSaturatedTowerAppend

variable {n : ℕ} {X Y Z : CMfd.{0} n}

private abbrev original {B : CMfd.{0} n} (W : Set B) (E : List (Set B)) : MarkedIdeal n B :=
  ⟨univ,E,vanishingIdeal (n := n) W,1⟩

/-- The next input carrier and the entire accumulated list agree
after the literal saturated restriction. -/
theorem saturated_native_input_coordinates {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (original W E) T)
    (V : Opens Y) (S : BlowupTower (CMfd.of (n := n) V) Z)
    (hS : IsGeoTestTower (original
      ((Subtype.val : V → Y) ⁻¹' strictTransform n T.proj W)
      ((geoTransformAlong (original W E) T).E.map ((Subtype.val : V → Y) ⁻¹' ·))) S)
    (O : Opens X) (hOV : openPreimage T O ≤ V) :
    let U := openPreimage T O
    let D := nestedOpens V U
    let e := (nestedOpensDiffeo (n := n) hOV).symm
    let MO := MarkedIdeal.pullback (Subtype.val : O → X) (original W E)
    let WV := (Subtype.val : V → Y) ⁻¹' strictTransform n T.proj W
    let EV := (geoTransformAlong (original W E) T).E.map ((Subtype.val : V → Y) ⁻¹' ·)
    e ⁻¹' ((Subtype.val : D → V) ⁻¹' WV) =
      strictTransform n (restrict O T).proj ((Subtype.val : O → X) ⁻¹' W) ∧
    ((EV.map ((Subtype.val : D → V) ⁻¹' ·)).map (e ⁻¹' ·)) =
      (geoTransformAlong MO (restrict O T)).E := by
  let U := openPreimage T O
  let D := nestedOpens V U
  let e := (nestedOpensDiffeo (n := n) hOV).symm
  let M := original W E
  let MO := MarkedIdeal.pullback (Subtype.val : O → X) M
  let G := strictTransform n T.proj W
  let F := (geoTransformAlong M T).E
  let N := original G F
  let WV := (Subtype.val : V → Y) ⁻¹' G
  let EV := F.map ((Subtype.val : V → Y) ⁻¹' ·)
  have hM : M.IsWellFormed := ⟨isClosedSubmanifold_univ,CartanIrreducible.cartanCoherence W hW,
    hE,SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hG := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW T
  have hF : IsSNCDivisor n F :=
    (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM T hT).isSNCDivisor
  have hN : N.IsWellFormed := ⟨isClosedSubmanifold_univ,CartanIrreducible.cartanCoherence G hG,
    hF,SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hF⟩
  have hV : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : V → Y) N) S := by
    rw [pullback_val_mk_vanishingIdeal V F G]
    exact hS
  have hMarked := saturated_marked_phase_restrict M hM T hT N hN rfl V S hV O hOV
  have hBoundary : ((EV.map ((Subtype.val : D → V) ⁻¹' ·)).map (e ⁻¹' ·)) =
      (geoTransformAlong MO (restrict O T)).E := by
    have hMap : ((EV.map ((Subtype.val : D → V) ⁻¹' ·)).map (e ⁻¹' ·)) =
        (MarkedIdeal.pullback (Subtype.val : U → Y) N).E := by
      change (((F.map ((Subtype.val : V → Y) ⁻¹' ·)).map ((Subtype.val : D → V) ⁻¹' ·)).map
        (e ⁻¹' ·)) = F.map ((Subtype.val : U → Y) ⁻¹' ·)
      rw [List.map_map, List.map_map]
      rfl
    exact hMap.trans hMarked.2.2.1.symm
  have hCarrier : e ⁻¹' ((Subtype.val : D → V) ⁻¹' WV) =
      strictTransform n (restrict O T).proj ((Subtype.val : O → X) ⁻¹' W) :=
    (strictTransform_restricted_tower O T W).symm
  exact ⟨hCarrier,hBoundary⟩

/-- Keep the native phase and its original chronological label when the
next phase is placed on the saturated literal input of an existing prefix. -/
theorem native_phase_on_saturated_input {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (original W E) T)
    (V : Opens Y) (S : BlowupTower (CMfd.of (n := n) V) Z)
    (H : ℕ → ℕ)
    (hS : ActualNativePhase ((Subtype.val : V → Y) ⁻¹' strictTransform n T.proj W)
      ((geoTransformAlong (original W E) T).E.map ((Subtype.val : V → Y) ⁻¹' ·)) H S)
    (O : Opens X) (hOV : openPreimage T O ≤ V) :
    let U := openPreimage T O
    let D := nestedOpens V U
    let e := (nestedOpensDiffeo (n := n) hOV).symm
    let tail := transport e (restrict D S)
    let M := MarkedIdeal.pullback (Subtype.val : O → X) (original W E)
    ActualNativePhase (strictTransform n (restrict O T).proj ((Subtype.val : O → X) ⁻¹' W))
      (geoTransformAlong M (restrict O T)).E H tail.tower := by
  let U := openPreimage T O
  let D := nestedOpens V U
  let e := (nestedOpensDiffeo (n := n) hOV).symm
  let R := restrict D S
  let tr := transport e R
  let G := strictTransform n T.proj W
  let F := (geoTransformAlong (original W E) T).E
  let WV := (Subtype.val : V → Y) ⁻¹' G
  let EV := F.map ((Subtype.val : V → Y) ⁻¹' ·)
  have hG := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW T
  obtain ⟨hCarrier,hBoundary⟩ :=
    saturated_native_input_coordinates hW E hE T hT V S hS.test O hOV
  have hWV := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hG V
  have hWD := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hWV D
  have hPhase := (hS.restrictOpen hWV D).of_isTowerIso hWD (transport_isTowerIso e R)
  change ActualNativePhase (e ⁻¹' ((Subtype.val : D → V) ⁻¹' WV))
    ((EV.map ((Subtype.val : D → V) ⁻¹' ·)).map (e ⁻¹' ·)) H tr.tower at hPhase
  rw [hCarrier,hBoundary] at hPhase
  exact hPhase

end
end Hironaka.HironakaG8SaturatedNativePhase
