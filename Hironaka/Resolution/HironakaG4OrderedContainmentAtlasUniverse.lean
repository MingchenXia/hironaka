import Hironaka.Resolution.HironakaG4OrderedContainmentAtlas
import Hironaka.Resolution.HironakaG4FullBoundaryUniverse
import Hironaka.Resolution.HironakaG4SharpStableAtlas
import Hironaka.Resolution.HironakaG3UniverseProvenancePhysical

/-! The ordered arbitrary-containment atlas after physical universe lift. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
universe u

namespace Hironaka.HironakaG4OrderedContainmentAtlasUniverse

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  BlowupTowerIsoTail HironakaG3RTowerClass G3UniversePhysicalClassComparisons
  HironakaG4OrderedContainmentAtlas HironakaG4FullBoundaryUniverse HironakaG4SharpTerminalAtlas
  HironakaG4SharpStableAtlas NormalCrossings NormalCrossingsInvariance
  HironakaG3UniverseSmallManifold HironakaG3UniverseShrinkManifold HironakaG3UniverseCarrierGeometry
  HironakaG3UniverseOrderedBoundary HironakaG3UniverseLiftManifold G3UniverseLiftedTower
  G3UniverseOpenDiffeo G3UniverseChartTowerTransport G3UniverseChartProvenance G3UniverseProvenancePhysical

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- The actual compatible small histories lift to compatible sharp histories
on the literal compact-enclosed opens of the original ambient manifold. -/
theorem exists_glued_full_sharp_cleanup_of_dense_all_universes {n : ℕ}
    (hService : 0 < n → DenseSharpAtlasService n)
    {X : CMfd.{u} n} {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) :
    ∃ (C : LocalTowerClass X) (Z : CMfd.{u} n) (P : Z → X),
      IsGluedSharpCleanup C W E Z P ∧
      ∀ (U : Opens X) (K : Set X), IsCompact K → (U : Set X) ⊆ K →
        ∃ c : TowerChart C Z P, c.U = U := by
  by_cases hn : 0 < n
  · let X₀ := shrinkCMfd X
    let e := shrinkDiffeomorph X
    let : Small.{0} X := complex_manifold_small X
    let W₀ : Set X₀ := e.symm ⁻¹' W
    let E₀ := E.map (e.symm ⁻¹' ·)
    have hW₀ : IsClosedSubmanifold n W₀ := transported_closedSubmanifold e.toHomeomorph W hW
    have hE₀ : IsSNCDivisor n E₀ := transported_list_snc X e.toHomeomorph E hE
    obtain ⟨C₀, hTerm₀, hCmp₀, hLocal₀⟩ := exists_full_sharp_class_of_dense (hService hn) hW₀ hE₀
    let C : LocalTowerClass X := fun U Y T => liftedProvenanceClass e C₀ U Y T ∧
      IsSharpTerminalTower ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) T
    have hTerm : SharpTerminalClass W E C := fun _ _ _ h => h.2
    have hPhysical := lifted_provenance_hasPhysicalComparisons e C₀ hCmp₀
    have hCmp : HasPhysicalComparisons C := by
      intro U V Y Z T S hT hS
      exact hPhysical U V Y Z T S hT.1 hS.1
    have hLocal (U : Opens X) (K : Set X) (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
        ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y), C U Y T := by
      let U₀ := preimageOpens e.symm U
      let K₀ : Set X₀ := e.symm ⁻¹' K
      have hK₀ : IsCompact K₀ := e.symm.toHomeomorph.isProperMap.isCompact_preimage hK
      have hUK₀ : (U₀ : Set X₀) ⊆ K₀ := fun _ hz => hUK hz
      obtain ⟨Y₀, T₀, hT₀⟩ := hLocal₀ U₀ K₀ hK₀ hUK₀
      let V := preimageOpens e U₀
      have hV : V = U := by
        ext x
        change e.symm (e x) ∈ U ↔ x ∈ U
        rw [e.symm_apply_apply]
      rw [← hV]
      let eV := (preimageDiffeo e U₀).symm
      let S := chartTowerTransport e U₀ T₀
      let WV := (Subtype.val : V → X) ⁻¹' W
      let EV := E.map ((Subtype.val : V → X) ⁻¹' ·)
      have hA : (Subtype.val : U₀ → X₀) ⁻¹' W₀ = eV.symm ⁻¹' WV := rfl
      have hB : E₀.map ((Subtype.val : U₀ → X₀) ⁻¹' ·) = EV.map (eV.symm ⁻¹' ·) := by
        dsimp only [E₀, EV]
        rw [List.map_map, List.map_map]
        rfl
      have hA₀ := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW₀ U₀
      have hB₀ := isSNCDivisor_map_preimage (pullsBackCoordinates_val U₀) continuous_subtype_val hE₀
      have hT := hTerm₀ U₀ Y₀ T₀ hT₀
      rw [hA] at hA₀
      rw [hB] at hB₀
      rw [hA, hB] at hT
      have hS : IsSharpTerminalTower WV EV S.tower :=
        sharpTerminal_transportLift eV WV EV hA₀ hB₀ T₀ hT
      refine ⟨S.target, S.tower, ?_, hS⟩
      refine ⟨U₀, Y₀, T₀, hT₀, rfl, S.back, ?_⟩
      have hBase : (opensCongr (rfl : V = V)).trans (baseLiftDiffeo e U₀) = baseLiftDiffeo e U₀ := by
        apply Diffeomorph.ext
        intro z
        rfl
      rw [hBase]
      exact transport_isTowerIso (baseLiftDiffeo e U₀) (liftTower.{u} T₀)
    obtain ⟨Z, P, hP, hCharts⟩ := glue_compatible_sharp_terminal_histories hW hE hTerm hCmp hLocal
    exact ⟨C, Z, P, hP, hCharts⟩
  · have hzero : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    let T : BlowupTower X X := .refl
    have hLocal (U : Opens X) (_K : Set X) (_hK : IsCompact _K) (_hUK : (U : Set X) ⊆ _K) :
        ∃ (Y : CMfd.{u} 0) (Q : BlowupTower (CMfd.of (n := 0) U) Y), finiteSharpClass T U Y Q :=
      ⟨CMfd.of (n := 0) (openPreimage T U), restrict U T, rfl⟩
    obtain ⟨Z, P, hP, hCharts⟩ := glue_compatible_sharp_terminal_histories hW hE
      (finite_sharp_class_terminal hW T (sharpTerminal_zero hW hE)) (finite_sharp_class_physical T) hLocal
    exact ⟨finiteSharpClass T, Z, P, hP, hCharts⟩

end
end Hironaka.HironakaG4OrderedContainmentAtlasUniverse
