import Hironaka.Resolution.HironakaG8SeparatedSmoothPhases
import Hironaka.Resolution.HironakaNormalCrossingsOpenRestrictionSeparation

/-! The precise stronger smooth-boundary centre law and its endpoint data
survive open restriction, a physical rebase, and phase concatenation. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
universe u

namespace Hironaka.HironakaG8SmoothBoundaryTowerTransport

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  RestrictEmptyTower NormalCrossings NormalCrossingsInvariance MarkedIdealTowerTransport MarkedIdealBiholomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaSharpActualFiniteChronologicalHistory
  HironakaEmbeddedBoundary HironakaCoherentTransformExtension HironakaG8UniverseBMTransport
  HironakaG8SeparatedSmoothPhases HironakaG4BoundaryRestrict HironakaG3CentresOverGenericFactor
  HironakaNormalCrossingsOpenRestrictionSeparation HironakaNormalCrossingsSeparationChoiceComparison
  HironakaG4CompactWholeMonomialMaskPhase HironakaAdmissibleSequence HironakaAdmissibleCalculus
  HironakaActualProcessedAllMasksDrop

private theorem restrict_template_boundary {n : ℕ} {X Y : CMfd.{u} n}
    (E : List (Set X)) (O : Opens X) (T : BlowupTower X Y) :
    (geoTransformAlong (geometricTemplate (univ : Set (CMfd.of (n := n) O))
      (E.map ((Subtype.val : O → X) ⁻¹' ·))) (restrict O T)).E =
      (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E.map
        ((Subtype.val : openPreimage T O → Y) ⁻¹' ·) := by
  let M := geometricTemplate (univ : Set X) E
  have hEq : (geometricTemplate (univ : Set (CMfd.of (n := n) O))
      (E.map ((Subtype.val : O → X) ⁻¹' ·))).E =
      (MarkedIdeal.pullback (Subtype.val : O → X) M).E := rfl
  rw [geoTransformAlong_E_eq_of_E_eq hEq]
  exact boundary_geoTransformAlong_restrict M O T

theorem smoothBoundaryStages_restrict {n : ℕ} {X : CMfd.{u} n} (W : Set X) (E : List (Set X)) (O : Opens X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), SmoothBoundaryStages W E T →
      SmoothBoundaryStages ((Subtype.val : O → X) ⁻¹' W) (E.map ((Subtype.val : O → X) ⁻¹' ·)) (restrict O T)
  | _, .refl, _ => trivial
  | _, @BlowupTower.step _ _ Y Z T C π hπ, h => by
    let M := geometricTemplate (univ : Set X) E
    let N := geometricTemplate (univ : Set (CMfd.of (n := n) O)) (E.map ((Subtype.val : O → X) ⁻¹' ·))
    let q : openPreimage T O → Y := Subtype.val
    refine ⟨smoothBoundaryStages_restrict W E O T h.1, ?_⟩
    change (IsClosedSubmanifold n (strictTransform n (restrict O T).proj ((Subtype.val : O → X) ⁻¹' W)) ∧
      q ⁻¹' C ⊆ strictTransform n (restrict O T).proj ((Subtype.val : O → X) ⁻¹' W) ∩ ⋃ H ∈
        (geoTransformAlong N (restrict O T)).E, H) ∧
      HasNormalCrossings n (q ⁻¹' C) (geoTransformAlong N (restrict O T)).E
    have hBoundary : (geoTransformAlong N (restrict O T)).E =
        (geoTransformAlong M T).E.map (q ⁻¹' ·) := restrict_template_boundary E O T
    rw [strictTransform_restricted_tower O T W, hBoundary]
    refine ⟨⟨BlowupRestrictOpen.isClosedSubmanifold_preimage_val h.2.1.1 (openPreimage T O), ?_⟩,
      hasNormalCrossings_preimage (pullsBackCoordinates_val (openPreimage T O)) h.2.2⟩
    rw [← preimage_biUnion_list]
    exact preimage_mono h.2.1.2

/-- Literal open restriction of an entire smooth boundary history. -/
theorem smoothTower_restrict {n : ℕ} {X Y : CMfd.{u} n} {W : Set X} {E : List (Set X)}
    (T : BlowupTower X Y) (hT : SmoothBoundaryTower W E T) (O : Opens X) :
    SmoothBoundaryTower ((Subtype.val : O → X) ⁻¹' W) (E.map ((Subtype.val : O → X) ⁻¹' ·)) (restrict O T) := by
  let M := geometricTemplate (univ : Set X) E
  let N := geometricTemplate (univ : Set (CMfd.of (n := n) O)) (E.map ((Subtype.val : O → X) ⁻¹' ·))
  have hs := smoothBoundaryStages_restrict W E O T hT.stages
  have hOver := centresOver_restrict O (W ∩ ⋃ H ∈ E, H) T hT.footprint
  rw [preimage_inter, preimage_biUnion_list] at hOver
  have hA := strictTransform_restricted_tower O T W
  have hE : (geoTransformAlong N (restrict O T)).E =
      (geoTransformAlong M T).E.map ((Subtype.val : openPreimage T O → Y) ⁻¹' ·) :=
    restrict_template_boundary E O T
  exact ⟨bm_stage_test _ _ _ (smoothBoundaryStages_bmStages hs), hOver, hs,
    hA.symm ▸ BlowupRestrictOpen.isClosedSubmanifold_preimage_val hT.smooth (openPreimage T O),
    hE.symm ▸ isSNCDivisor_map_preimage (pullsBackCoordinates_val (openPreimage T O)) continuous_subtype_val hT.snc,
    hA.symm ▸ hE.symm ▸ hasNormalCrossings_preimage (pullsBackCoordinates_val (openPreimage T O)) hT.nc⟩

private theorem stages_rebase {n : ℕ} {X X' : CMfd.{u} n}
    (e : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ X) (W : Set X) (hW : IsClosed W)
    (E : List (Set X)) (hE : IsSNCDivisor n E) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), SmoothBoundaryStages W E T →
      SmoothBoundaryStages (e ⁻¹' W) (E.map (e ⁻¹' ·)) (transport e T).tower
  | _, .refl, _ => trivial
  | _, .step T C π hπ, h => by
    let R := transport e T
    let N := geometricTemplate (univ : Set X') (E.map (e ⁻¹' ·))
    have hA := strictTransform_preimage_of_square e R.back R.tower.contMDiff_proj T.contMDiff_proj W hW
      (fun z => (proj_transport e T z).symm)
    have hE' := rebase_bm_boundary_eq e W E hE T (smoothBoundaryStages_bmStages h.1)
    refine ⟨stages_rebase e W hW E hE T h.1, ?_⟩
    change (IsClosedSubmanifold n (strictTransform n R.tower.proj (e ⁻¹' W)) ∧
      R.back ⁻¹' C ⊆ strictTransform n R.tower.proj (e ⁻¹' W) ∩ ⋃ H ∈ (geoTransformAlong N R.tower).E, H) ∧
      HasNormalCrossings n (R.back ⁻¹' C) (geoTransformAlong N R.tower).E
    rw [hA, hE']
    refine ⟨⟨(isClosedSubmanifold_preimage_iff R.back).mpr h.2.1.1, ?_⟩,
      hasNormalCrossings_preimage (pullsBackCoordinates R.back) h.2.2⟩
    rw [← preimage_biUnion_list]
    exact preimage_mono h.2.1.2

/-- Actual rebasing retains the stronger smooth position and the full boundary. -/
theorem smoothTower_rebase {n : ℕ} {X X' Y : CMfd.{u} n}
    (e : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ X) {W : Set X} (hW : IsClosed W)
    {E : List (Set X)} (hE : IsSNCDivisor n E) (T : BlowupTower X Y)
    (hT : SmoothBoundaryTower W E T) :
    SmoothBoundaryTower (e ⁻¹' W) (E.map (e ⁻¹' ·)) (transport e T).tower := by
  let R := transport e T
  have hs := stages_rebase e W hW E hE T hT.stages
  have hOver := centresOver_of_isTowerIso (transport_isTowerIso e T) (W ∩ ⋃ H ∈ E, H) hT.footprint
  rw [preimage_inter, preimage_biUnion_list] at hOver
  have hA := strictTransform_preimage_of_square e R.back R.tower.contMDiff_proj T.contMDiff_proj W hW
    (fun z => (proj_transport e T z).symm)
  have hE' := rebase_bm_boundary_eq e W E hE T (smoothBoundaryStages_bmStages hT.stages)
  exact ⟨bm_stage_test _ _ _ (smoothBoundaryStages_bmStages hs), hOver, hs,
    hA.symm ▸ (isClosedSubmanifold_preimage_iff R.back).mpr hT.smooth,
    hE'.symm ▸ isSNCDivisor_map_preimage (pullsBackCoordinates R.back) R.back.continuous hT.snc,
    hA.symm ▸ hE'.symm ▸ hasNormalCrossings_preimage (pullsBackCoordinates R.back) hT.nc⟩

/-- Join a smooth phase that has reached a partial endpoint to a terminal
smooth phase on its actual strict carrier with its full boundary. -/
theorem smoothTower_append_of_terminal {n : ℕ} {X Y Z : CMfd.{u} n} {W : Set X} (hW : IsClosed W)
    {E : List (Set X)} (hE : IsSNCDivisor n E) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOver : CentresOver (W ∩ ⋃ H ∈ E, H) T) (hStage : SmoothBoundaryStages W E T)
    (S : BlowupTower Y Z) (hS : SmoothBoundaryTower (strictTransform n T.proj W)
      (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E S) :
    SmoothBoundaryTower W E (T.append S) := by
  let M := geometricTemplate (univ : Set X) E
  let N := geometricTemplate (univ : Set Y) (geoTransformAlong M T).E
  let F := W ∩ ⋃ H ∈ E, H
  have hTemp : geoTransformAlong M T = N := by rw [template_current, strict_univ]
  have hTest : IsGeoTestTower M (T.append S) := by
    apply (isGeoTestTower_append_iff M T S).mpr
    exact ⟨hT, hTemp.symm ▸ hS.test⟩
  have hSourceFoot : strictTransform n T.proj W ∩ ⋃ H ∈ (geoTransformAlong M T).E, H ⊆ T.proj ⁻¹' F := by
    intro y hy
    have hyW := strictTransform_subset_preimage T.contMDiff_proj.continuous hW hy.1
    have hAdm := isAdmissibleBlowupSequence_proj M F T hT hOver
    have hyE := IsAdmissibleBlowupSequence.biUnion_subset hAdm hE.1 hy.2
    exact ⟨hyW, hyE.elim id fun h => h.2⟩
  have hOver' := (centresOver_append_iff F T S).mpr
    ⟨hOver, centresOver_mono_local hSourceFoot S hS.footprint⟩
  have hA : strictTransform n (T.append S).proj W = strictTransform n S.proj (strictTransform n T.proj W) := by
    rw [BlowupTower.proj_append, StrictTransformComposition.strictTransform_comp T.contMDiff_proj S.contMDiff_proj]
  have hB : (geoTransformAlong M (T.append S)).E = (geoTransformAlong N S).E := by
    rw [geoTransformAlong_append, hTemp]
  exact ⟨hTest, hOver', smoothBoundaryStages_append W E T hStage S hS.stages,
    hA.symm ▸ hS.smooth, hB.symm ▸ hS.snc, hA.symm ▸ hB.symm ▸ hS.nc⟩

end Hironaka.HironakaG8SmoothBoundaryTowerTransport
