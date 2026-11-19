import Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentSmoothContext
import Hironaka.Analytic.Unibranch.OriginalNativeHSOuterInitialBound

/-! Concrete ACTUAL D39 leading profiles and source-image avoidance from
honest PAST smooth contexts. Full Blueprint FIRST; no future case supplier. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentSmoothLeadingProfiles
noncomputable section
open Hironaka SourceReducedComplexSpace
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaG1NativeFiniteProductState
  HironakaG1NativeFiniteProductHSLex OriginalLocalEmbeddingStalkHS OriginalIntrinsicHSSuperlevels
  OriginalNativeProductWindow OriginalNativeSmoothLocalProduct OriginalNativeSmoothComposition
  OriginalNativeSmoothSingularLocus OriginalNativeHSOuterInitialBound OriginalNativeHSShadowOuterState
  OriginalNativeHSCurrentSmoothContext

private theorem shadowSing_nonempty {Z : SourceReducedComplexSpace} {K : Set Z.obj.left}
    (A : State Z K) (hne : (singularShadow A).Nonempty) :
    (shadow A∩intrinsicSingularLocus A.source.obj).Nonempty := by
  simpa only [singularShadow,inter_comm] using hne

variable {X Y : SourceReducedComplexSpace} {f : X⟶Y} {e0 : LocalEmbedding Y} {r : ℕ}
  {O : Opens (productAmbient e0 r)} {a : windowSpace e0 r O⟶X}
  {ha : LocallyRingedSpace.IsOpenImmersion a.hom.left} {hChart : a≫f=windowFirst e0 r O}
  {KS : Set X.obj.left} {KT : Set Y.obj.left} {S : State X KS} {T : State Y KT}
  (c : Context f e0 r O a ha hChart S T)

include c in
/-- Literal ACTUAL D39 profiles, with all compact lifts/rank laws derived. -/
theorem leading_profile_le (hKS : IsCompact KS) (hKT : IsCompact KT)
    (hneS : (singularShadow S).Nonempty) (hneT : (singularShadow T).Nonempty) :
    toLex (profile S.history (baseShadow S) (baseShadow_compact S hKS) hneS) ≤
      toLex (finiteProductHS r (profile T.history (baseShadow T) (baseShadow_compact T hKT) hneT)) := by
  let MS := OriginalNativeHSShadowPhaseFactory.maximum S.source (shadow S) (shadow_compact S hKS)
    (shadowSing_nonempty S hneS)
  let MT := OriginalNativeHSShadowPhaseFactory.maximum T.source (shadow T) (shadow_compact T hKT)
    (shadowSing_nonempty T hneT)
  have hLift : MS.point∈c.sourceInclusion.hom.left.base '' c.sourceCompact :=
    (Set.ext_iff.mp c.sourceCompact_image MS.point).mpr MS.in_compact
  obtain ⟨z,hz,hPoint⟩ := hLift
  have hSingSource : z∈intrinsicSingularLocus
      (OriginalNativeHSCurrentOverlap.endpoint S c.sourceOpen c.sourceCompactClosure c.sourceRange).obj :=
    (smoothAt_singular_iff c.sourceInclusion z
      (isSmoothMorphism_of_isOpenImmersion _ c.sourceInclusion_isOpenImmersion z)).mpr
        (hPoint.symm ▸ MS.singular)
  have hSingTarget := (smoothAt_singular_iff c.map z (c.smooth z)).mp hSingSource
  have hOldSing := (smoothAt_singular_iff c.targetInclusion (c.map.hom.left.base z)
    (isSmoothMorphism_of_isOpenImmersion _ c.targetInclusion_isOpenImmersion _)).mp hSingTarget
  have hMember : c.targetInclusion.hom.left.base (c.map.hom.left.base z)∈shadow T :=
    (Set.ext_iff.mp c.targetCompact_image _).mp ⟨_,c.compact_image_subset ⟨z,hz,rfl⟩,rfl⟩
  have hBound := MT.maximal _ hMember hOldSing
  have hProfile := c.old_point_profile z
  rw [hPoint] at hProfile
  change toLex (originalStalkHS S.source MS.point)≤toLex (finiteProductHS r (originalStalkHS T.source MT.point))
  rw [hProfile]
  exact (finiteProductHS_lex_le_iff r _ _).mpr hBound

/-- Present one-sided image avoidance on ENTIRE source compact; no assertion
that the whole target fibre is absent. Actual skip maps are constructed later. -/
theorem higher_target_avoids_sourceCompact (hKS : IsCompact KS) (hKT : IsCompact KT)
    (hneS : (singularShadow S).Nonempty) (hneT : (singularShadow T).Nonempty)
    (hlt : toLex (profile S.history (baseShadow S) (baseShadow_compact S hKS) hneS) <
      toLex (finiteProductHS r (profile T.history (baseShadow T) (baseShadow_compact T hKT) hneT))) :
    ∀z∈c.sourceCompact,(c.map≫c.targetInclusion).hom.left.base z∉originalSingularHSThreshold T.source
      (profile T.history (baseShadow T) (baseShadow_compact T hKT) hneT) := by
  intro z hz hThreshold
  let MS := OriginalNativeHSShadowPhaseFactory.maximum S.source (shadow S) (shadow_compact S hKS)
    (shadowSing_nonempty S hneS)
  have hSingTarget := (smoothAt_singular_iff c.targetInclusion (c.map.hom.left.base z)
    (isSmoothMorphism_of_isOpenImmersion _ c.targetInclusion_isOpenImmersion _)).mpr hThreshold.1
  have hSingSource := (smoothAt_singular_iff c.map z (c.smooth z)).mpr hSingTarget
  have hOldSing := (smoothAt_singular_iff c.sourceInclusion z
    (isSmoothMorphism_of_isOpenImmersion _ c.sourceInclusion_isOpenImmersion z)).mp hSingSource
  have hMember : c.sourceInclusion.hom.left.base z∈shadow S :=
    (Set.ext_iff.mp c.sourceCompact_image _).mp ⟨z,hz,rfl⟩
  have hBound := MS.maximal _ hMember hOldSing
  have hLower : toLex (finiteProductHS r
      (profile T.history (baseShadow T) (baseShadow_compact T hKT) hneT))≤
      toLex (originalStalkHS S.source (c.sourceInclusion.hom.left.base z)) := by
    rw [c.old_point_profile z]
    exact (finiteProductHS_lex_le_iff r _ _).mpr (Pi.toLex_monotone hThreshold.2)
  exact (not_le_of_gt hlt) (hLower.trans hBound)

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentSmoothLeadingProfiles
