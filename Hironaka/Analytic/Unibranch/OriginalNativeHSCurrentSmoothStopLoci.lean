import Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentSmoothContext
import Hironaka.Analytic.Unibranch.OriginalNativeSmoothSingularLocus

/-! Actual PAST smooth comparison stop loci. Blueprint FIRST:
original-native-hs-current-smooth-stop-loci.tex. No future phase or
whole-target-fibre absence premise. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentSmoothStopLoci
noncomputable section
open Hironaka SourceReducedComplexSpace
  HironakaIntrinsicComplexAnalyticRegularLocus OriginalNativeHSShadowOuterState
  OriginalNativeProductWindow OriginalNativeSmoothLocalProduct OriginalNativeSmoothComposition
  OriginalNativeSmoothSingularLocus OriginalNativeHSCurrentSmoothContext

variable {X Y : SourceReducedComplexSpace} {f : X ⟶ Y} {e0 : LocalEmbedding Y} {r : ℕ}
  {O : Opens (productAmbient e0 r)} {a : windowSpace e0 r O ⟶ X}
  {ha : LocallyRingedSpace.IsOpenImmersion a.hom.left} {hChart : a ≫ f = windowFirst e0 r O}
  {KS : Set X.obj.left} {KT : Set Y.obj.left} {S : State X KS} {T : State Y KT}
  (c : Context f e0 r O a ha hChart S T)

private theorem targetComposite_smooth : IsSmoothMorphism (c.map ≫ c.targetInclusion) :=
  isSmoothMorphism_comp _ _ c.smooth
    (isSmoothMorphism_of_isOpenImmersion _ c.targetInclusion_isOpenImmersion)

include c in
/-- Genuine target STOP rules out EVERY actual source singular-shadow point. -/
theorem source_stop_of_target_stop (heT : singularShadow T = ∅) : singularShadow S = ∅ := by
  apply Set.eq_empty_of_subset_empty
  rintro y ⟨hySing,hyShadow⟩
  have hy : y ∈ c.sourceInclusion.hom.left.base '' c.sourceCompact := by
    rw [c.sourceCompact_image]
    exact hyShadow
  obtain ⟨z,hz,hzy⟩ := hy
  have hsz := (smoothAt_singular_iff c.sourceInclusion z
    (isSmoothMorphism_of_isOpenImmersion _ c.sourceInclusion_isOpenImmersion z)).mpr (hzy.symm ▸ hySing)
  have htz : (c.map ≫ c.targetInclusion).hom.left.base z ∈ intrinsicSingularLocus T.source.obj :=
    (smoothAt_singular_iff _ z (targetComposite_smooth c z)).mp hsz
  have htC : c.map.hom.left.base z ∈ c.targetCompact := c.compact_image_subset ⟨z,hz,rfl⟩
  have htShadow : c.targetInclusion.hom.left.base (c.map.hom.left.base z) ∈ shadow T := by
    rw [← c.targetCompact_image]
    exact ⟨_,htC,rfl⟩
  have bad : c.targetInclusion.hom.left.base (c.map.hom.left.base z) ∈ singularShadow T := ⟨htz,htShadow⟩
  rw [heT] at bad
  exact bad

include c in
/-- A real source NEXT is incompatible with an actual target STOP. -/
theorem target_not_stopped_of_source_next (hneS : (singularShadow S).Nonempty) : singularShadow T ≠ ∅ := by
  intro heT
  obtain ⟨z,hz⟩ := hneS
  rw [source_stop_of_target_stop c heT] at hz
  exact hz

/-- Only the actual image of the ENTIRE source compact fibre is asserted regular. -/
theorem source_stop_image_regular (heS : singularShadow S = ∅) :
    (c.map ≫ c.targetInclusion).hom.left.base '' c.sourceCompact ⊆ intrinsicRegularLocus T.source.obj := by
  rintro _ ⟨z,hz,rfl⟩
  have hOld : c.sourceInclusion.hom.left.base z ∈ intrinsicRegularLocus S.source.obj := by
    by_contra hn
    have hs : c.sourceInclusion.hom.left.base z ∈ shadow S := by
      rw [← c.sourceCompact_image]
      exact ⟨z,hz,rfl⟩
    have bad : c.sourceInclusion.hom.left.base z ∈ singularShadow S := ⟨hn,hs⟩
    rw [heS] at bad
    exact bad
  have hReg := (smoothAt_regular_iff c.sourceInclusion z
    (isSmoothMorphism_of_isOpenImmersion _ c.sourceInclusion_isOpenImmersion z)).mpr hOld
  exact (smoothAt_regular_iff _ z (targetComposite_smooth c z)).mp hReg

/-- This is the honest one-sided absence consumed by the ACTUAL target skip. -/
theorem source_stop_avoids_threshold (heS : singularShadow S = ∅) (H : ℕ → ℕ)
    (z : (OriginalNativeHSCurrentOverlap.endpoint S c.sourceOpen c.sourceCompactClosure c.sourceRange).obj.left)
    (hz : z ∈ c.sourceCompact) :
    (c.map ≫ c.targetInclusion).hom.left.base z ∉
      OriginalIntrinsicHSSuperlevels.originalSingularHSThreshold T.source H := by
  intro hH
  exact hH.1 (source_stop_image_regular c heS ⟨z,hz,rfl⟩)

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentSmoothStopLoci
