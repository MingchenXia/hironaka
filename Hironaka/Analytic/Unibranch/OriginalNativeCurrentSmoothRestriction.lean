import Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentSmoothContext
import Hironaka.Analytic.Unibranch.OriginalNativePrescribedHistoryRefinement
import Hironaka.Analytic.Unibranch.OriginalNativeSmoothOpenLocality

/-! Restriction of the real current smooth context to smaller original opens. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeCurrentSmoothRestriction
noncomputable section
open SourceReducedComplexSpace OriginalNativeHSShadowOuterState OriginalNativeProductWindow
  OriginalNativeSmoothLocalProduct OriginalNativeSmoothComposition OriginalNativeSmoothOpenLocality
  OriginalNativeHSCurrentSmoothContext

variable {X Y : SourceReducedComplexSpace} {f : X ⟶ Y} {e0 : LocalEmbedding Y} {r : ℕ}
  {O : Opens (productAmbient e0 r)} {a : windowSpace e0 r O ⟶ X}
  {ha : LocallyRingedSpace.IsOpenImmersion a.hom.left} {hChart : a ≫ f = windowFirst e0 r O}
  {KS : Set X.obj.left} {KT : Set Y.obj.left} {S : State X KS} {T : State Y KT}
  (c : Context f e0 r O a ha hChart S T)
  (US : Opens X.obj.left) (UT : Opens Y.obj.left)
  (hUS : IsCompact (closure (US : Set X.obj.left))) (hUT : IsCompact (closure (UT : Set Y.obj.left)))
  (hCS : KS ⊆ US) (hCT : KT ⊆ UT)
  (hCloseS : closure (US : Set X.obj.left) ⊆ c.sourceOpen)
  (hCloseT : closure (UT : Set Y.obj.left) ⊆ c.targetOpen)
  (hImage : f.hom.left.base '' closure (US : Set X.obj.left) ⊆ (UT : Set Y.obj.left))

/-- The same current histories and map restrict to the indicated original opens. -/
def restrictContext : Context f e0 r O a ha hChart S T := by
  let hSRange : closure (US : Set X.obj.left) ⊆ range S.inclusion.hom.left.base :=
    fun _ hx => c.sourceRange (subset_closure (hCloseS hx))
  let hTRange : closure (UT : Set Y.obj.left) ⊆ range T.inclusion.hom.left.base :=
    fun _ hy => c.targetRange (subset_closure (hCloseT hy))
  let hSSub : US ≤ c.sourceOpen := fun _ hx => hCloseS (subset_closure hx)
  let hTSub : UT ≤ c.targetOpen := fun _ hx => hCloseT (subset_closure hx)
  let src := OriginalNativePrescribedHistoryRefinement.sourceMap S.inclusion S.inclusion_isOpenImmersion
    c.sourceOpen c.sourceCompactClosure c.sourceRange S.history US hUS hSSub
  let tgt := OriginalNativePrescribedHistoryRefinement.sourceMap T.inclusion T.inclusion_isOpenImmersion
    c.targetOpen c.targetCompactClosure c.targetRange T.history UT hUT hTSub
  have hSrcOpen : LocallyRingedSpace.IsOpenImmersion src.hom.left :=
    OriginalNativePrescribedHistoryRefinement.sourceMap_isOpenImmersion _ _ _ _ _ _ _ _ _
  have hTgtOpen : LocallyRingedSpace.IsOpenImmersion tgt.hom.left :=
    OriginalNativePrescribedHistoryRefinement.sourceMap_isOpenImmersion _ _ _ _ _ _ _ _ _
  have hSrcOriginal : src ≫ c.sourceHistory.projection ≫ c.sourceBaseInclusion =
      (OriginalNativeHSCurrentOverlap.history S US hUS hSRange).projection ≫
        OriginalRelativelyCompactRestriction.inclusion X US hUS := by
    have hi := OriginalNativePrescribedHistoryRefinement.sourceMap_inclusion S.inclusion S.inclusion_isOpenImmersion
      c.sourceOpen c.sourceCompactClosure c.sourceRange S.history US hUS hSSub
    have hn := OriginalNativePrescribedOpenHistory.projection_square S.inclusion S.inclusion_isOpenImmersion
      US hUS hSRange S.history
    apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
    intro z
    have hs := congrArg (fun p => p.hom.left.base (src.hom.left.base z)) c.source_square
    have hI := congrArg (fun p => p.hom.left.base z) hi
    have hN := congrArg (fun p => p.hom.left.base z) hn
    exact hs.trans ((congrArg (fun y => S.inclusion.hom.left.base (S.history.projection.hom.left.base y)) hI).trans hN.symm)
  have hTgtOriginal : tgt ≫ c.targetHistory.projection ≫ c.targetBaseInclusion =
      (OriginalNativeHSCurrentOverlap.history T UT hUT hTRange).projection ≫
        OriginalRelativelyCompactRestriction.inclusion Y UT hUT := by
    have hi := OriginalNativePrescribedHistoryRefinement.sourceMap_inclusion T.inclusion T.inclusion_isOpenImmersion
      c.targetOpen c.targetCompactClosure c.targetRange T.history UT hUT hTSub
    have hn := OriginalNativePrescribedOpenHistory.projection_square T.inclusion T.inclusion_isOpenImmersion
      UT hUT hTRange T.history
    apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
    intro z
    have hs := congrArg (fun p => p.hom.left.base (tgt.hom.left.base z)) c.target_square
    have hI := congrArg (fun p => p.hom.left.base z) hi
    have hN := congrArg (fun p => p.hom.left.base z) hn
    exact hs.trans ((congrArg (fun y => T.inclusion.hom.left.base (T.history.projection.hom.left.base y)) hI).trans hN.symm)
  have hRange : range (src ≫ c.map).hom.left.base ⊆ range tgt.hom.left.base := by
    rintro _ ⟨z,rfl⟩
    have htgt : range tgt.hom.left.base =
        (c.targetHistory.projection ≫ c.targetBaseInclusion).hom.left.base ⁻¹' (UT : Set Y.obj.left) :=
      OriginalNativePrescribedHistoryRefinement.sourceMap_range T.inclusion T.inclusion_isOpenImmersion
        c.targetOpen c.targetCompactClosure c.targetRange T.history UT hUT hTSub
    change c.map.hom.left.base (src.hom.left.base z) ∈ range tgt.hom.left.base
    rw [htgt]
    have hs := congrArg (fun p => p.hom.left.base z) hSrcOriginal
    have ht := congrArg (fun p => p.hom.left.base (src.hom.left.base z)) c.square
    have hz : (OriginalRelativelyCompactRestriction.inclusion X US hUS).hom.left.base
        ((OriginalNativeHSCurrentOverlap.history S US hUS hSRange).projection.hom.left.base z) ∈ US :=
      ((OriginalNativeHSCurrentOverlap.history S US hUS hSRange).projection.hom.left.base z).property
    have hf := hImage ⟨_,subset_closure hz,rfl⟩
    exact (congrArg (fun y : Y.obj.left => y ∈ UT) ht).mpr
      ((congrArg (fun x : X.obj.left => f.hom.left.base x ∈ UT) hs).mpr hf)
  let : LocallyRingedSpace.IsOpenImmersion tgt.hom.left := hTgtOpen
  let l := LocallyRingedSpace.IsOpenImmersion.lift tgt.hom.left (src ≫ c.map).hom.left hRange
  have hfac : l ≫ tgt.hom.left = (src ≫ c.map).hom.left :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _
  let q : (OriginalNativeHSCurrentOverlap.endpoint S US hUS hSRange) ⟶
      (OriginalNativeHSCurrentOverlap.endpoint T UT hUT hTRange) := by
    refine ObjectProperty.homMk (Over.homMk l ?_)
    exact (congrArg (fun p => l ≫ p) (Over.w tgt.hom).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun p => p ≫ (OriginalNativeHSCurrentOverlap.endpoint T c.targetOpen
          c.targetCompactClosure c.targetRange).obj.hom) hfac).trans (Over.w (src ≫ c.map).hom)))
  have hq : q ≫ tgt = src ≫ c.map := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hfac
  have hqSmooth : IsSmoothMorphism q :=
    isSmoothMorphism_of_postcomp_openImmersion _ tgt hTgtOpen
      ((congrArg IsSmoothMorphism hq).mpr
        (isSmoothMorphism_comp _ _ (isSmoothMorphism_of_isOpenImmersion _ hSrcOpen) c.smooth))
  have hqOriginal : q ≫ (OriginalNativeHSCurrentOverlap.history T UT hUT hTRange).projection ≫
      OriginalRelativelyCompactRestriction.inclusion Y UT hUT =
      (OriginalNativeHSCurrentOverlap.history S US hUS hSRange).projection ≫
        OriginalRelativelyCompactRestriction.inclusion X US hUS ≫ f := by
    apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
    intro z
    have hl := congrArg (fun p => p.hom.left.base z) hq
    have ht := congrArg (fun p => p.hom.left.base (q.hom.left.base z)) hTgtOriginal
    have hs := congrArg (fun p => p.hom.left.base z) hSrcOriginal
    have hc := congrArg (fun p => p.hom.left.base (src.hom.left.base z)) c.square
    exact ht.symm.trans ((congrArg (fun y => c.targetBaseInclusion.hom.left.base
      (c.targetHistory.projection.hom.left.base y)) hl).trans (hc.trans (congrArg f.hom.left.base hs)))
  exact {
    compactImage := c.compactImage
    sourceOpen := US
    sourceCompactClosure := hUS
    sourceContains := hCS
    sourceRange := hSRange
    sourceChartRange := fun _ hx => c.sourceChartRange (subset_closure (hCloseS hx))
    targetOpen := UT
    targetCompactClosure := hUT
    targetContains := hCT
    targetRange := hTRange
    imageClosure := hImage
    map := q
    smooth := hqSmooth
    square := hqOriginal }
end
end Hironaka.Analytic.Unibranch.OriginalNativeCurrentSmoothRestriction
