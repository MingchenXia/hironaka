import Hironaka.Analytic.Unibranch.OriginalNativeGlobalSmoothAtlasSites
import Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentSmoothContext
import Hironaka.Analytic.Unibranch.OriginalNativePrescribedHistoryRefinement
import Hironaka.Analytic.Unibranch.OriginalNativeHSSmoothOuterRunComparison

/-! Actual site-only smooth lifts for the computed resolution atlas.
Blueprint: original-native-global-smooth-site-lift.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeGlobalSmoothSiteLift
noncomputable section
open SourceReducedComplexSpace OriginalNativeGlobalSmoothAtlasSites
  OriginalNativeSmoothLocalProduct OriginalNativeSmoothComposition OriginalNativeSmoothOpenLocality

variable {X Y : SourceReducedComplexSpace} (f : X ⟶ Y)

private abbrev SiteContext (s : Site f) :=
  OriginalNativeHSCurrentSmoothContext.Context f s.targetEmbedding s.rank s.productOpen s.chart
    s.chart_open s.chart_square (OriginalNativeHSResolutionAtlasChoice.initialState s.sourceIndex)
      (OriginalNativeHSResolutionAtlasChoice.initialState s.targetIndex)

variable (s : Site f) (c : SiteContext f s)
local notation "S" => OriginalNativeHSResolutionAtlasChoice.initialState s.sourceIndex
local notation "T" => OriginalNativeHSResolutionAtlasChoice.initialState s.targetIndex

private theorem source_le : OriginalNativeHSResolutionAtlasChoice.openSet s.sourceIndex ≤ c.sourceOpen :=
  fun _ hx => c.sourceContains (OriginalNativeHSResolutionAtlasChoice.open_subset_compact s.sourceIndex hx)
private theorem target_le : OriginalNativeHSResolutionAtlasChoice.openSet s.targetIndex ≤ c.targetOpen :=
  fun _ hx => c.targetContains (OriginalNativeHSResolutionAtlasChoice.open_subset_compact s.targetIndex hx)

private abbrev sourceEndpoint := OriginalNativeHSCurrentOverlap.endpoint (S)
  c.sourceOpen c.sourceCompactClosure c.sourceRange
private abbrev targetEndpoint := OriginalNativeHSCurrentOverlap.endpoint (T)
  c.targetOpen c.targetCompactClosure c.targetRange

private def sourceRefinement : OriginalNativeHSResolutionAtlasChoice.source s.sourceIndex ⟶ sourceEndpoint f s c :=
  OriginalNativePrescribedHistoryRefinement.sourceMap (S).inclusion (S).inclusion_isOpenImmersion
    c.sourceOpen c.sourceCompactClosure c.sourceRange (S).history
    (OriginalNativeHSResolutionAtlasChoice.openSet s.sourceIndex)
    (OriginalNativeHSResolutionAtlasChoice.compact_isCompact s.sourceIndex) (source_le f s c)

private def targetRefinement : OriginalNativeHSResolutionAtlasChoice.source s.targetIndex ⟶ targetEndpoint f s c :=
  OriginalNativePrescribedHistoryRefinement.sourceMap (T).inclusion (T).inclusion_isOpenImmersion
    c.targetOpen c.targetCompactClosure c.targetRange (T).history
    (OriginalNativeHSResolutionAtlasChoice.openSet s.targetIndex)
    (OriginalNativeHSResolutionAtlasChoice.compact_isCompact s.targetIndex) (target_le f s c)

private theorem sourceRefinement_open : LocallyRingedSpace.IsOpenImmersion (sourceRefinement f s c).hom.left :=
  OriginalNativePrescribedHistoryRefinement.sourceMap_isOpenImmersion (S).inclusion (S).inclusion_isOpenImmersion
    c.sourceOpen c.sourceCompactClosure c.sourceRange (S).history
    (OriginalNativeHSResolutionAtlasChoice.openSet s.sourceIndex)
    (OriginalNativeHSResolutionAtlasChoice.compact_isCompact s.sourceIndex) (source_le f s c)
private theorem targetRefinement_open : LocallyRingedSpace.IsOpenImmersion (targetRefinement f s c).hom.left :=
  OriginalNativePrescribedHistoryRefinement.sourceMap_isOpenImmersion (T).inclusion (T).inclusion_isOpenImmersion
    c.targetOpen c.targetCompactClosure c.targetRange (T).history
    (OriginalNativeHSResolutionAtlasChoice.openSet s.targetIndex)
    (OriginalNativeHSResolutionAtlasChoice.compact_isCompact s.targetIndex) (target_le f s c)

private theorem sourceRefinement_square : sourceRefinement f s c ≫ c.sourceHistory.projection ≫ c.sourceBaseInclusion =
    OriginalNativeHSResolutionAtlasChoice.projection s.sourceIndex ≫
      OriginalNativeHSResolutionAtlasChoice.baseInclusion s.sourceIndex := by
  have h := OriginalNativePrescribedHistoryRefinement.sourceMap_projection (S).inclusion (S).inclusion_isOpenImmersion
    c.sourceOpen c.sourceCompactClosure c.sourceRange (S).history
    (OriginalNativeHSResolutionAtlasChoice.openSet s.sourceIndex)
    (OriginalNativeHSResolutionAtlasChoice.compact_isCompact s.sourceIndex) (source_le f s c)
  have ht := OriginalNativePrescribedHistoryRefinement.targetMap_square c.sourceOpen c.sourceCompactClosure
    (OriginalNativeHSResolutionAtlasChoice.openSet s.sourceIndex)
    (OriginalNativeHSResolutionAtlasChoice.compact_isCompact s.sourceIndex) (source_le f s c)
  have h' : sourceRefinement f s c ≫ c.sourceHistory.projection =
      OriginalNativeHSResolutionAtlasChoice.projection s.sourceIndex ≫
        OriginalNativePrescribedHistoryRefinement.targetMap c.sourceOpen c.sourceCompactClosure
          (OriginalNativeHSResolutionAtlasChoice.openSet s.sourceIndex)
          (OriginalNativeHSResolutionAtlasChoice.compact_isCompact s.sourceIndex) (source_le f s c) := h
  have ht' : OriginalNativePrescribedHistoryRefinement.targetMap c.sourceOpen c.sourceCompactClosure
      (OriginalNativeHSResolutionAtlasChoice.openSet s.sourceIndex)
      (OriginalNativeHSResolutionAtlasChoice.compact_isCompact s.sourceIndex) (source_le f s c) ≫
      c.sourceBaseInclusion = OriginalNativeHSResolutionAtlasChoice.baseInclusion s.sourceIndex := ht
  calc
    _ = (sourceRefinement f s c ≫ c.sourceHistory.projection) ≫ c.sourceBaseInclusion :=
      (Category.assoc _ _ _).symm
    _ = (OriginalNativeHSResolutionAtlasChoice.projection s.sourceIndex ≫
        OriginalNativePrescribedHistoryRefinement.targetMap c.sourceOpen c.sourceCompactClosure
          (OriginalNativeHSResolutionAtlasChoice.openSet s.sourceIndex)
          (OriginalNativeHSResolutionAtlasChoice.compact_isCompact s.sourceIndex) (source_le f s c)) ≫
        c.sourceBaseInclusion := congrArg (fun a => a ≫ c.sourceBaseInclusion) h'
    _ = OriginalNativeHSResolutionAtlasChoice.projection s.sourceIndex ≫
        (OriginalNativePrescribedHistoryRefinement.targetMap c.sourceOpen c.sourceCompactClosure
          (OriginalNativeHSResolutionAtlasChoice.openSet s.sourceIndex)
          (OriginalNativeHSResolutionAtlasChoice.compact_isCompact s.sourceIndex) (source_le f s c) ≫
          c.sourceBaseInclusion) := Category.assoc _ _ _
    _ = _ := congrArg (fun a => OriginalNativeHSResolutionAtlasChoice.projection s.sourceIndex ≫ a) ht'

private theorem targetRefinement_square : targetRefinement f s c ≫ c.targetHistory.projection ≫ c.targetBaseInclusion =
    OriginalNativeHSResolutionAtlasChoice.projection s.targetIndex ≫
      OriginalNativeHSResolutionAtlasChoice.baseInclusion s.targetIndex := by
  have h := OriginalNativePrescribedHistoryRefinement.sourceMap_projection (T).inclusion (T).inclusion_isOpenImmersion
    c.targetOpen c.targetCompactClosure c.targetRange (T).history
    (OriginalNativeHSResolutionAtlasChoice.openSet s.targetIndex)
    (OriginalNativeHSResolutionAtlasChoice.compact_isCompact s.targetIndex) (target_le f s c)
  have ht := OriginalNativePrescribedHistoryRefinement.targetMap_square c.targetOpen c.targetCompactClosure
    (OriginalNativeHSResolutionAtlasChoice.openSet s.targetIndex)
    (OriginalNativeHSResolutionAtlasChoice.compact_isCompact s.targetIndex) (target_le f s c)
  have h' : targetRefinement f s c ≫ c.targetHistory.projection =
      OriginalNativeHSResolutionAtlasChoice.projection s.targetIndex ≫
        OriginalNativePrescribedHistoryRefinement.targetMap c.targetOpen c.targetCompactClosure
          (OriginalNativeHSResolutionAtlasChoice.openSet s.targetIndex)
          (OriginalNativeHSResolutionAtlasChoice.compact_isCompact s.targetIndex) (target_le f s c) := h
  have ht' : OriginalNativePrescribedHistoryRefinement.targetMap c.targetOpen c.targetCompactClosure
      (OriginalNativeHSResolutionAtlasChoice.openSet s.targetIndex)
      (OriginalNativeHSResolutionAtlasChoice.compact_isCompact s.targetIndex) (target_le f s c) ≫
      c.targetBaseInclusion = OriginalNativeHSResolutionAtlasChoice.baseInclusion s.targetIndex := ht
  calc
    _ = (targetRefinement f s c ≫ c.targetHistory.projection) ≫ c.targetBaseInclusion :=
      (Category.assoc _ _ _).symm
    _ = (OriginalNativeHSResolutionAtlasChoice.projection s.targetIndex ≫
        OriginalNativePrescribedHistoryRefinement.targetMap c.targetOpen c.targetCompactClosure
          (OriginalNativeHSResolutionAtlasChoice.openSet s.targetIndex)
          (OriginalNativeHSResolutionAtlasChoice.compact_isCompact s.targetIndex) (target_le f s c)) ≫
        c.targetBaseInclusion := congrArg (fun a => a ≫ c.targetBaseInclusion) h'
    _ = OriginalNativeHSResolutionAtlasChoice.projection s.targetIndex ≫
        (OriginalNativePrescribedHistoryRefinement.targetMap c.targetOpen c.targetCompactClosure
          (OriginalNativeHSResolutionAtlasChoice.openSet s.targetIndex)
          (OriginalNativeHSResolutionAtlasChoice.compact_isCompact s.targetIndex) (target_le f s c) ≫
          c.targetBaseInclusion) := Category.assoc _ _ _
    _ = _ := congrArg (fun a => OriginalNativeHSResolutionAtlasChoice.projection s.targetIndex ≫ a) ht'

private theorem targetRefinement_range : range (targetRefinement f s c).hom.left.base =
    (c.targetHistory.projection ≫ c.targetBaseInclusion).hom.left.base ⁻¹'
      (OriginalNativeHSResolutionAtlasChoice.openSet s.targetIndex : Set Y.obj.left) :=
  OriginalNativePrescribedHistoryRefinement.sourceMap_range (T).inclusion (T).inclusion_isOpenImmersion
    c.targetOpen c.targetCompactClosure c.targetRange (T).history
    (OriginalNativeHSResolutionAtlasChoice.openSet s.targetIndex)
    (OriginalNativeHSResolutionAtlasChoice.compact_isCompact s.targetIndex) (target_le f s c)

private theorem mapped_original_square : (sourceRefinement f s c ≫ c.map) ≫
    c.targetHistory.projection ≫ c.targetBaseInclusion =
      OriginalNativeHSResolutionAtlasChoice.projection s.sourceIndex ≫
        OriginalNativeHSResolutionAtlasChoice.baseInclusion s.sourceIndex ≫ f := by
  calc
    _ = sourceRefinement f s c ≫ (c.map ≫ c.targetHistory.projection ≫ c.targetBaseInclusion) := by
      simp only [Category.assoc]
    _ = sourceRefinement f s c ≫ (c.sourceHistory.projection ≫ c.sourceBaseInclusion ≫ f) :=
      congrArg (fun a => sourceRefinement f s c ≫ a) c.square
    _ = (sourceRefinement f s c ≫ c.sourceHistory.projection ≫ c.sourceBaseInclusion) ≫ f := by
      simp only [Category.assoc]
    _ = _ := by rw [sourceRefinement_square]; exact Category.assoc _ _ _

private theorem mapped_range : range (sourceRefinement f s c ≫ c.map).hom.left.base ⊆
    range (targetRefinement f s c).hom.left.base := by
  rw [targetRefinement_range]
  rintro _ ⟨z,rfl⟩
  have hs := congrArg (fun a => a.hom.left.base z) (mapped_original_square f s c)
  have hp := OriginalNativeHSResolutionAtlasChoice.projection_mem_open s.sourceIndex z
  have hi : (OriginalNativeHSResolutionAtlasChoice.projection s.sourceIndex ≫
      OriginalNativeHSResolutionAtlasChoice.baseInclusion s.sourceIndex ≫ f).hom.left.base z ∈
        OriginalNativeHSResolutionAtlasChoice.openSet s.targetIndex :=
    s.image_closure ⟨_,OriginalNativeHSResolutionAtlasChoice.open_subset_compact s.sourceIndex hp,rfl⟩
  have hm : ((sourceRefinement f s c ≫ c.map) ≫ c.targetHistory.projection ≫ c.targetBaseInclusion).hom.left.base z ∈
      OriginalNativeHSResolutionAtlasChoice.openSet s.targetIndex := hs.symm ▸ hi
  exact hm

private def restrictedMap : OriginalNativeHSResolutionAtlasChoice.source s.sourceIndex ⟶
    OriginalNativeHSResolutionAtlasChoice.source s.targetIndex := by
  let : LocallyRingedSpace.IsOpenImmersion (targetRefinement f s c).hom.left := targetRefinement_open f s c
  let g := LocallyRingedSpace.IsOpenImmersion.lift (targetRefinement f s c).hom.left
    (sourceRefinement f s c ≫ c.map).hom.left (mapped_range f s c)
  have hfac : g ≫ (targetRefinement f s c).hom.left = (sourceRefinement f s c ≫ c.map).hom.left :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _
  have hover : g ≫ (OriginalNativeHSResolutionAtlasChoice.source s.targetIndex).obj.hom =
      (OriginalNativeHSResolutionAtlasChoice.source s.sourceIndex).obj.hom := by
    calc
      _ = g ≫ ((targetRefinement f s c).hom.left ≫ (targetEndpoint f s c).obj.hom) :=
        congrArg (fun a => g ≫ a) (Over.w (targetRefinement f s c).hom).symm
      _ = (g ≫ (targetRefinement f s c).hom.left) ≫ (targetEndpoint f s c).obj.hom := (Category.assoc _ _ _).symm
      _ = (sourceRefinement f s c ≫ c.map).hom.left ≫ (targetEndpoint f s c).obj.hom :=
        congrArg (fun a => a ≫ (targetEndpoint f s c).obj.hom) hfac
      _ = _ := Over.w (sourceRefinement f s c ≫ c.map).hom
  exact ObjectProperty.homMk (Over.homMk g hover)

private theorem restrictedMap_factorization : restrictedMap f s c ≫ targetRefinement f s c =
    sourceRefinement f s c ≫ c.map := by
  let : LocallyRingedSpace.IsOpenImmersion (targetRefinement f s c).hom.left := targetRefinement_open f s c
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ (mapped_range f s c)

private theorem restrictedMap_smooth : IsSmoothMorphism (restrictedMap f s c) := by
  apply isSmoothMorphism_of_postcomp_openImmersion (restrictedMap f s c) (targetRefinement f s c)
    (targetRefinement_open f s c)
  rw [restrictedMap_factorization]
  exact isSmoothMorphism_comp (sourceRefinement f s c) c.map
    (isSmoothMorphism_of_isOpenImmersion _ (sourceRefinement_open f s c)) c.smooth

private theorem restrictedMap_original_square : restrictedMap f s c ≫
    OriginalNativeHSResolutionAtlasChoice.projection s.targetIndex ≫
      OriginalNativeHSResolutionAtlasChoice.baseInclusion s.targetIndex =
      OriginalNativeHSResolutionAtlasChoice.projection s.sourceIndex ≫
        OriginalNativeHSResolutionAtlasChoice.baseInclusion s.sourceIndex ≫ f := by
  calc
    _ = restrictedMap f s c ≫ (targetRefinement f s c ≫ c.targetHistory.projection ≫ c.targetBaseInclusion) :=
      congrArg (fun a => restrictedMap f s c ≫ a) (targetRefinement_square f s c).symm
    _ = (restrictedMap f s c ≫ targetRefinement f s c) ≫ c.targetHistory.projection ≫ c.targetBaseInclusion := by
      simp only [Category.assoc]
    _ = (sourceRefinement f s c ≫ c.map) ≫ c.targetHistory.projection ≫ c.targetBaseInclusion := by
      rw [restrictedMap_factorization]
    _ = _ := mapped_original_square f s c

/-- The comparison of the actual saved construction runs at this site. -/
private def computedContext : SiteContext f s :=
  Classical.choice (OriginalNativeHSSmoothOuterRunComparison.exists_near_compact_context
    f s.targetEmbedding s.rank s.productOpen s.chart s.chart_open s.chart_square
    (OriginalNativeHSResolutionAtlasChoice.compact s.sourceIndex)
    (OriginalNativeHSResolutionAtlasChoice.compact s.targetIndex)
    (OriginalNativeHSResolutionAtlasChoice.compact_isCompact s.sourceIndex)
    (OriginalNativeHSResolutionAtlasChoice.compact_isCompact s.targetIndex)
    s.closure_in_chart (compact_image f s))

/-- The actual local map between the saved resolution atlas recipes. -/
def map : OriginalNativeHSResolutionAtlasChoice.source s.sourceIndex ⟶
    OriginalNativeHSResolutionAtlasChoice.source s.targetIndex :=
  restrictedMap f s (computedContext f s)

theorem map_smooth : IsSmoothMorphism (map f s) :=
  restrictedMap_smooth f s (computedContext f s)

theorem original_square : map f s ≫
    OriginalNativeHSResolutionAtlasChoice.projection s.targetIndex ≫
      OriginalNativeHSResolutionAtlasChoice.baseInclusion s.targetIndex =
      OriginalNativeHSResolutionAtlasChoice.projection s.sourceIndex ≫
        OriginalNativeHSResolutionAtlasChoice.baseInclusion s.sourceIndex ≫ f :=
  restrictedMap_original_square f s (computedContext f s)

theorem scalar : (map f s).hom.left ≫
    (OriginalNativeHSResolutionAtlasChoice.source s.targetIndex).obj.hom =
      (OriginalNativeHSResolutionAtlasChoice.source s.sourceIndex).obj.hom :=
  Over.w (map f s).hom

end
end Hironaka.Analytic.Unibranch.OriginalNativeGlobalSmoothSiteLift
