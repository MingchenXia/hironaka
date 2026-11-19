import Hironaka.Analytic.Unibranch.OriginalNativeHSGlobalResolution
import Hironaka.Analytic.Unibranch.OriginalNativeSmoothLocalProduct

/-! Concrete good source/target atlas sites from ordinary GLOBAL smooth f.
The actual resolution-source charts cover all RX, by exact saturation.
No future lift/span/context/cover packet is an input or site field.
Full Blueprint FIRST: original-native-global-smooth-atlas-sites.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeGlobalSmoothAtlasSites
noncomputable section
open SourceReducedComplexSpace OriginalNativeProductWindow OriginalNativeSmoothLocalProduct

variable {X Y : SourceReducedComplexSpace} (f : X ⟶ Y)

/-- Only genuine CURRENT ordinary product geometry and ACTUAL atlas indices. -/
structure Site where
  sourceIndex : OriginalNativeHSResolutionAtlasChoice.Index X
  targetIndex : OriginalNativeHSResolutionAtlasChoice.Index Y
  targetEmbedding : LocalEmbedding Y
  rank : ℕ
  productOpen : Opens (productAmbient targetEmbedding rank)
  chart : windowSpace targetEmbedding rank productOpen ⟶ X
  chart_open : LocallyRingedSpace.IsOpenImmersion chart.hom.left
  chart_square : chart ≫ f = windowFirst targetEmbedding rank productOpen
  closure_in_chart : OriginalNativeHSResolutionAtlasChoice.compact sourceIndex ⊆ range chart.hom.left.base
  image_closure : f.hom.left.base '' OriginalNativeHSResolutionAtlasChoice.compact sourceIndex ⊆
    (OriginalNativeHSResolutionAtlasChoice.openSet targetIndex : Set Y.obj.left)

/-- The actual ordinary smoothness witness and target cover INTERNALLY choose a good site. -/
theorem exists_site (hf : IsSmoothMorphism f) (x : X.obj.left) :
    ∃ s : Site f, x ∈ OriginalNativeHSResolutionAtlasChoice.openSet s.sourceIndex := by
  obtain ⟨j,b,hb⟩ := OriginalNativeHSResolutionAtlasChoice.base_cover Y (f.hom.left.base x)
  have hbmem : (OriginalNativeHSResolutionAtlasChoice.baseInclusion j).hom.left.base b ∈
      OriginalNativeHSResolutionAtlasChoice.openSet j := by
    exact b.property
  have hfx : f.hom.left.base x ∈ OriginalNativeHSResolutionAtlasChoice.openSet j := hb ▸ hbmem
  obtain ⟨e,r,P,W,hWP,a,z,ha,hz,_hsource,_htarget,hsq,_hsub,_hideal⟩ :=
    exists_ambient_representation f x (hf x) ⊤ (OriginalNativeHSResolutionAtlasChoice.openSet j)
      (Set.mem_univ x) hfx
  have hChart : a ≫ f = windowFirst e r W :=
    hsq.trans (nativeProjection_square e r P W hWP)
  let G : Opens X.obj.left :=
    ⟨range a.hom.left.base ∩ f.hom.left.base ⁻¹'
        (OriginalNativeHSResolutionAtlasChoice.openSet j : Set Y.obj.left),
      ha.base_open.isOpen_range.inter
        ((OriginalNativeHSResolutionAtlasChoice.openSet j).isOpen.preimage f.hom.left.base.hom.continuous)⟩
  have hxG : x ∈ G := ⟨⟨z,hz⟩,hfx⟩
  let N := OriginalNativePrecompactNeighbourhood.neighbourhood X {x} isCompact_singleton G
    (singleton_subset_iff.mpr hxG)
  let i : OriginalNativeHSResolutionAtlasChoice.Index X := ⟨N.openSet,N.compactClosure⟩
  have hC : OriginalNativeHSResolutionAtlasChoice.compact i ⊆ range a.hom.left.base := by
    intro y hy
    exact (N.closure_subset hy).1
  have hI : f.hom.left.base '' OriginalNativeHSResolutionAtlasChoice.compact i ⊆
      (OriginalNativeHSResolutionAtlasChoice.openSet j : Set Y.obj.left) := by
    rintro _ ⟨y,hy,rfl⟩
    exact (N.closure_subset hy).2
  refine ⟨⟨i,j,e,r,W,a,ha,hChart,hC,hI⟩,?_⟩
  exact N.contains (mem_singleton x)

def siteAt (hf : IsSmoothMorphism f) (x : X.obj.left) : Site f :=
  (exists_site f hf x).choose

theorem siteAt_contains (hf : IsSmoothMorphism f) (x : X.obj.left) :
    x ∈ OriginalNativeHSResolutionAtlasChoice.openSet (siteAt f hf x).sourceIndex :=
  (exists_site f hf x).choose_spec

theorem compact_image (s : Site f) :
    f.hom.left.base '' OriginalNativeHSResolutionAtlasChoice.compact s.sourceIndex ⊆
      OriginalNativeHSResolutionAtlasChoice.compact s.targetIndex :=
  s.image_closure.trans (OriginalNativeHSResolutionAtlasChoice.open_subset_compact s.targetIndex)

/-- SAME actual original source recipe, indexed by the good site. -/
abbrev sourceChart (s : Site f) : SourceReducedComplexSpace :=
  OriginalNativeHSResolutionAtlasChoice.source s.sourceIndex

def sourceChartInclusion (s : Site f) : sourceChart f s ⟶ OriginalNativeHSGlobalResolution.source X :=
  OriginalNativeHSResolutionProperAtlas.localInclusion X s.sourceIndex

theorem sourceChart_isOpenImmersion (s : Site f) :
    LocallyRingedSpace.IsOpenImmersion (sourceChartInclusion f s).hom.left :=
  OriginalNativeHSResolutionProperAtlas.localInclusion_isOpenImmersion X s.sourceIndex

theorem sourceChart_projection (s : Site f) :
    sourceChartInclusion f s ≫ OriginalNativeHSGlobalResolution.projection X =
      OriginalNativeHSResolutionAtlasChoice.projection s.sourceIndex ≫
        OriginalNativeHSResolutionAtlasChoice.baseInclusion s.sourceIndex :=
  OriginalNativeHSResolutionProperAtlas.localInclusion_projection X s.sourceIndex

theorem sourceChart_scalar (s : Site f) : (sourceChartInclusion f s).hom.left ≫
    (OriginalNativeHSGlobalResolution.source X).obj.hom = (sourceChart f s).obj.hom :=
  Over.w (sourceChartInclusion f s).hom

theorem sourceChart_range (s : Site f) : range (sourceChartInclusion f s).hom.left.base =
    (OriginalNativeHSGlobalResolution.projection X).hom.left.base ⁻¹'
      (OriginalNativeHSResolutionAtlasChoice.openSet s.sourceIndex : Set X.obj.left) :=
  (OriginalNativeHSResolutionProperAtlas.preimage_chart_range X s.sourceIndex).symm

/-- Covers EVERY actual point of RX, not only any compact shadow. -/
theorem sourceChart_cover (hf : IsSmoothMorphism f)
    (y : (OriginalNativeHSGlobalResolution.source X).obj.left) :
    ∃ (s : Site f) (z : (sourceChart f s).obj.left), (sourceChartInclusion f s).hom.left.base z = y := by
  let s := siteAt f hf ((OriginalNativeHSGlobalResolution.projection X).hom.left.base y)
  have hy : y ∈ range (sourceChartInclusion f s).hom.left.base := by
    rw [sourceChart_range]
    exact siteAt_contains f hf ((OriginalNativeHSGlobalResolution.projection X).hom.left.base y)
  obtain ⟨z,hz⟩ := hy
  exact ⟨s,z,hz⟩

private theorem sourceChart_original_mem_open (s : Site f) (z : (sourceChart f s).obj.left) :
    (OriginalNativeHSGlobalResolution.projection X).hom.left.base ((sourceChartInclusion f s).hom.left.base z) ∈
      OriginalNativeHSResolutionAtlasChoice.openSet s.sourceIndex := by
  have h := congrArg (fun a => a.hom.left.base z) (sourceChart_projection f s)
  exact h.symm ▸ OriginalNativeHSResolutionAtlasChoice.projection_mem_open s.sourceIndex z

theorem sourceChart_original_in_product (s : Site f) (z : (sourceChart f s).obj.left) :
    (OriginalNativeHSGlobalResolution.projection X).hom.left.base ((sourceChartInclusion f s).hom.left.base z) ∈
      range s.chart.hom.left.base :=
  s.closure_in_chart (OriginalNativeHSResolutionAtlasChoice.open_subset_compact s.sourceIndex
    (sourceChart_original_mem_open f s z))

theorem sourceChart_image_in_target (s : Site f) (z : (sourceChart f s).obj.left) :
    f.hom.left.base ((OriginalNativeHSGlobalResolution.projection X).hom.left.base
      ((sourceChartInclusion f s).hom.left.base z)) ∈ OriginalNativeHSResolutionAtlasChoice.openSet s.targetIndex :=
  s.image_closure ⟨_,OriginalNativeHSResolutionAtlasChoice.open_subset_compact s.sourceIndex
    (sourceChart_original_mem_open f s z),rfl⟩

end
end Hironaka.Analytic.Unibranch.OriginalNativeGlobalSmoothAtlasSites
