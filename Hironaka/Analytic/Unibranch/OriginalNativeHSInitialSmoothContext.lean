import Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentSmoothContext
import Hironaka.Analytic.Unibranch.OriginalNativeSmoothOpenLocality

/-! Ordinary genuine initial product chart -> actual nil-history smooth
Context, with no supplied initial comparison map. Blueprint FIRST:
original-native-hs-initial-smooth-context.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSInitialSmoothContext
noncomputable section
open SourceReducedComplexSpace OriginalNativeHSShadowOuterState OriginalNativeProductWindow
  OriginalNativeSmoothLocalProduct OriginalNativeSmoothComposition OriginalNativeSmoothOpenLocality
  OriginalNativeHSCurrentSmoothContext OriginalNativeHSOuterHistory

variable {X Y : SourceReducedComplexSpace} (f : X ⟶ Y) (e0 : LocalEmbedding Y) (r : ℕ)
  (O : Opens (productAmbient e0 r)) (a : windowSpace e0 r O ⟶ X)
  (ha : LocallyRingedSpace.IsOpenImmersion a.hom.left) (hChart : a ≫ f = windowFirst e0 r O)
  (KS : Set X.obj.left) (KT : Set Y.obj.left) (hKS : IsCompact KS) (hKT : IsCompact KT)
  (hRange : KS ⊆ range a.hom.left.base) (hImage : f.hom.left.base '' KS ⊆ KT)

def targetNeighbourhood : OriginalNativePrecompactNeighbourhood.Neighbourhood Y KT ⊤ :=
  OriginalNativePrecompactNeighbourhood.neighbourhood Y KT hKT ⊤ (fun _ _ => Set.mem_univ _)
local notation "NT" => targetNeighbourhood KT hKT

def sourceNeighbourhood : OriginalNativePrecompactNeighbourhood.Neighbourhood X KS
    (⟨range a.hom.left.base,ha.base_open.isOpen_range⟩ ⊓
      ⟨f.hom.left.base ⁻¹' ((NT).openSet : Set Y.obj.left),
        (NT).openSet.isOpen.preimage f.hom.left.base.hom.continuous⟩) :=
  OriginalNativePrecompactNeighbourhood.neighbourhood X KS hKS _
    (fun _ hx => ⟨hRange hx,(NT).contains (hImage ⟨_,hx,rfl⟩)⟩)
local notation "NS" => sourceNeighbourhood f e0 r O a ha KS KT hKS hKT hRange hImage

private theorem initial_source_range : closure ((NS).openSet : Set X.obj.left) ⊆
    range (initial X KS).inclusion.hom.left.base := fun x _ => ⟨x,rfl⟩
private theorem initial_target_range : closure ((NT).openSet : Set Y.obj.left) ⊆
    range (initial Y KT).inclusion.hom.left.base := fun y _ => ⟨y,rfl⟩

private abbrev source := OriginalNativeHSCurrentOverlap.endpoint (initial X KS) (NS).openSet (NS).compactClosure
  (initial_source_range f e0 r O a ha KS KT hKS hKT hRange hImage)
private abbrev target := OriginalNativeHSCurrentOverlap.endpoint (initial Y KT) (NT).openSet (NT).compactClosure
  (initial_target_range KT hKT)
private abbrev sourceInclusion : source f e0 r O a ha KS KT hKS hKT hRange hImage ⟶ X :=
  OriginalNativeHSCurrentOverlap.inclusion (initial X KS) (NS).openSet (NS).compactClosure
    (initial_source_range f e0 r O a ha KS KT hKS hKT hRange hImage)
private abbrev targetInclusion : target KT hKT ⟶ Y :=
  OriginalNativeHSCurrentOverlap.inclusion (initial Y KT) (NT).openSet (NT).compactClosure (initial_target_range KT hKT)

private theorem sourceInclusion_open : LocallyRingedSpace.IsOpenImmersion
    (sourceInclusion f e0 r O a ha KS KT hKS hKT hRange hImage).hom.left :=
  OriginalNativePrescribedOpenHistory.sourceInclusion_isOpenImmersion _ _ _ _ _ _
private theorem targetInclusion_open : LocallyRingedSpace.IsOpenImmersion (targetInclusion KT hKT).hom.left :=
  OriginalNativePrescribedOpenHistory.sourceInclusion_isOpenImmersion _ _ _ _ _ _

private theorem source_range : range (sourceInclusion f e0 r O a ha KS KT hKS hKT hRange hImage).hom.left.base =
    ((NS).openSet : Set X.obj.left) := by
  change range (Subtype.val : {x : X.obj.left // x ∈ (NS).openSet} → X.obj.left) = _
  exact Subtype.range_coe
private theorem target_range : range (targetInclusion KT hKT).hom.left.base = ((NT).openSet : Set Y.obj.left) := by
  change range (Subtype.val : {y : Y.obj.left // y ∈ (NT).openSet} → Y.obj.left) = _
  exact Subtype.range_coe

private theorem mapRange : range (sourceInclusion f e0 r O a ha KS KT hKS hKT hRange hImage ≫ f).hom.left.base ⊆
    range (targetInclusion KT hKT).hom.left.base := by
  rw [target_range]
  rintro _ ⟨z,rfl⟩
  have hz : (sourceInclusion f e0 r O a ha KS KT hKS hKT hRange hImage).hom.left.base z ∈ (NS).openSet := by
    exact (Set.ext_iff.mp (source_range f e0 r O a ha KS KT hKS hKT hRange hImage) _).mp ⟨z,rfl⟩
  exact ((NS).closure_subset (subset_closure hz)).2

def map : source f e0 r O a ha KS KT hKS hKT hRange hImage ⟶ target KT hKT := by
  let i := targetInclusion KT hKT
  let : LocallyRingedSpace.IsOpenImmersion i.hom.left := targetInclusion_open KT hKT
  let l := LocallyRingedSpace.IsOpenImmersion.lift i.hom.left
    (sourceInclusion f e0 r O a ha KS KT hKS hKT hRange hImage ≫ f).hom.left
    (mapRange f e0 r O a ha KS KT hKS hKT hRange hImage)
  have hf : l ≫ i.hom.left = (sourceInclusion f e0 r O a ha KS KT hKS hKT hRange hImage ≫ f).hom.left :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _
  refine ObjectProperty.homMk (Over.homMk l ?_)
  exact (congrArg (fun p => l ≫ p) (Over.w i.hom).symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun p => p ≫ Y.obj.hom) hf).trans
        (Over.w (sourceInclusion f e0 r O a ha KS KT hKS hKT hRange hImage ≫ f).hom)))

theorem map_square : map f e0 r O a ha KS KT hKS hKT hRange hImage ≫ targetInclusion KT hKT =
    sourceInclusion f e0 r O a ha KS KT hKS hKT hRange hImage ≫ f := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  let : LocallyRingedSpace.IsOpenImmersion (targetInclusion KT hKT).hom.left := targetInclusion_open KT hKT
  exact LocallyRingedSpace.IsOpenImmersion.lift_fac (targetInclusion KT hKT).hom.left
    (sourceInclusion f e0 r O a ha KS KT hKS hKT hRange hImage ≫ f).hom.left
    (mapRange f e0 r O a ha KS KT hKS hKT hRange hImage)

private theorem first_smooth : IsSmoothMorphism (windowFirst e0 r O) := by
  let hWP : MapsTo (Prod.fst : productAmbient e0 r → e0.ambient) O (⊤ : Opens e0.ambient) := fun _ _ => mem_univ _
  have hp := isSmoothMorphism_comp (nativeProjection e0 r ⊤ O hWP) (OriginalNativeSmoothLocalProduct.targetInclusion e0 ⊤)
    (nativeProjection_isSmooth e0 r ⊤ O hWP)
    (isSmoothMorphism_of_isOpenImmersion _ (targetInclusion_isOpenImmersion e0 ⊤))
  exact (nativeProjection_square e0 r ⊤ O hWP) ▸ hp

include hChart in
theorem smooth : IsSmoothMorphism (map f e0 r O a ha KS KT hKS hKT hRange hImage) := by
  have hsub : range (sourceInclusion f e0 r O a ha KS KT hKS hKT hRange hImage).hom.left.base ⊆ range a.hom.left.base := by
    rw [source_range]
    exact fun _ hx => ((NS).closure_subset (subset_closure hx)).1
  obtain ⟨j,hj,hja⟩ := exists_native_open_lift a (sourceInclusion f e0 r O a ha KS KT hKS hKT hRange hImage)
    ha (sourceInclusion_open f e0 r O a ha KS KT hKS hKT hRange hImage) hsub
  have he : sourceInclusion f e0 r O a ha KS KT hKS hKT hRange hImage ≫ f = j ≫ windowFirst e0 r O :=
    (congrArg (fun p => p ≫ f) hja.symm).trans ((Category.assoc _ _ _).trans (congrArg (fun p => j ≫ p) hChart))
  have hs : IsSmoothMorphism (sourceInclusion f e0 r O a ha KS KT hKS hKT hRange hImage ≫ f) :=
    (congrArg IsSmoothMorphism he).mpr (isSmoothMorphism_comp _ _ (isSmoothMorphism_of_isOpenImmersion _ hj) (first_smooth e0 r O))
  exact isSmoothMorphism_of_postcomp_openImmersion _ (targetInclusion KT hKT) (targetInclusion_open KT hKT)
    ((congrArg IsSmoothMorphism (map_square f e0 r O a ha KS KT hKS hKT hRange hImage)).mpr hs)

private theorem source_projection :
    (OriginalNativeHSCurrentOverlap.history (initial X KS) (NS).openSet (NS).compactClosure
      (initial_source_range f e0 r O a ha KS KT hKS hKT hRange hImage)).projection ≫
      OriginalRelativelyCompactRestriction.inclusion X (NS).openSet (NS).compactClosure =
    sourceInclusion f e0 r O a ha KS KT hKS hKT hRange hImage := by
  have h := OriginalNativePrescribedOpenHistory.projection_square (initial X KS).inclusion
    (initial X KS).inclusion_isOpenImmersion (NS).openSet (NS).compactClosure
    (initial_source_range f e0 r O a ha KS KT hKS hKT hRange hImage) (initial X KS).history
  have hi : sourceInclusion f e0 r O a ha KS KT hKS hKT hRange hImage ≫
      (initial X KS).history.projection ≫ (initial X KS).inclusion =
        sourceInclusion f e0 r O a ha KS KT hKS hKT hRange hImage :=
    (congrArg (fun p => sourceInclusion f e0 r O a ha KS KT hKS hKT hRange hImage ≫ p)
      (Category.id_comp (𝟙 X))).trans (Category.comp_id _)
  exact h.trans hi
private theorem target_projection :
    (OriginalNativeHSCurrentOverlap.history (initial Y KT) (NT).openSet (NT).compactClosure
      (initial_target_range KT hKT)).projection ≫
      OriginalRelativelyCompactRestriction.inclusion Y (NT).openSet (NT).compactClosure = targetInclusion KT hKT := by
  have h := OriginalNativePrescribedOpenHistory.projection_square (initial Y KT).inclusion
    (initial Y KT).inclusion_isOpenImmersion (NT).openSet (NT).compactClosure (initial_target_range KT hKT) (initial Y KT).history
  have hi : targetInclusion KT hKT ≫ (initial Y KT).history.projection ≫ (initial Y KT).inclusion =
      targetInclusion KT hKT :=
    (congrArg (fun p => targetInclusion KT hKT ≫ p) (Category.id_comp (𝟙 Y))).trans (Category.comp_id _)
  exact h.trans hi

include hChart in
def context : Context f e0 r O a ha hChart (initial X KS) (initial Y KT) where
  compactImage := hImage
  sourceOpen := (NS).openSet
  sourceCompactClosure := (NS).compactClosure
  sourceContains := (NS).contains
  sourceRange := initial_source_range f e0 r O a ha KS KT hKS hKT hRange hImage
  sourceChartRange := fun _ hx => ((NS).closure_subset hx).1
  targetOpen := (NT).openSet
  targetCompactClosure := (NT).compactClosure
  targetContains := (NT).contains
  targetRange := initial_target_range KT hKT
  imageClosure := by rintro _ ⟨x,hx,rfl⟩;exact ((NS).closure_subset hx).2
  map := map f e0 r O a ha KS KT hKS hKT hRange hImage
  smooth := smooth f e0 r O a ha hChart KS KT hKS hKT hRange hImage
  square := (congrArg (fun p => map f e0 r O a ha KS KT hKS hKT hRange hImage ≫ p) (target_projection KT hKT)).trans
    ((map_square f e0 r O a ha KS KT hKS hKT hRange hImage).trans
      ((congrArg (fun p => p ≫ f) (source_projection f e0 r O a ha KS KT hKS hKT hRange hImage).symm).trans (Category.assoc _ _ _)))

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSInitialSmoothContext
