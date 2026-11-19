import Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentSmoothStopLoci
import Hironaka.Analytic.Unibranch.OriginalNativeHSStoppedEndpointComparison
import Hironaka.Analytic.Unibranch.OriginalNativePrescribedHistoryRefinement
import Hironaka.Analytic.Unibranch.OriginalNativeSmoothOpenLocality

/-! Actual BOTH-STOP current smooth Context on honest smaller original opens.
Blueprint FIRST: original-native-hs-current-smooth-stopped-comparison.tex.
No supplied endpoint/phase map or future case packet. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentSmoothStoppedComparison
noncomputable section
open SourceReducedComplexSpace OriginalNativeHSShadowOuterState OriginalNativeProductWindow
  OriginalNativeSmoothLocalProduct OriginalNativeSmoothComposition OriginalNativeSmoothOpenLocality
  OriginalNativeHSCurrentSmoothContext

variable {X Y : SourceReducedComplexSpace} {f : X ⟶ Y} {e0 : LocalEmbedding Y} {r : ℕ}
  {O : Opens (productAmbient e0 r)} {a : windowSpace e0 r O ⟶ X}
  {ha : LocallyRingedSpace.IsOpenImmersion a.hom.left} {hChart : a ≫ f = windowFirst e0 r O}
  {KS : Set X.obj.left} {KT : Set Y.obj.left} {S : State X KS} {T : State Y KT}
  (c : Context f e0 r O a ha hChart S T) (hKS : IsCompact KS) (hKT : IsCompact KT)
  (heS : singularShadow S = ∅) (heT : singularShadow T = ∅)

def targetNeighbourhood : OriginalNativePrecompactNeighbourhood.Neighbourhood Y KT
    (c.targetOpen ⊓ ⟨range (stopped T hKT heT).inclusion.hom.left.base,
      (stopped T hKT heT).inclusion_isOpenImmersion.base_open.isOpen_range⟩) :=
  OriginalNativePrecompactNeighbourhood.neighbourhood Y KT hKT _
    (fun _ hy => ⟨c.targetContains hy,(stopped T hKT heT).contains hy⟩)

local notation "NT" => targetNeighbourhood c hKT heT

def sourceNeighbourhood : OriginalNativePrecompactNeighbourhood.Neighbourhood X KS
    ((c.sourceOpen ⊓ ⟨range (stopped S hKS heS).inclusion.hom.left.base,
      (stopped S hKS heS).inclusion_isOpenImmersion.base_open.isOpen_range⟩) ⊓
      ⟨f.hom.left.base ⁻¹' ((NT).openSet : Set Y.obj.left),
        (NT).openSet.isOpen.preimage f.hom.left.base.hom.continuous⟩) :=
  OriginalNativePrecompactNeighbourhood.neighbourhood X KS hKS _
    (fun _ hx => ⟨⟨c.sourceContains hx,(stopped S hKS heS).contains hx⟩,
      (NT).contains (c.compactImage ⟨_,hx,rfl⟩)⟩)

local notation "NS" => sourceNeighbourhood c hKS hKT heS heT

private theorem sourceOldRange : closure ((NS).openSet : Set X.obj.left) ⊆ range S.inclusion.hom.left.base :=
  fun _ hx => c.sourceRange (subset_closure ((NS).closure_subset hx).1.1)
private theorem targetOldRange : closure ((NT).openSet : Set Y.obj.left) ⊆ range T.inclusion.hom.left.base :=
  fun _ hy => c.targetRange (subset_closure ((NT).closure_subset hy).1)
private theorem sourceStopRange : closure ((NS).openSet : Set X.obj.left) ⊆ range (stopped S hKS heS).inclusion.hom.left.base :=
  fun _ hx => ((NS).closure_subset hx).1.2
private theorem targetStopRange : closure ((NT).openSet : Set Y.obj.left) ⊆ range (stopped T hKT heT).inclusion.hom.left.base :=
  fun _ hy => ((NT).closure_subset hy).2

private theorem sourceSubset : (NS).openSet ≤ c.sourceOpen :=
  fun _ hx => ((NS).closure_subset (subset_closure hx)).1.1
private theorem targetSubset : (NT).openSet ≤ c.targetOpen :=
  fun _ hy => ((NT).closure_subset (subset_closure hy)).1

private abbrev oldSource := OriginalNativeHSCurrentOverlap.endpoint S (NS).openSet (NS).compactClosure
  (sourceOldRange c hKS hKT heS heT)
private abbrev oldTarget := OriginalNativeHSCurrentOverlap.endpoint T (NT).openSet (NT).compactClosure
  (targetOldRange c hKT heT)
private abbrev newSource := OriginalNativeHSCurrentOverlap.endpoint (stopped S hKS heS) (NS).openSet (NS).compactClosure
  (sourceStopRange c hKS hKT heS heT)
private abbrev newTarget := OriginalNativeHSCurrentOverlap.endpoint (stopped T hKT heT) (NT).openSet (NT).compactClosure
  (targetStopRange c hKT heT)

private def sourceRefinement : oldSource c hKS hKT heS heT ⟶
    OriginalNativeHSCurrentOverlap.endpoint S c.sourceOpen c.sourceCompactClosure c.sourceRange :=
  OriginalNativePrescribedHistoryRefinement.sourceMap S.inclusion S.inclusion_isOpenImmersion
    c.sourceOpen c.sourceCompactClosure c.sourceRange S.history (NS).openSet (NS).compactClosure
    (sourceSubset c hKS hKT heS heT)
private def targetRefinement : oldTarget c hKT heT ⟶
    OriginalNativeHSCurrentOverlap.endpoint T c.targetOpen c.targetCompactClosure c.targetRange :=
  OriginalNativePrescribedHistoryRefinement.sourceMap T.inclusion T.inclusion_isOpenImmersion
    c.targetOpen c.targetCompactClosure c.targetRange T.history (NT).openSet (NT).compactClosure
    (targetSubset c hKT heT)

private theorem sourceRefinement_open : LocallyRingedSpace.IsOpenImmersion (sourceRefinement c hKS hKT heS heT).hom.left :=
  OriginalNativePrescribedHistoryRefinement.sourceMap_isOpenImmersion _ _ _ _ _ _ _ _ _
private theorem targetRefinement_open : LocallyRingedSpace.IsOpenImmersion (targetRefinement c hKT heT).hom.left :=
  OriginalNativePrescribedHistoryRefinement.sourceMap_isOpenImmersion _ _ _ _ _ _ _ _ _

private theorem sourceRefinement_original : sourceRefinement c hKS hKT heS heT ≫
    c.sourceHistory.projection ≫ c.sourceBaseInclusion =
    (OriginalNativeHSCurrentOverlap.history S (NS).openSet (NS).compactClosure
      (sourceOldRange c hKS hKT heS heT)).projection ≫
        OriginalRelativelyCompactRestriction.inclusion X (NS).openSet (NS).compactClosure := by
  have hi := OriginalNativePrescribedHistoryRefinement.sourceMap_inclusion S.inclusion S.inclusion_isOpenImmersion
    c.sourceOpen c.sourceCompactClosure c.sourceRange S.history (NS).openSet (NS).compactClosure
    (sourceSubset c hKS hKT heS heT)
  have hn := OriginalNativePrescribedOpenHistory.projection_square S.inclusion S.inclusion_isOpenImmersion
    (NS).openSet (NS).compactClosure (sourceOldRange c hKS hKT heS heT) S.history
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro z
  have hs := congrArg (fun p => p.hom.left.base ((sourceRefinement c hKS hKT heS heT).hom.left.base z)) c.source_square
  have hI := congrArg (fun p => p.hom.left.base z) hi
  have hN := congrArg (fun p => p.hom.left.base z) hn
  exact hs.trans ((congrArg (fun y => S.inclusion.hom.left.base (S.history.projection.hom.left.base y)) hI).trans hN.symm)

private theorem targetRefinement_original : targetRefinement c hKT heT ≫
    c.targetHistory.projection ≫ c.targetBaseInclusion =
    (OriginalNativeHSCurrentOverlap.history T (NT).openSet (NT).compactClosure
      (targetOldRange c hKT heT)).projection ≫
        OriginalRelativelyCompactRestriction.inclusion Y (NT).openSet (NT).compactClosure := by
  have hi := OriginalNativePrescribedHistoryRefinement.sourceMap_inclusion T.inclusion T.inclusion_isOpenImmersion
    c.targetOpen c.targetCompactClosure c.targetRange T.history (NT).openSet (NT).compactClosure
    (targetSubset c hKT heT)
  have hn := OriginalNativePrescribedOpenHistory.projection_square T.inclusion T.inclusion_isOpenImmersion
    (NT).openSet (NT).compactClosure (targetOldRange c hKT heT) T.history
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro z
  have hs := congrArg (fun p => p.hom.left.base ((targetRefinement c hKT heT).hom.left.base z)) c.target_square
  have hI := congrArg (fun p => p.hom.left.base z) hi
  have hN := congrArg (fun p => p.hom.left.base z) hn
  exact hs.trans ((congrArg (fun y => T.inclusion.hom.left.base (T.history.projection.hom.left.base y)) hI).trans hN.symm)

private theorem restrictedRange : range (sourceRefinement c hKS hKT heS heT ≫ c.map).hom.left.base ⊆
    range (targetRefinement c hKT heT).hom.left.base := by
  rintro _ ⟨z,rfl⟩
  have hRange : range (targetRefinement c hKT heT).hom.left.base =
      (c.targetHistory.projection ≫ c.targetBaseInclusion).hom.left.base ⁻¹' ((NT).openSet : Set Y.obj.left) :=
    OriginalNativePrescribedHistoryRefinement.sourceMap_range T.inclusion T.inclusion_isOpenImmersion
      c.targetOpen c.targetCompactClosure c.targetRange T.history (NT).openSet (NT).compactClosure (targetSubset c hKT heT)
  rw [hRange]
  have hs := congrArg (fun p => p.hom.left.base z) (sourceRefinement_original c hKS hKT heS heT)
  have ht := congrArg (fun p => p.hom.left.base ((sourceRefinement c hKS hKT heS heT).hom.left.base z)) c.square
  have hz : (OriginalRelativelyCompactRestriction.inclusion X (NS).openSet (NS).compactClosure).hom.left.base
      ((OriginalNativeHSCurrentOverlap.history S (NS).openSet (NS).compactClosure
        (sourceOldRange c hKS hKT heS heT)).projection.hom.left.base z) ∈ (NS).openSet :=
    ((OriginalNativeHSCurrentOverlap.history S (NS).openSet (NS).compactClosure
      (sourceOldRange c hKS hKT heS heT)).projection.hom.left.base z).property
  have hf := ((NS).closure_subset (subset_closure hz)).2
  exact (congrArg (fun y : Y.obj.left => y ∈ (NT).openSet) ht).mpr
    ((congrArg (fun x : X.obj.left => f.hom.left.base x ∈ (NT).openSet) hs).mpr hf)

private def restrictedMap : oldSource c hKS hKT heS heT ⟶ oldTarget c hKT heT := by
  let i := targetRefinement c hKT heT
  let : LocallyRingedSpace.IsOpenImmersion i.hom.left := targetRefinement_open c hKT heT
  let l := LocallyRingedSpace.IsOpenImmersion.lift i.hom.left
    (sourceRefinement c hKS hKT heS heT ≫ c.map).hom.left (restrictedRange c hKS hKT heS heT)
  have hf : l ≫ i.hom.left = (sourceRefinement c hKS hKT heS heT ≫ c.map).hom.left :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _
  refine ObjectProperty.homMk (Over.homMk l ?_)
  exact (congrArg (fun p => l ≫ p) (Over.w i.hom).symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun p => p ≫ (OriginalNativeHSCurrentOverlap.endpoint T c.targetOpen
        c.targetCompactClosure c.targetRange).obj.hom) hf).trans
          (Over.w (sourceRefinement c hKS hKT heS heT ≫ c.map).hom)))

private theorem restrictedMap_square : restrictedMap c hKS hKT heS heT ≫ targetRefinement c hKT heT =
    sourceRefinement c hKS hKT heS heT ≫ c.map := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  let : LocallyRingedSpace.IsOpenImmersion (targetRefinement c hKT heT).hom.left := targetRefinement_open c hKT heT
  exact LocallyRingedSpace.IsOpenImmersion.lift_fac (targetRefinement c hKT heT).hom.left
    (sourceRefinement c hKS hKT heS heT ≫ c.map).hom.left (restrictedRange c hKS hKT heS heT)

private theorem restrictedMap_smooth : IsSmoothMorphism (restrictedMap c hKS hKT heS heT) :=
  isSmoothMorphism_of_postcomp_openImmersion _ (targetRefinement c hKT heT) (targetRefinement_open c hKT heT)
    ((congrArg IsSmoothMorphism (restrictedMap_square c hKS hKT heS heT)).mpr
      (isSmoothMorphism_comp _ _
        (isSmoothMorphism_of_isOpenImmersion _ (sourceRefinement_open c hKS hKT heS heT)) c.smooth))

private theorem restrictedMap_original : restrictedMap c hKS hKT heS heT ≫
    (OriginalNativeHSCurrentOverlap.history T (NT).openSet (NT).compactClosure
      (targetOldRange c hKT heT)).projection ≫
        OriginalRelativelyCompactRestriction.inclusion Y (NT).openSet (NT).compactClosure =
    (OriginalNativeHSCurrentOverlap.history S (NS).openSet (NS).compactClosure
      (sourceOldRange c hKS hKT heS heT)).projection ≫
        OriginalRelativelyCompactRestriction.inclusion X (NS).openSet (NS).compactClosure ≫ f := by
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro z
  have hl := congrArg (fun p => p.hom.left.base z) (restrictedMap_square c hKS hKT heS heT)
  have ht := congrArg (fun p => p.hom.left.base ((restrictedMap c hKS hKT heS heT).hom.left.base z))
    (targetRefinement_original c hKT heT)
  have hs := congrArg (fun p => p.hom.left.base z) (sourceRefinement_original c hKS hKT heS heT)
  have hc := congrArg (fun p => p.hom.left.base ((sourceRefinement c hKS hKT heS heT).hom.left.base z)) c.square
  exact ht.symm.trans ((congrArg (fun y => c.targetBaseInclusion.hom.left.base
    (c.targetHistory.projection.hom.left.base y)) hl).trans (hc.trans (congrArg f.hom.left.base hs)))

private def sourceStopIso : newSource c hKS hKT heS heT ≅ oldSource c hKS hKT heS heT :=
  OriginalNativeHSStoppedEndpointComparison.stoppedComparison S hKS heS (NS).openSet (NS).compactClosure
    (sourceOldRange c hKS hKT heS heT) (sourceStopRange c hKS hKT heS heT)
private def targetStopIso : newTarget c hKT heT ≅ oldTarget c hKT heT :=
  OriginalNativeHSStoppedEndpointComparison.stoppedComparison T hKT heT (NT).openSet (NT).compactClosure
    (targetOldRange c hKT heT) (targetStopRange c hKT heT)

def map : newSource c hKS hKT heS heT ⟶ newTarget c hKT heT :=
  (sourceStopIso c hKS hKT heS heT).hom ≫ restrictedMap c hKS hKT heS heT ≫ (targetStopIso c hKT heT).inv

theorem smooth : IsSmoothMorphism (map c hKS hKT heS heT) := by
  have hs : LocallyRingedSpace.IsOpenImmersion (sourceStopIso c hKS hKT heS heT).hom.hom.left := by
    change LocallyRingedSpace.IsOpenImmersion (isoLeft (sourceStopIso c hKS hKT heS heT)).hom
    infer_instance
  have ht : LocallyRingedSpace.IsOpenImmersion (targetStopIso c hKT heT).inv.hom.left := by
    change LocallyRingedSpace.IsOpenImmersion (isoLeft (targetStopIso c hKT heT)).inv
    infer_instance
  exact isSmoothMorphism_comp _ _ (isSmoothMorphism_of_isOpenImmersion _ hs)
    (isSmoothMorphism_comp _ _ (restrictedMap_smooth c hKS hKT heS heT) (isSmoothMorphism_of_isOpenImmersion _ ht))

theorem original_square : map c hKS hKT heS heT ≫
    (OriginalNativeHSCurrentOverlap.history (stopped T hKT heT) (NT).openSet (NT).compactClosure
      (targetStopRange c hKT heT)).projection ≫
        OriginalRelativelyCompactRestriction.inclusion Y (NT).openSet (NT).compactClosure =
    (OriginalNativeHSCurrentOverlap.history (stopped S hKS heS) (NS).openSet (NS).compactClosure
      (sourceStopRange c hKS hKT heS heT)).projection ≫
        OriginalRelativelyCompactRestriction.inclusion X (NS).openSet (NS).compactClosure ≫ f := by
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro z
  have hs := congrArg (fun p => p.hom.left.base z)
    (OriginalNativeHSStoppedEndpointComparison.stoppedComparison_projection S hKS heS
      (NS).openSet (NS).compactClosure (sourceOldRange c hKS hKT heS heT) (sourceStopRange c hKS hKT heS heT))
  have ht := congrArg (fun p => p.hom.left.base
    ((restrictedMap c hKS hKT heS heT).hom.left.base ((sourceStopIso c hKS hKT heS heT).hom.hom.left.base z)))
    (OriginalNativeHSStoppedEndpointComparison.stoppedComparison_inverse_projection T hKT heT
      (NT).openSet (NT).compactClosure (targetOldRange c hKT heT) (targetStopRange c hKT heT))
  have hm := congrArg (fun p => p.hom.left.base ((sourceStopIso c hKS hKT heS heT).hom.hom.left.base z))
    (restrictedMap_original c hKS hKT heS heT)
  exact (congrArg (OriginalRelativelyCompactRestriction.inclusion Y (NT).openSet (NT).compactClosure).hom.left.base ht).trans
    (hm.trans (congrArg (fun x => f.hom.left.base
      ((OriginalRelativelyCompactRestriction.inclusion X (NS).openSet (NS).compactClosure).hom.left.base x)) hs))

def context : Context f e0 r O a ha hChart (stopped S hKS heS) (stopped T hKT heT) where
  compactImage := c.compactImage
  sourceOpen := (NS).openSet
  sourceCompactClosure := (NS).compactClosure
  sourceContains := (NS).contains
  sourceRange := sourceStopRange c hKS hKT heS heT
  sourceChartRange := fun _ hx => c.sourceChartRange (subset_closure ((NS).closure_subset hx).1.1)
  targetOpen := (NT).openSet
  targetCompactClosure := (NT).compactClosure
  targetContains := (NT).contains
  targetRange := targetStopRange c hKT heT
  imageClosure := by rintro _ ⟨x,hx,rfl⟩;exact ((NS).closure_subset hx).2
  map := map c hKS hKT heS heT
  smooth := smooth c hKS hKT heS heT
  square := original_square c hKS hKT heS heT

/-- The concrete BOTH-STOP constructor on smaller original source and target opens. -/
theorem exists_context : ∃ d : Context f e0 r O a ha hChart (stopped S hKS heS) (stopped T hKT heT),
    d.sourceOpen ≤ c.sourceOpen ∧ d.targetOpen ≤ c.targetOpen :=
  ⟨context c hKS hKT heS heT,sourceSubset c hKS hKT heS heT,targetSubset c hKT heT⟩

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentSmoothStoppedComparison
