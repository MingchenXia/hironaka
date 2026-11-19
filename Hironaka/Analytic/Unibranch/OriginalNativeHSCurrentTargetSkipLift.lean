import Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentSmoothLeadingProfiles
import Hironaka.Analytic.Unibranch.OriginalNativeHSShadowOuterRun
import Hironaka.Analytic.Unibranch.OriginalNativeHSOuterEndpointRange
import Hironaka.Analytic.Unibranch.OriginalNativePrecompactNeighbourhood
import Hironaka.Analytic.Unibranch.OriginalNativeSmoothProductPhaseSpans

/-! ACTUAL native smooth inverse branch to the SAME computed target successor.
Full Blueprint FIRST. Proper SOURCE original-fibre saturation is separate;
no future skip map, source factory or properness of g is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentTargetSkipLift
noncomputable section
open Hironaka SourceReducedComplexSpace
  HironakaIntrinsicComplexAnalyticRegularLocus OriginalLocalEmbeddingStalkHS OriginalIntrinsicHSSuperlevels
  OriginalNativeProductWindow OriginalNativeSmoothLocalProduct OriginalNativeSmoothComposition
  OriginalNativeSmoothOpenLocality OriginalNativeSmoothProductPhaseSpans
  OriginalNativeHSOuterInitialBound OriginalNativeHSShadowOuterState OriginalNativeHSShadowOuterRun
  OriginalNativeHSCurrentSmoothContext OriginalNativeHSThresholdIsomorphism

variable {X Y : SourceReducedComplexSpace} {f : X⟶Y} {e0 : LocalEmbedding Y} {r : ℕ}
  {O : Opens (productAmbient e0 r)} {a : windowSpace e0 r O⟶X}
  {ha : LocallyRingedSpace.IsOpenImmersion a.hom.left} {hChart : a≫f=windowFirst e0 r O}
  {KS : Set X.obj.left} {KT : Set Y.obj.left} {S : State X KS} {T : State Y KT}
  (c : Context f e0 r O a ha hChart S T) (hKT : IsCompact KT) (hneT : (singularShadow T).Nonempty)

private abbrev oldSource := OriginalNativeHSOuterSuccessor.oldSource T.history (baseShadow T)
  (baseShadow_compact T hKT) hneT
private abbrev oldInclusion := OriginalNativeHSOuterSuccessor.oldInclusion T.history (baseShadow T)
  (baseShadow_compact T hKT) hneT
private theorem oldInclusion_open : LocallyRingedSpace.IsOpenImmersion (oldInclusion (T := T) hKT hneT).hom.left :=
  OriginalNativeHSOuterEndpointRange.oldInclusion_isOpenImmersion T.history (baseShadow T)
    (baseShadow_compact T hKT) hneT

private theorem shadow_in_oldRange : shadow T⊆range (oldInclusion (T := T) hKT hneT).hom.left.base := by
  intro y hy
  refine ⟨⟨y,?_⟩,rfl⟩
  exact (OriginalNativeHSOuterSuccessor.neighbourhood T.history (baseShadow T)
    (baseShadow_compact T hKT) hneT).contains hy

/-- Actual old-resaturation range intersected with the actual inverse locus. -/
def skipOpen : Opens (OriginalNativeHSCurrentOverlap.endpoint S c.sourceOpen c.sourceCompactClosure c.sourceRange).obj.left :=
  ⟨((c.map≫c.targetInclusion).hom.left.base ⁻¹' range (oldInclusion (T := T) hKT hneT).hom.left.base) ∩
    ((c.map≫c.targetInclusion).hom.left.base ⁻¹' originalSingularHSThreshold T.source
      (profile T.history (baseShadow T) (baseShadow_compact T hKT) hneT))ᶜ,
    ((oldInclusion_open (T := T) hKT hneT).base_open.isOpen_range.preimage
      (c.map≫c.targetInclusion).hom.left.base.hom.continuous).inter
      (((original_hs_threshold_dictionary T.source
        (profile T.history (baseShadow T) (baseShadow_compact T hKT) hneT)).2.1.isClosed.preimage
          (c.map≫c.targetInclusion).hom.left.base.hom.continuous).isOpen_compl)⟩

variable (hAvoid : ∀z∈c.sourceCompact,(c.map≫c.targetInclusion).hom.left.base z∉
  originalSingularHSThreshold T.source (profile T.history (baseShadow T) (baseShadow_compact T hKT) hneT))

include hAvoid in
private theorem compact_in_skipOpen : c.sourceCompact⊆skipOpen c hKT hneT := by
  intro z hz
  have htarget : c.targetInclusion.hom.left.base (c.map.hom.left.base z)∈shadow T :=
    (Set.ext_iff.mp c.targetCompact_image _).mp ⟨_,c.compact_image_subset ⟨z,hz,rfl⟩,rfl⟩
  exact ⟨shadow_in_oldRange (T := T) hKT hneT htarget,hAvoid z hz⟩

/-- Internally chosen true current-domain neighbourhood retaining ENTIRE source compact. -/
def neighbourhood (hKS : IsCompact KS) : OriginalNativePrecompactNeighbourhood.Neighbourhood
    (OriginalNativeHSCurrentOverlap.endpoint S c.sourceOpen c.sourceCompactClosure c.sourceRange)
    c.sourceCompact (skipOpen c hKT hneT) :=
  OriginalNativePrecompactNeighbourhood.neighbourhood _ c.sourceCompact (c.sourceCompact_isCompact hKS)
    (skipOpen c hKT hneT) (compact_in_skipOpen c hKT hneT hAvoid)

private theorem open_isIsoOver {A B : SourceReducedComplexSpace} (i : A⟶B)
    (hi : LocallyRingedSpace.IsOpenImmersion i.hom.left) : IsIsoOver i (range i.hom.left.base) := by
  refine ⟨A.obj.left,𝟙 _,by infer_instance,?_,?_,?_⟩
  · ext a; simp
  · simpa using hi
  · simp

/-- Construct an actual smooth map to the SAME D39 next source, with both
full native old-target and original-global squares. No future case map input. -/
theorem exists_skip_phase_lift (hKS : IsCompact KS) :
    ∃ b : (neighbourhood c hKT hneT hAvoid hKS).source⟶(next T hKT hneT).source,
      IsSmoothMorphism b ∧
      b≫next_sourceMap T hKT hneT=
        (neighbourhood c hKT hneT hAvoid hKS).inclusion≫c.map≫c.targetInclusion ∧
      b≫(next T hKT hneT).history.projection≫(next T hKT hneT).inclusion=
        (neighbourhood c hKT hneT hAvoid hKS).inclusion≫c.sourceHistory.projection≫c.sourceBaseInclusion≫f := by
  let N := neighbourhood c hKT hneT hAvoid hKS
  let G := N.inclusion≫c.map≫c.targetInclusion
  have hGood (z : N.source.obj.left) : N.inclusion.hom.left.base z∈skipOpen c hKT hneT := by
    have hz : N.inclusion.hom.left.base z∈N.openSet :=
      (Set.ext_iff.mp N.inclusion_range _).mp ⟨z,rfl⟩
    exact N.closure_subset (subset_closure hz)
  have hRange : range G.hom.left.base⊆range (oldInclusion (T := T) hKT hneT).hom.left.base := by
    rintro _ ⟨z,rfl⟩
    exact (hGood z).1
  obtain ⟨F,hF,_,_⟩ := HironakaG10GenDisjointModification.IsIsoOver.exists_lift
    (open_isIsoOver (oldInclusion (T := T) hKT hneT) (oldInclusion_open (T := T) hKT hneT)) G hRange
  have hGSmooth : IsSmoothMorphism G := isSmoothMorphism_comp _ _
    (isSmoothMorphism_of_isOpenImmersion _ N.inclusion_isOpenImmersion)
    (isSmoothMorphism_comp _ _ c.smooth (isSmoothMorphism_of_isOpenImmersion _ c.targetInclusion_isOpenImmersion))
  have hFSmooth : IsSmoothMorphism F := isSmoothMorphism_of_postcomp_openImmersion
    F (oldInclusion (T := T) hKT hneT) (oldInclusion_open (T := T) hKT hneT) (hF.symm ▸ hGSmooth)
  have hThreshold := threshold_preimage_openImmersion
    (profile T.history (baseShadow T) (baseShadow_compact T hKT) hneT)
    (oldInclusion (T := T) hKT hneT) (oldInclusion_open (T := T) hKT hneT)
  have hOff : range F.hom.left.base⊆(originalSingularHSThreshold (oldSource (T := T) hKT hneT)
      (profile T.history (baseShadow T) (baseShadow_compact T hKT) hneT))ᶜ := by
    rintro _ ⟨z,rfl⟩ hbad
    have hbadOld := (Set.ext_iff.mp hThreshold _).mpr hbad
    have hPoint := congrArg (fun k=>k.hom.left.base z) hF
    have hbadG : G.hom.left.base z∈originalSingularHSThreshold T.source
        (profile T.history (baseShadow T) (baseShadow_compact T hKT) hneT) :=
      (congrArg (fun y : T.source.obj.left=>y∈originalSingularHSThreshold T.source
        (profile T.history (baseShadow T) (baseShadow_compact T hKT) hneT)) hPoint).mp hbadOld
    exact (hGood z).2 hbadG
  let p := (OriginalNativeHSOuterSuccessor.phaseSuffix T.history (baseShadow T)
    (baseShadow_compact T hKT) hneT).projection
  have hp : IsIsoOver p (originalSingularHSThreshold (oldSource (T := T) hKT hneT)
      (profile T.history (baseShadow T) (baseShadow_compact T hKT) hneT))ᶜ :=
    OriginalNativeHSOuterSuccessor.phaseSuffix_off_threshold T.history (baseShadow T)
      (baseShadow_compact T hKT) hneT
  obtain ⟨b,hb,_,_⟩ := HironakaG10GenDisjointModification.IsIsoOver.exists_lift hp F hOff
  have hOld : b≫next_sourceMap T hKT hneT=G := by
    calc
      _=b≫p≫oldInclusion (T := T) hKT hneT := congrArg (fun k=>b≫k)
        (OriginalNativeHSOuterSuccessor.phaseSuffix_old_square T.history (baseShadow T)
          (baseShadow_compact T hKT) hneT).symm
      _=(b≫p)≫oldInclusion (T := T) hKT hneT := (Category.assoc _ _ _).symm
      _=F≫oldInclusion (T := T) hKT hneT := congrArg (fun k=>k≫oldInclusion (T := T) hKT hneT) hb
      _=G := hF
  have hOriginal : (c.map≫c.targetInclusion)≫T.history.projection≫T.inclusion=
      c.sourceHistory.projection≫c.sourceBaseInclusion≫f := by
    simpa only [Category.assoc] using
      (congrArg (fun k=>c.map≫k) c.target_square.symm).trans c.square
  refine ⟨b,isSmoothMorphism_lift_of_isIsoOver p hp F hOff hFSmooth b hb,hOld,?_⟩
  calc
    _=(b≫next_sourceMap T hKT hneT)≫T.history.projection≫T.inclusion := by
      simpa only [Category.assoc] using congrArg (fun k=>b≫k) (next_projection_square T hKT hneT)
    _=G≫T.history.projection≫T.inclusion := congrArg (fun k=>k≫T.history.projection≫T.inclusion) hOld
    _=_ := by simpa only [G,Category.assoc] using congrArg (fun k=>N.inclusion≫k) hOriginal

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentTargetSkipLift
