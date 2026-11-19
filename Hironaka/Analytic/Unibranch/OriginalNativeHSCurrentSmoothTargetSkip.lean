import Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentTargetSkipLift
import Hironaka.Analytic.Unibranch.OriginalNativeHSPrescribedFibreShrink

/-! Actual target-only successor Context on SAME global originals, retaining
ALL original compacts. Full Blueprint FIRST; no future case-map supplier. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentSmoothTargetSkip
noncomputable section
open Hironaka SourceReducedComplexSpace
  HironakaIntrinsicComplexAnalyticRegularLocus OriginalLocalEmbeddingStalkHS OriginalIntrinsicHSSuperlevels
  HironakaG1NativeFiniteProductState OriginalNativeProductWindow OriginalNativeSmoothLocalProduct
  OriginalNativeSmoothComposition OriginalNativeSmoothOpenLocality
  OriginalNativeHSOuterInitialBound OriginalNativeHSShadowOuterState OriginalNativeHSShadowOuterRun
  OriginalNativeHSCurrentSmoothContext OriginalNativeHSCurrentSmoothLeadingProfiles

private theorem prescribed_range {Z : SourceReducedComplexSpace} {K : Set Z.obj.left}
    (A : State Z K) (U : Opens Z.obj.left) (hU : IsCompact (closure (U : Set Z.obj.left)))
    (hRange : closure (U : Set Z.obj.left)⊆range A.inclusion.hom.left.base) :
    range (OriginalNativeHSCurrentOverlap.inclusion A U hU hRange).hom.left.base=
      (A.history.projection≫A.inclusion).hom.left.base ⁻¹' (U : Set Z.obj.left) := by
  change range (Subtype.val : OriginalRelativelyCompactRestriction.preimageOpen
    (OriginalNativePrescribedOpenHistory.pullbackOpen A.inclusion U) A.history.projection→A.source.obj.left)=_
  rw [Subtype.range_coe]
  rfl

private theorem open_isIsoOver {A B : SourceReducedComplexSpace} (i : A⟶B)
    (hi : LocallyRingedSpace.IsOpenImmersion i.hom.left) : IsIsoOver i (range i.hom.left.base) := by
  refine ⟨A.obj.left,𝟙 _,by infer_instance,?_,?_,?_⟩
  · ext a; simp
  · simpa using hi
  · simp

variable {X Y : SourceReducedComplexSpace} {f : X⟶Y} {e0 : LocalEmbedding Y} {r : ℕ}
  {O : Opens (productAmbient e0 r)} {a : windowSpace e0 r O⟶X}
  {ha : LocallyRingedSpace.IsOpenImmersion a.hom.left} {hChart : a≫f=windowFirst e0 r O}
  {KS : Set X.obj.left} {KT : Set Y.obj.left} {S : State X KS} {T : State Y KT}
  (c : Context f e0 r O a ha hChart S T)

/-- Construct the REAL target-only next Context from PRESENT source-image
avoidance; no source nonempty-Sing/factory or future-map input is needed. -/
theorem exists_context (hKS : IsCompact KS) (hKT : IsCompact KT) (hneT : (singularShadow T).Nonempty)
    (hAvoid : ∀z∈c.sourceCompact,(c.map≫c.targetInclusion).hom.left.base z∉
      originalSingularHSThreshold T.source (profile T.history (baseShadow T) (baseShadow_compact T hKT) hneT)) :
    ∃ d : Context f e0 r O a ha hChart S (next T hKT hneT),
      d.sourceOpen≤c.sourceOpen ∧ d.targetOpen≤c.targetOpen := by
  let Tn := next T hKT hneT
  let targetGood : Opens Y.obj.left :=
    ⟨(c.targetOpen : Set Y.obj.left)∩range Tn.inclusion.hom.left.base,
      c.targetOpen.isOpen.inter Tn.inclusion_isOpenImmersion.base_open.isOpen_range⟩
  have hTargetGood : KT⊆targetGood := fun y hy=>⟨c.targetContains hy,Tn.contains hy⟩
  let TN := OriginalNativePrecompactNeighbourhood.neighbourhood Y KT hKT targetGood hTargetGood
  let W := TN.openSet
  have hW : IsCompact (closure (W : Set Y.obj.left)) := TN.compactClosure
  have wRange : closure (W : Set Y.obj.left)⊆range Tn.inclusion.hom.left.base :=
    fun _ hy=>(TN.closure_subset hy).2
  let N := OriginalNativeHSCurrentTargetSkipLift.neighbourhood c hKT hneT hAvoid hKS
  obtain ⟨b,hb,_hOld,hGeo⟩ := OriginalNativeHSCurrentTargetSkipLift.exists_skip_phase_lift c hKT hneT hAvoid hKS
  let U := N.openSet
  have hGood : OriginalNativeHSPrescribedFibreShrink.compact S c.sourceOpen c.sourceCompactClosure c.sourceRange⊆U := N.contains
  let extra : Opens X.obj.left := ⟨f.hom.left.base ⁻¹' (W : Set Y.obj.left),W.isOpen.preimage f.hom.left.base.hom.continuous⟩
  have hExtra : KS⊆extra := fun x hx=>TN.contains (c.compactImage ⟨x,hx,rfl⟩)
  let V := OriginalNativeHSPrescribedFibreShrink.openSet S c.sourceOpen c.sourceCompactClosure c.sourceRange
    c.sourceContains hKS U hGood extra hExtra
  have hV : IsCompact (closure (V : Set X.obj.left)) :=
    OriginalNativeHSPrescribedFibreShrink.compactClosure S c.sourceOpen c.sourceCompactClosure c.sourceRange
      c.sourceContains hKS U hGood extra hExtra
  have vRange : closure (V : Set X.obj.left)⊆range S.inclusion.hom.left.base :=
    OriginalNativeHSPrescribedFibreShrink.closureRange S c.sourceOpen c.sourceCompactClosure c.sourceRange
      c.sourceContains hKS U hGood extra hExtra
  have hVold : closure (V : Set X.obj.left)⊆c.sourceOpen :=
    OriginalNativeHSPrescribedFibreShrink.closure_subset_old S c.sourceOpen c.sourceCompactClosure c.sourceRange
      c.sourceContains hKS U hGood extra hExtra
  have hVextra : closure (V : Set X.obj.left)⊆extra :=
    OriginalNativeHSPrescribedFibreShrink.closure_subset_extra S c.sourceOpen c.sourceCompactClosure c.sourceRange
      c.sourceContains hKS U hGood extra hExtra
  let k := OriginalNativeHSPrescribedFibreShrink.sourceMap S c.sourceOpen c.sourceCompactClosure c.sourceRange
    c.sourceContains hKS U hGood extra hExtra
  have hk : LocallyRingedSpace.IsOpenImmersion k.hom.left :=
    OriginalNativeHSPrescribedFibreShrink.sourceMap_isOpenImmersion S c.sourceOpen c.sourceCompactClosure c.sourceRange
      c.sourceContains hKS U hGood extra hExtra
  have hkRange : range k.hom.left.base⊆range N.inclusion.hom.left.base := by
    rw [N.inclusion_range]
    exact OriginalNativeHSPrescribedFibreShrink.sourceMap_in_good S c.sourceOpen c.sourceCompactClosure c.sourceRange
      c.sourceContains hKS U hGood extra hExtra
  obtain ⟨l,hl,hfac⟩ := exists_native_open_lift N.inclusion k N.inclusion_isOpenImmersion hk hkRange
  let qS := (OriginalNativeHSCurrentOverlap.history S V hV vRange).projection
  let iS := OriginalRelativelyCompactRestriction.inclusion X V hV
  have hSource : qS≫iS=k≫c.sourceHistory.projection≫c.sourceBaseInclusion :=
    OriginalNativeHSPrescribedFibreShrink.projection_square S c.sourceOpen c.sourceCompactClosure c.sourceRange
      c.sourceContains hKS U hGood extra hExtra
  let bFull := l≫b
  have hFullSmooth : IsSmoothMorphism bFull := isSmoothMorphism_comp _ _
    (isSmoothMorphism_of_isOpenImmersion _ hl) hb
  have hFullSquare : bFull≫Tn.history.projection≫Tn.inclusion=qS≫iS≫f := by
    calc
      _=l≫(b≫Tn.history.projection≫Tn.inclusion) := by simp only [bFull,Category.assoc]
      _=l≫(N.inclusion≫c.sourceHistory.projection≫c.sourceBaseInclusion≫f) := congrArg (fun m=>l≫m) hGeo
      _=(l≫N.inclusion)≫c.sourceHistory.projection≫c.sourceBaseInclusion≫f := by simp only [Category.assoc]
      _=(k≫c.sourceHistory.projection≫c.sourceBaseInclusion)≫f := by rw [hfac]; simp only [Category.assoc]
      _=(qS≫iS)≫f := congrArg (fun m=>m≫f) hSource.symm
      _=_ := Category.assoc _ _ _
  let jT := OriginalNativeHSCurrentOverlap.inclusion Tn W hW wRange
  have hjT : LocallyRingedSpace.IsOpenImmersion jT.hom.left :=
    OriginalNativePrescribedOpenHistory.sourceInclusion_isOpenImmersion Tn.inclusion Tn.inclusion_isOpenImmersion
      W hW wRange Tn.history
  have hTargetRange : range bFull.hom.left.base⊆range jT.hom.left.base := by
    rw [prescribed_range Tn W hW wRange]
    rintro _ ⟨z,rfl⟩
    have hzV : iS.hom.left.base (qS.hom.left.base z)∈V := (qS.hom.left.base z).property
    have him : f.hom.left.base (iS.hom.left.base (qS.hom.left.base z))∈W := hVextra (subset_closure hzV)
    have hp := congrArg (fun m=>m.hom.left.base z) hFullSquare
    exact (congrArg (fun y : Y.obj.left=>y∈(W : Set Y.obj.left)) hp).mpr him
  obtain ⟨g,hg,_,_⟩ := HironakaG10GenDisjointModification.IsIsoOver.exists_lift
    (open_isIsoOver jT hjT) bFull hTargetRange
  have hSmooth : IsSmoothMorphism g := isSmoothMorphism_of_postcomp_openImmersion g jT hjT (hg.symm ▸ hFullSmooth)
  have hSquare : g≫(OriginalNativeHSCurrentOverlap.history Tn W hW wRange).projection≫
      OriginalRelativelyCompactRestriction.inclusion Y W hW=qS≫iS≫f := by
    calc
      _=g≫jT≫Tn.history.projection≫Tn.inclusion := congrArg (fun m=>g≫m)
        (OriginalNativePrescribedOpenHistory.projection_square Tn.inclusion Tn.inclusion_isOpenImmersion W hW wRange Tn.history)
      _=(g≫jT)≫Tn.history.projection≫Tn.inclusion := by simp only [Category.assoc]
      _=bFull≫Tn.history.projection≫Tn.inclusion := congrArg (fun m=>m≫Tn.history.projection≫Tn.inclusion) hg
      _=_ := hFullSquare
  refine ⟨{
    compactImage := c.compactImage
    sourceOpen := V
    sourceCompactClosure := hV
    sourceContains := OriginalNativeHSPrescribedFibreShrink.contains S c.sourceOpen c.sourceCompactClosure c.sourceRange
      c.sourceContains hKS U hGood extra hExtra
    sourceRange := vRange
    sourceChartRange := fun x hx=>c.sourceChartRange (subset_closure (hVold hx))
    targetOpen := W
    targetCompactClosure := hW
    targetContains := TN.contains
    targetRange := wRange
    imageClosure := by rintro _ ⟨x,hx,rfl⟩; exact hVextra hx
    map := g
    smooth := hSmooth
    square := hSquare
  },?_,?_⟩
  · exact fun x hx=>hVold (subset_closure hx)
  · exact fun y hy=>(TN.closure_subset (subset_closure hy)).1

/-- Strict ACTUAL leading profiles derive present avoidance internally and
invoke the REAL target-only Context constructor. -/
theorem exists_context_of_higher_target (hKS : IsCompact KS) (hKT : IsCompact KT)
    (hneS : (singularShadow S).Nonempty) (hneT : (singularShadow T).Nonempty)
    (hlt : toLex (profile S.history (baseShadow S) (baseShadow_compact S hKS) hneS) <
      toLex (finiteProductHS r (profile T.history (baseShadow T) (baseShadow_compact T hKT) hneT))) :
    ∃d : Context f e0 r O a ha hChart S (next T hKT hneT),
      d.sourceOpen≤c.sourceOpen ∧d.targetOpen≤c.targetOpen :=
  exists_context c hKS hKT hneT (higher_target_avoids_sourceCompact c hKS hKT hneS hneT hlt)

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentSmoothTargetSkip
