import Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentOverlap
import Hironaka.Analytic.Unibranch.OriginalNativeCurrentSmoothProductRank

/-! Honest PAST smooth context for actual states/literal prescribed endpoints.
Full Blueprint FIRST; no next/future case/profile/density supplier fields. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentSmoothContext
noncomputable section
open Hironaka SourceReducedComplexSpace OriginalLocalEmbeddingStalkHS
  OriginalNativeHSOuterHistory OriginalNativeHSShadowOuterState OriginalNativeProductWindow
  OriginalNativeSmoothLocalProduct OriginalNativeSmoothComposition HironakaG1NativeFiniteProductState
  HironakaG11HSPhaseInduction OriginalNativeCurrentSmoothProductRank

structure Context {X Y : SourceReducedComplexSpace} (f : X⟶Y) (e0 : LocalEmbedding Y) (r : ℕ)
    (O : Opens (productAmbient e0 r)) (a : windowSpace e0 r O⟶X)
    (ha : LocallyRingedSpace.IsOpenImmersion a.hom.left) (hChart : a≫f=windowFirst e0 r O)
    {KS : Set X.obj.left} {KT : Set Y.obj.left}
    (S : State X KS) (T : State Y KT) where
  compactImage : (f).hom.left.base '' KS⊆KT
  sourceOpen : Opens X.obj.left
  sourceCompactClosure : IsCompact (closure (sourceOpen : Set X.obj.left))
  sourceContains : KS⊆sourceOpen
  sourceRange : closure (sourceOpen : Set X.obj.left)⊆range S.inclusion.hom.left.base
  sourceChartRange : closure (sourceOpen : Set X.obj.left)⊆range a.hom.left.base
  targetOpen : Opens Y.obj.left
  targetCompactClosure : IsCompact (closure (targetOpen : Set Y.obj.left))
  targetContains : KT⊆targetOpen
  targetRange : closure (targetOpen : Set Y.obj.left)⊆range T.inclusion.hom.left.base
  imageClosure : (f).hom.left.base '' closure (sourceOpen : Set X.obj.left)⊆(targetOpen : Set Y.obj.left)
  map : OriginalNativeHSCurrentOverlap.endpoint S sourceOpen sourceCompactClosure sourceRange ⟶
    OriginalNativeHSCurrentOverlap.endpoint T targetOpen targetCompactClosure targetRange
  smooth : IsSmoothMorphism map
  square : map≫(OriginalNativeHSCurrentOverlap.history T targetOpen targetCompactClosure targetRange).projection≫
      OriginalRelativelyCompactRestriction.inclusion Y targetOpen targetCompactClosure =
    (OriginalNativeHSCurrentOverlap.history S sourceOpen sourceCompactClosure sourceRange).projection≫
      OriginalRelativelyCompactRestriction.inclusion X sourceOpen sourceCompactClosure≫f

namespace Context
variable {X Y : SourceReducedComplexSpace} {f : X⟶Y} {e0 : LocalEmbedding Y} {r : ℕ}
  {O : Opens (productAmbient e0 r)} {a : windowSpace e0 r O⟶X}
  {ha : LocallyRingedSpace.IsOpenImmersion a.hom.left} {hChart : a≫f=windowFirst e0 r O}
  {KS : Set X.obj.left} {KT : Set Y.obj.left}
  {S : State X KS} {T : State Y KT} (c : Context f e0 r O a ha hChart S T)

abbrev sourceHistory := OriginalNativeHSCurrentOverlap.history S c.sourceOpen c.sourceCompactClosure c.sourceRange
abbrev targetHistory := OriginalNativeHSCurrentOverlap.history T c.targetOpen c.targetCompactClosure c.targetRange
abbrev sourceBaseInclusion := OriginalRelativelyCompactRestriction.inclusion
  X c.sourceOpen c.sourceCompactClosure
abbrev targetBaseInclusion := OriginalRelativelyCompactRestriction.inclusion Y c.targetOpen c.targetCompactClosure
abbrev sourceInclusion := OriginalNativeHSCurrentOverlap.inclusion S c.sourceOpen c.sourceCompactClosure c.sourceRange
abbrev targetInclusion := OriginalNativeHSCurrentOverlap.inclusion T c.targetOpen c.targetCompactClosure c.targetRange

instance sourceInclusion_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion c.sourceInclusion.hom.left :=
  OriginalNativePrescribedOpenHistory.sourceInclusion_isOpenImmersion S.inclusion S.inclusion_isOpenImmersion
    c.sourceOpen c.sourceCompactClosure c.sourceRange S.history
instance targetInclusion_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion c.targetInclusion.hom.left :=
  OriginalNativePrescribedOpenHistory.sourceInclusion_isOpenImmersion T.inclusion T.inclusion_isOpenImmersion
    c.targetOpen c.targetCompactClosure c.targetRange T.history

private theorem baseRange : range (c.sourceBaseInclusion≫f).hom.left.base⊆
    range c.targetBaseInclusion.hom.left.base := by
  rw [OriginalRelativelyCompactRestriction.inclusion_range Y c.targetOpen c.targetCompactClosure]
  rintro _ ⟨z,rfl⟩
  exact c.imageClosure ⟨z.val,subset_closure z.property,rfl⟩

private def nativeOpenLift {A B C : SourceReducedComplexSpace}
    (i : B⟶C) (hi : LocallyRingedSpace.IsOpenImmersion i.hom.left) (f : A⟶C)
    (hr : range f.hom.left.base⊆range i.hom.left.base) : A⟶B := by
  let : LocallyRingedSpace.IsOpenImmersion i.hom.left := hi
  let l := LocallyRingedSpace.IsOpenImmersion.lift i.hom.left f.hom.left hr
  have hfac : l≫i.hom.left=f.hom.left := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hr
  have hp : l≫B.obj.hom=A.obj.hom := by
    calc
      _=l≫(i.hom.left≫C.obj.hom) := congrArg (fun t=>l≫t) (Over.w i.hom).symm
      _=(l≫i.hom.left)≫C.obj.hom := (Category.assoc _ _ _).symm
      _=f.hom.left≫C.obj.hom := congrArg (fun t=>t≫C.obj.hom) hfac
      _=_ := Over.w f.hom
  exact ObjectProperty.homMk (Over.homMk l hp)

private theorem nativeOpenLift_fac {A B C : SourceReducedComplexSpace}
    (i : B⟶C) (hi : LocallyRingedSpace.IsOpenImmersion i.hom.left) (f : A⟶C)
    (hr : range f.hom.left.base⊆range i.hom.left.base) : nativeOpenLift i hi f hr≫i=f := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  let : LocallyRingedSpace.IsOpenImmersion i.hom.left := hi
  exact LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hr

/-- Actual native restriction of ORIGINAL f0; not a context field. -/
def baseMap : OriginalRelativelyCompactRestriction.restriction
    X c.sourceOpen c.sourceCompactClosure ⟶
    OriginalRelativelyCompactRestriction.restriction Y c.targetOpen c.targetCompactClosure :=
  nativeOpenLift c.targetBaseInclusion
    (OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion _ _ _)
    (c.sourceBaseInclusion≫f) (baseRange c)

theorem baseMap_square : c.baseMap≫c.targetBaseInclusion=c.sourceBaseInclusion≫f :=
  nativeOpenLift_fac c.targetBaseInclusion
    (OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion _ _ _)
    (c.sourceBaseInclusion≫f) (baseRange c)

theorem base_square : c.map≫c.targetHistory.projection=c.sourceHistory.projection≫c.baseMap := by
  have hfull : (c.map≫c.targetHistory.projection)≫c.targetBaseInclusion=
      (c.sourceHistory.projection≫c.baseMap)≫c.targetBaseInclusion := by
    simpa only [Category.assoc] using c.square.trans
      (congrArg (fun k=>c.sourceHistory.projection≫k) c.baseMap_square).symm
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  let : LocallyRingedSpace.IsOpenImmersion c.targetBaseInclusion.hom.left :=
    OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion _ _ _
  apply (cancel_mono c.targetBaseInclusion.hom.left).mp
  exact congrArg (fun k=>k.hom.left) hfull

theorem source_square : c.sourceHistory.projection≫c.sourceBaseInclusion=
    c.sourceInclusion≫S.history.projection≫S.inclusion :=
  OriginalNativePrescribedOpenHistory.projection_square S.inclusion S.inclusion_isOpenImmersion
    c.sourceOpen c.sourceCompactClosure c.sourceRange S.history

theorem target_square : c.targetHistory.projection≫c.targetBaseInclusion=
    c.targetInclusion≫T.history.projection≫T.inclusion :=
  OriginalNativePrescribedOpenHistory.projection_square T.inclusion T.inclusion_isOpenImmersion
    c.targetOpen c.targetCompactClosure c.targetRange T.history

private theorem prescribed_range {Z : SourceReducedComplexSpace} {K : Set Z.obj.left}
    (A : State Z K) (U : Opens Z.obj.left) (hU : IsCompact (closure (U : Set Z.obj.left)))
    (hRange : closure (U : Set Z.obj.left)⊆range A.inclusion.hom.left.base) :
    range (OriginalNativeHSCurrentOverlap.inclusion A U hU hRange).hom.left.base=
      A.history.projection.hom.left.base ⁻¹' (A.inclusion.hom.left.base ⁻¹' (U : Set Z.obj.left)) := by
  change range (Subtype.val : OriginalRelativelyCompactRestriction.preimageOpen
    (OriginalNativePrescribedOpenHistory.pullbackOpen A.inclusion U) A.history.projection→A.source.obj.left)=_
  rw [Subtype.range_coe]
  rfl

theorem source_range : range c.sourceInclusion.hom.left.base=
    S.history.projection.hom.left.base ⁻¹' (S.inclusion.hom.left.base ⁻¹' (c.sourceOpen : Set X.obj.left)) :=
  prescribed_range S c.sourceOpen c.sourceCompactClosure c.sourceRange

theorem target_range : range c.targetInclusion.hom.left.base=
    T.history.projection.hom.left.base ⁻¹' (T.inclusion.hom.left.base ⁻¹' (c.targetOpen : Set Y.obj.left)) :=
  prescribed_range T c.targetOpen c.targetCompactClosure c.targetRange

/-- ENTIRE inverse original compact under the literal prescribed source history. -/
def sourceCompact : Set (OriginalNativeHSCurrentOverlap.endpoint S c.sourceOpen c.sourceCompactClosure c.sourceRange).obj.left :=
  c.sourceHistory.projection.hom.left.base ⁻¹' (c.sourceBaseInclusion.hom.left.base ⁻¹' KS)

def targetCompact : Set (OriginalNativeHSCurrentOverlap.endpoint T c.targetOpen c.targetCompactClosure c.targetRange).obj.left :=
  c.targetHistory.projection.hom.left.base ⁻¹' (c.targetBaseInclusion.hom.left.base ⁻¹' KT)

private theorem prescribed_compact {Z : SourceReducedComplexSpace} {K : Set Z.obj.left}
    (A : State Z K) (U : Opens Z.obj.left) (hU : IsCompact (closure (U : Set Z.obj.left)))
    (hRange : closure (U : Set Z.obj.left)⊆range A.inclusion.hom.left.base)
    (hContains : K⊆U) (hK : IsCompact K) :
    IsCompact ((OriginalNativeHSCurrentOverlap.history A U hU hRange).projection.hom.left.base ⁻¹'
      ((OriginalRelativelyCompactRestriction.inclusion Z U hU).hom.left.base ⁻¹' K)) := by
  have hb : IsCompact ((OriginalRelativelyCompactRestriction.inclusion Z U hU).hom.left.base ⁻¹' K) :=
    (OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion Z U hU).base_open.isEmbedding.isInducing.isCompact_preimage'
      hK (fun x hx=>⟨⟨x,hContains hx⟩,rfl⟩)
  exact (OriginalNativeHSCurrentOverlap.history A U hU hRange).singularModification.isProperMap.isCompact_preimage hb

theorem sourceCompact_isCompact (hKS : IsCompact KS) : IsCompact c.sourceCompact :=
  prescribed_compact S c.sourceOpen c.sourceCompactClosure c.sourceRange c.sourceContains hKS

theorem targetCompact_isCompact (hKT : IsCompact KT) : IsCompact c.targetCompact :=
  prescribed_compact T c.targetOpen c.targetCompactClosure c.targetRange c.targetContains hKT

private theorem prescribed_shadow_image {Z : SourceReducedComplexSpace} {K : Set Z.obj.left}
    (A : State Z K) (U : Opens Z.obj.left) (hU : IsCompact (closure (U : Set Z.obj.left)))
    (hRange : closure (U : Set Z.obj.left)⊆range A.inclusion.hom.left.base)
    (hContains : K⊆U) :
    (OriginalNativeHSCurrentOverlap.inclusion A U hU hRange).hom.left.base ''
      ((OriginalNativeHSCurrentOverlap.history A U hU hRange).projection.hom.left.base ⁻¹'
        ((OriginalRelativelyCompactRestriction.inclusion Z U hU).hom.left.base ⁻¹' K)) = shadow A := by
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    have hs := congrArg (fun f=>f.hom.left.base z)
      (OriginalNativePrescribedOpenHistory.projection_square A.inclusion A.inclusion_isOpenImmersion U hU hRange A.history)
    exact (congrArg (fun x : Z.obj.left=>x∈K) hs).mp hz
  · intro hy
    have hr : y∈range (OriginalNativeHSCurrentOverlap.inclusion A U hU hRange).hom.left.base := by
      rw [prescribed_range A U hU hRange]
      exact hContains hy
    obtain ⟨z,hz⟩:=hr
    refine ⟨z,?_,hz⟩
    have hs := congrArg (fun f=>f.hom.left.base z)
      (OriginalNativePrescribedOpenHistory.projection_square A.inclusion A.inclusion_isOpenImmersion U hU hRange A.history)
    apply (congrArg (fun x : Z.obj.left=>x∈K) hs).mpr
    change A.inclusion.hom.left.base (A.history.projection.hom.left.base
      ((OriginalNativeHSCurrentOverlap.inclusion A U hU hRange).hom.left.base z))∈K
    rw [hz]
    exact hy

/-- Equality with the ENTIRE existing source State shadow; no g-surjectivity. -/
theorem sourceCompact_image : c.sourceInclusion.hom.left.base '' c.sourceCompact=shadow S :=
  prescribed_shadow_image S c.sourceOpen c.sourceCompactClosure c.sourceRange c.sourceContains

theorem targetCompact_image : c.targetInclusion.hom.left.base '' c.targetCompact=shadow T :=
  prescribed_shadow_image T c.targetOpen c.targetCompactClosure c.targetRange c.targetContains

/-- Whole source compact shadow maps INTO target compact shadow, not onto it. -/
theorem compact_image_subset : c.map.hom.left.base '' c.sourceCompact⊆c.targetCompact := by
  rintro _ ⟨z,hz,rfl⟩
  have hs := congrArg (fun f=>f.hom.left.base z) c.square
  have him : (f).hom.left.base
      (c.sourceBaseInclusion.hom.left.base (c.sourceHistory.projection.hom.left.base z))∈KT :=
    c.compactImage ⟨_,hz,rfl⟩
  exact (congrArg (fun y : Y.obj.left=>y∈KT) hs).mpr him

private theorem chartRange : range c.sourceBaseInclusion.hom.left.base⊆range a.hom.left.base := by
  rintro _ ⟨z,rfl⟩
  exact c.sourceChartRange (subset_closure z.property)

/-- The actual retained ORIGINAL source base lifts to its genuine local product chart. -/
def sourceChartMap : OriginalRelativelyCompactRestriction.restriction X c.sourceOpen c.sourceCompactClosure ⟶
    windowSpace e0 r O := nativeOpenLift a ha c.sourceBaseInclusion (chartRange c)

theorem sourceChartMap_square : c.sourceChartMap≫a=c.sourceBaseInclusion :=
  nativeOpenLift_fac a ha c.sourceBaseInclusion (chartRange c)

instance sourceChartMap_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion c.sourceChartMap.hom.left := by
  let : LocallyRingedSpace.IsOpenImmersion a.hom.left := ha
  let : LocallyRingedSpace.IsOpenImmersion c.sourceBaseInclusion.hom.left :=
    OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion _ _ _
  let : IsIso (CategoryTheory.Limits.pullback.snd a.hom.left c.sourceBaseInclusion.hom.left) :=
    LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset _ _ (chartRange c)
  change LocallyRingedSpace.IsOpenImmersion
    (LocallyRingedSpace.IsOpenImmersion.lift a.hom.left c.sourceBaseInclusion.hom.left (chartRange c))
  dsimp only [LocallyRingedSpace.IsOpenImmersion.lift]
  infer_instance

theorem sourceChartMap_projection : c.sourceChartMap≫windowFirst e0 r O=c.sourceBaseInclusion≫f := by
  rw [←hChart,←Category.assoc,c.sourceChartMap_square]

theorem product_square : c.map≫c.targetHistory.projection≫c.targetBaseInclusion=
    c.sourceHistory.projection≫c.sourceChartMap≫windowFirst e0 r O := by
  exact c.square.trans (congrArg (fun k=>c.sourceHistory.projection≫k) c.sourceChartMap_projection).symm

/-- Actual E-prescribed PAST histories internally derive rank r and the
WHOLE product profile at EVERY actual current point. -/
theorem point_profile (z : (OriginalNativeHSCurrentOverlap.endpoint S c.sourceOpen c.sourceCompactClosure c.sourceRange).obj.left) :
    originalStalkHS (OriginalNativeHSCurrentOverlap.endpoint S c.sourceOpen c.sourceCompactClosure c.sourceRange) z=
      finiteProductHS r (originalStalkHS
        (OriginalNativeHSCurrentOverlap.endpoint T c.targetOpen c.targetCompactClosure c.targetRange)
        (c.map.hom.left.base z)) :=
  OriginalNativeCurrentSmoothProductRank.current_point_profile e0 r O c.sourceChartMap
    c.sourceChartMap_isOpenImmersion c.targetBaseInclusion
    (OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion _ _ _)
    c.sourceHistory c.targetHistory c.map c.product_square c.smooth z

/-- Same whole profile on the actual existing State sources via their OWN OIs. -/
theorem old_point_profile (z : (OriginalNativeHSCurrentOverlap.endpoint S c.sourceOpen c.sourceCompactClosure c.sourceRange).obj.left) :
    originalStalkHS S.source (c.sourceInclusion.hom.left.base z)=
      finiteProductHS r (originalStalkHS T.source (c.targetInclusion.hom.left.base (c.map.hom.left.base z))) :=
  (originalStalkHS_openImmersion c.sourceInclusion c.sourceInclusion_isOpenImmersion z).trans
    ((point_profile c z).trans (congrArg (finiteProductHS r)
      (originalStalkHS_openImmersion c.targetInclusion c.targetInclusion_isOpenImmersion (c.map.hom.left.base z)).symm))

end Context
end
end Hironaka.Analytic.Unibranch.OriginalNativeHSCurrentSmoothContext
