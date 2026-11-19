import Hironaka.Analytic.Unibranch.HironakaG11BlowupLocality
import Hironaka.Analytic.Unibranch.OriginalRelativelyCompactRestriction
import Hironaka.Analytic.Unibranch.OriginalLocalStrictWindowRegularity
import Hironaka.Analytic.Unibranch.EmbeddedCommonResolutionGeneralAnalyticSubsets

/-! # The SAME literal inverse-open native arrow is a genuine physical blowup

Own entire-ideal Cartier data and full ORIGINAL-source UP are DERIVED from
the old blowup, not assumed for a second arrow. Blueprint FIRST.
-/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace Hironaka.Analytic.Unibranch.OriginalNativeBlowupOpenRestriction
noncomputable section
open Hironaka Hironaka
  SourceReducedComplexSpace SmoothCentreModification HironakaG11BlowupLocality
  HironakaReducedComplexAnalyticSpaces HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaIntrinsicReducedCentreIdealSheaf HironakaNativePulledIdealSheaf
  OriginalIntrinsicSingularLocus

variable {X Y S W A B : SourceReducedComplexSpace}

/-- Actual native open immersions pull back entire intrinsic analytic sets. -/
theorem analytic_preimage_openImmersion (j : W ⟶ X)
    (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left)
    {C : Set X.obj.left} (hC : X.IsAnalyticSubset C) :
    W.IsAnalyticSubset (j.hom.left.base ⁻¹' C) := by
  intro x
  let e := LocalEmbedding.ofPoint W x
  let f : LocalEmbedding X :=
    { dim := e.dim, ambient := e.ambient, carrier := e.carrier, analytic := e.analytic
      map := e.map ≫ j.hom.left
      isOpenImmersion := @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ e.map
        e.isOpenImmersion j.hom.left hj
      overPoint := (Category.assoc _ _ _).trans
        ((congrArg (fun t => e.map ≫ t) (Over.w j.hom)).trans e.overPoint) }
  refine ⟨e, LocalEmbedding.mem_range_ofPoint W x,
    Subtype.val '' (f.toPoint ⁻¹' C), hC.analytic_image_localEmbedding f, ?_⟩
  rw [Subtype.val_injective.preimage_image]
  rfl

private theorem thin_preimage {T V : Type*} [TopologicalSpace T] [TopologicalSpace V]
    {f : T → V} (hf : IsOpenMap f) (hc : Continuous f) {C : Set V}
    (hC : interior C = ∅) : interior (f ⁻¹' C) = ∅ := by
  rw [← hf.preimage_interior_eq_interior_preimage hc, hC, preimage_empty]

private abbrev target (U : Opens X.obj.left)
    (hU : IsCompact (closure (U : Set X.obj.left))) :=
  OriginalRelativelyCompactRestriction.restriction X U hU

private abbrev targetInclusion (U : Opens X.obj.left)
    (hU : IsCompact (closure (U : Set X.obj.left))) :=
  OriginalRelativelyCompactRestriction.inclusion X U hU

private abbrev source (q : Y ⟶ X) (hq : IsProperMap q.hom.left.base)
    (U : Opens X.obj.left) (hU : IsCompact (closure (U : Set X.obj.left))) :=
  OriginalRelativelyCompactRestriction.preimageRestriction U q hU hq

private abbrev sourceInclusion (q : Y ⟶ X) (hq : IsProperMap q.hom.left.base)
    (U : Opens X.obj.left) (hU : IsCompact (closure (U : Set X.obj.left))) :
    source q hq U hU ⟶ Y :=
  OriginalRelativelyCompactRestriction.inclusion Y
    (OriginalRelativelyCompactRestriction.preimageOpen U q)
    (OriginalRelativelyCompactRestriction.isCompact_closure_preimage U q hU hq)

private abbrev projection (q : Y ⟶ X) (hq : IsProperMap q.hom.left.base)
    (U : Opens X.obj.left) (hU : IsCompact (closure (U : Set X.obj.left))) :=
  OriginalRelativelyCompactRestriction.restrictionProjection U q hU hq

private theorem source_range (q : Y ⟶ X) (hq : IsProperMap q.hom.left.base)
    (U : Opens X.obj.left) (hU : IsCompact (closure (U : Set X.obj.left))) :
    range (sourceInclusion q hq U hU).hom.left.base =
      q.hom.left.base ⁻¹' range (targetInclusion U hU).hom.left.base := by
  rw [OriginalRelativelyCompactRestriction.inclusion_range]
  exact Subtype.range_coe

/-- Proper-bimeromorphicity of the SAME literal inverse-open map to its actual target. -/
theorem restriction_isProperBimeromorphic (q : Y ⟶ X) (hq : IsProperBimeromorphic q)
    (U : Opens X.obj.left) (hU : IsCompact (closure (U : Set X.obj.left))) :
    IsProperBimeromorphic
      (OriginalRelativelyCompactRestriction.restrictionProjection U q hU hq.1) := by
  obtain ⟨hprop, C, hCa, hCt, hpre, hiso⟩ := hq
  let j := targetInclusion U hU
  let l := sourceInclusion q hprop U hU
  let p := projection q hprop U hU
  have hj : LocallyRingedSpace.IsOpenImmersion j.hom.left :=
    OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion _ _ _
  have hl : LocallyRingedSpace.IsOpenImmersion l.hom.left :=
    OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion _ _ _
  have hs : p ≫ j = l ≫ q :=
    OriginalRelativelyCompactRestriction.restrictionProjection_inclusion _ _ _ _
  refine ⟨OriginalRelativelyCompactRestriction.restrictionProjection_isProperMap _ _ _ _,
    j.hom.left.base ⁻¹' C, analytic_preimage_openImmersion j hj hCa,
    thin_preimage hj.base_open.isOpenMap j.hom.left.base.hom.continuous hCt, ?_, ?_⟩
  · have heq : p.hom.left.base ⁻¹' (j.hom.left.base ⁻¹' C) =
        l.hom.left.base ⁻¹' (q.hom.left.base ⁻¹' C) := by
      ext z
      exact iff_of_eq (congrArg (fun f => f.hom.left.base z ∈ C) hs)
    rw [heq]
    exact thin_preimage hl.base_open.isOpenMap l.hom.left.base.hom.continuous hpre
  · have h := OriginalLocalStrictWindowRegularity.isIsoOver_of_open_square q p l j hl hj hs
      (source_range q hprop U hU) Cᶜ hiso
    simpa only [preimage_compl] using h

private theorem native_cancel_open (j : W ⟶ X)
    (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left)
    {f g : A ⟶ W} (h : f ≫ j = g ≫ j) : f = g := by
  let : LocallyRingedSpace.IsOpenImmersion j.hom.left := hj
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact (cancel_mono j.hom.left).mp (congrArg (fun t => t.hom.left) h)

/-- Own Cartier data and full original UP on the SAME actual saturated open arrow. -/
theorem isIdealBlowup_of_saturated_open_square
    (q : Y ⟶ X) (p : A ⟶ B) (l : A ⟶ Y) (j : B ⟶ X)
    (hl : LocallyRingedSpace.IsOpenImmersion l.hom.left)
    (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left)
    (hs : p ≫ j = l ≫ q)
    (hr : range l.hom.left.base = q.hom.left.base ⁻¹' range j.hom.left.base)
    (C : Set X.obj.left)
    (hq : IsIdealBlowup q (intrinsicReducedCentreIdealModule X.obj.left C)
      (intrinsicReducedCentreIdealInclusion X.obj.left C)) :
    IsIdealBlowup p
      (intrinsicReducedCentreIdealModule B.obj.left (j.hom.left.base ⁻¹' C))
      (intrinsicReducedCentreIdealInclusion B.obj.left (j.hom.left.base ⁻¹' C)) := by
  let : LocallyRingedSpace.IsOpenImmersion l.hom.left := hl
  let : LocallyRingedSpace.IsOpenImmersion j.hom.left := hj
  have own : HasRankOneData (nativePulledIdealModule p.hom.left
      (intrinsicReducedCentreIdealModule B.obj.left (j.hom.left.base ⁻¹' C))
      (intrinsicReducedCentreIdealInclusion B.obj.left (j.hom.left.base ⁻¹' C))) := by
    apply (hasRankOneData_comp_openImmersion_iff p.hom.left j.hom.left C).mp
    change HasRankOneData (nativePulledIdealModule (p ≫ j).hom.left _ _)
    rw [hs]
    exact hasRankOneData_comp_openImmersion l.hom.left q.hom.left _ _ hq.1
  refine ⟨own, ?_⟩
  intro T F hF
  have hFj := (hasRankOneData_comp_openImmersion_iff F.hom.left j.hom.left C).mpr hF
  obtain ⟨L, hL, hLuniq⟩ := hq.2 T (F ≫ j) hFj
  have hland : range L.hom.left.base ⊆ range l.hom.left.base := by
    rw [hr]
    rintro _ ⟨t, rfl⟩
    exact ⟨F.hom.left.base t, (congrArg (fun f => f.hom.left.base t) hL).symm⟩
  let k := LocallyRingedSpace.IsOpenImmersion.lift l.hom.left L.hom.left hland
  have hkl : k ≫ l.hom.left = L.hom.left :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hland
  have hkScalar : k ≫ A.obj.hom = T.obj.hom := by
    rw [← Over.w l.hom, ← Category.assoc, hkl]
    exact Over.w L.hom
  let K : T ⟶ A := ObjectProperty.homMk (Over.homMk k hkScalar)
  have hKl : K ≫ l = L := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hkl
  have hK : K ≫ p = F := native_cancel_open j hj (by
    rw [Category.assoc, hs, ← Category.assoc, hKl, hL])
  refine ⟨K, hK, ?_⟩
  intro M hM
  apply native_cancel_open l hl
  have hMq : (M ≫ l) ≫ q = F ≫ j := by
    rw [Category.assoc, ← hs, ← Category.assoc, hM]
  exact (hLuniq (M ≫ l) hMq).trans hKl.symm

variable (q : Y ⟶ X) (i : S ⟶ X) (hp : IsSmoothCentreBlowup q i)
  (U : Opens X.obj.left) (hU : IsCompact (closure (U : Set X.obj.left)))

private abbrev centreProper : IsProperMap i.hom.left.base := hp.2.1.isProperMap
private abbrev blowupProper : IsProperMap q.hom.left.base := hp.2.2.2.2.2.2.1

/-- The SAME actual inverse-open restriction of the original centre. -/
def centreSource : SourceReducedComplexSpace := source i (centreProper q i hp) U hU

def centreInclusion : centreSource q i hp U hU ⟶ S :=
  sourceInclusion i (centreProper q i hp) U hU

def centreProjection : centreSource q i hp U hU ⟶ target U hU :=
  projection i (centreProper q i hp) U hU

theorem centreProjection_square : centreProjection q i hp U hU ≫ targetInclusion U hU =
    centreInclusion q i hp U hU ≫ i :=
  OriginalRelativelyCompactRestriction.restrictionProjection_inclusion _ _ _ _

theorem centreProjection_scalar :
    (centreProjection q i hp U hU).hom.left ≫ (target U hU).obj.hom =
      (centreSource q i hp U hU).obj.hom :=
  Over.w (centreProjection q i hp U hU).hom

/-- The whole inverse centre, not an independently chosen support. -/
theorem centreProjection_range : range (centreProjection q i hp U hU).hom.left.base =
    (targetInclusion U hU).hom.left.base ⁻¹' range i.hom.left.base := by
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s.val, (OriginalRelativelyCompactRestriction.restrictionProjection_base
      U i hU (centreProper q i hp) s).symm⟩
  · rintro ⟨s, hs⟩
    have hsU : i.hom.left.base s ∈ U := hs ▸ x.property
    refine ⟨⟨s, hsU⟩, ?_⟩
    apply Subtype.ext
    exact (OriginalRelativelyCompactRestriction.restrictionProjection_base
      U i hU (centreProper q i hp) ⟨s, hsU⟩).trans hs

private theorem centreSmooth : (centreSource q i hp U hU).IsSmooth := by
  apply (isSmooth_iff_intrinsicSingularLocus_eq_empty _).mpr
  change intrinsicSingularLocus
    (OriginalRelativelyCompactRestriction.restriction S
      (OriginalRelativelyCompactRestriction.preimageOpen U i)
      (OriginalRelativelyCompactRestriction.isCompact_closure_preimage U i hU (centreProper q i hp))).obj = ∅
  rw [← OriginalRelativelyCompactRestriction.inclusion_preimage_intrinsicSingularLocus
    S (OriginalRelativelyCompactRestriction.preimageOpen U i)
    (OriginalRelativelyCompactRestriction.isCompact_closure_preimage U i hU (centreProper q i hp)),
    (isSmooth_iff_intrinsicSingularLocus_eq_empty S).mp hp.1, preimage_empty]

private theorem centreClosedEmbedding :
    Topology.IsClosedEmbedding (centreProjection q i hp U hU).hom.left.base := by
  have heq : (fun s => (centreProjection q i hp U hU).hom.left.base s) =
      (U : Set X.obj.left).restrictPreimage i.hom.left.base := by
    funext s
    exact Subtype.ext (OriginalRelativelyCompactRestriction.restrictionProjection_base
      U i hU (centreProper q i hp) s)
  change Topology.IsClosedEmbedding (fun s => (centreProjection q i hp U hU).hom.left.base s)
  rw [heq]
  exact hp.2.1.restrictPreimage _

private theorem centreStalkSurjective (s : (centreSource q i hp U hU).obj.left) :
    Function.Surjective ((centreProjection q i hp U hU).hom.left.stalkMap s) := by
  have hcomp : Function.Surjective
      ((centreProjection q i hp U hU ≫ targetInclusion U hU).hom.left.stalkMap s) := by
    rw [centreProjection_square]
    change Function.Surjective
      (((centreInclusion q i hp U hU).hom.left ≫ i.hom.left).stalkMap s)
    rw [LocallyRingedSpace.stalkMap_comp]
    let hs : IsIso ((centreInclusion q i hp U hU).hom.left.stalkMap s) := by
      let : LocallyRingedSpace.IsOpenImmersion (centreInclusion q i hp U hU).hom.left :=
        OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion _ _ _
      infer_instance
    exact (ConcreteCategory.bijective_of_isIso
      ((centreInclusion q i hp U hU).hom.left.stalkMap s)).2.comp (hp.2.2.1 _)
  change Function.Surjective
    (((centreProjection q i hp U hU).hom.left ≫ (targetInclusion U hU).hom.left).stalkMap s) at hcomp
  rw [LocallyRingedSpace.stalkMap_comp] at hcomp
  intro a
  obtain ⟨b, hb⟩ := hcomp a
  exact ⟨((targetInclusion U hU).hom.left.stalkMap
    ((centreProjection q i hp U hU).hom.left.base s)) b, hb⟩

/-- The SAME literal native restriction has its OWN actual smooth-centre blowup data. -/
theorem restriction_isSmoothCentreBlowup :
    IsSmoothCentreBlowup
      (OriginalRelativelyCompactRestriction.restrictionProjection U q hU
        hp.2.2.2.2.2.2.1) (centreProjection q i hp U hU) := by
  let j := targetInclusion U hU
  let l := sourceInclusion q (blowupProper q i hp) U hU
  let p := projection q (blowupProper q i hp) U hU
  have hj : LocallyRingedSpace.IsOpenImmersion j.hom.left :=
    OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion _ _ _
  have hl : LocallyRingedSpace.IsOpenImmersion l.hom.left :=
    OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion _ _ _
  have htrace := centreProjection_range q i hp U hU
  have hIdeal := isIdealBlowup_of_saturated_open_square q p l j hl hj
    (OriginalRelativelyCompactRestriction.restrictionProjection_inclusion _ _ _ _)
    (source_range q (blowupProper q i hp) U hU) (range i.hom.left.base) hp.2.2.2.2.2.1
  rw [← htrace] at hIdeal
  refine ⟨centreSmooth q i hp U hU, centreClosedEmbedding q i hp U hU,
    centreStalkSurjective q i hp U hU, ?_, ?_, hIdeal,
    restriction_isProperBimeromorphic q hp.2.2.2.2.2.2 U hU⟩
  · rw [htrace]
    exact analytic_preimage_openImmersion j hj hp.2.2.2.1
  · rw [htrace]
    exact thin_preimage hj.base_open.isOpenMap j.hom.left.base.hom.continuous hp.2.2.2.2.1

/-- Actual current-singular containment is retained on the SAME physical restricted arrow. -/
theorem restriction_isSingularCentreStep
    (hsing : range i.hom.left.base ⊆ intrinsicSingularLocus X.obj) :
    HironakaG11SingularCentreModification.IsSingularCentreStep
      (OriginalRelativelyCompactRestriction.restrictionProjection U q hU
        hp.2.2.2.2.2.2.1) := by
  refine ⟨centreSource q i hp U hU, centreProjection q i hp U hU,
    restriction_isSmoothCentreBlowup q i hp U hU, ?_⟩
  rw [centreProjection_range,
    ← OriginalRelativelyCompactRestriction.inclusion_preimage_intrinsicSingularLocus X U hU]
  exact preimage_mono hsing

end
end Hironaka.Analytic.Unibranch.OriginalNativeBlowupOpenRestriction
