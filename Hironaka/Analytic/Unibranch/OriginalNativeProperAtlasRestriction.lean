import Hironaka.Analytic.Unibranch.OriginalRelativelyCompactRestriction
import Hironaka.Analytic.Unibranch.OriginalNativeHSOuterHistory
import Hironaka.Analytic.Unibranch.OriginalNativeSmoothOpenLocality
import Hironaka.Analytic.Unibranch.HironakaG1NativeModificationIsoTransport

/-! Native identification and REAL finite witness for the SAME literal
inverse-open restriction of a proper map, from an ACTUAL saturated chart
and its genuine finite physical history. Blueprint FIRST:
original-native-proper-atlas-restriction.tex. No gluer/future/output packet. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeProperAtlasRestriction
noncomputable section
open SourceReducedComplexSpace OriginalNativeHSOuterHistory

variable {X Z : SourceReducedComplexSpace} (q : Z ⟶ X) (hq : IsProperMap q.hom.left.base)
  (U : Opens X.obj.left) (hU : IsCompact (closure (U : Set X.obj.left)))

abbrev source : SourceReducedComplexSpace :=
  OriginalRelativelyCompactRestriction.preimageRestriction U q hU hq

def sourceInclusion : source q hq U hU ⟶ Z :=
  OriginalRelativelyCompactRestriction.inclusion Z (OriginalRelativelyCompactRestriction.preimageOpen U q)
    (OriginalRelativelyCompactRestriction.isCompact_closure_preimage U q hU hq)

theorem sourceInclusion_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion (sourceInclusion q hq U hU).hom.left :=
  OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion _ _ _

theorem sourceInclusion_range : range (sourceInclusion q hq U hU).hom.left.base = q.hom.left.base ⁻¹' (U : Set X.obj.left) :=
  Subtype.range_coe

def projection : source q hq U hU ⟶ OriginalRelativelyCompactRestriction.restriction X U hU :=
  OriginalRelativelyCompactRestriction.restrictionProjection U q hU hq

theorem projection_square : projection q hq U hU ≫ OriginalRelativelyCompactRestriction.inclusion X U hU =
    sourceInclusion q hq U hU ≫ q :=
  OriginalRelativelyCompactRestriction.restrictionProjection_inclusion U q hU hq

private theorem native_cancel {A B C : SourceReducedComplexSpace} (a b : A ⟶ B) (f : B ⟶ C)
    (hf : LocallyRingedSpace.IsOpenImmersion f.hom.left) (hab : a ≫ f = b ≫ f) : a = b := by
  let : LocallyRingedSpace.IsOpenImmersion f.hom.left := hf
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_mono f.hom.left).mp
  exact congrArg (fun k => k.hom.left) hab

variable {A : SourceReducedComplexSpace} (a : A ⟶ Z)
  (ha : LocallyRingedSpace.IsOpenImmersion a.hom.left)
  (hRange : range a.hom.left.base = q.hom.left.base ⁻¹' (U : Set X.obj.left))

include ha hRange in
private theorem exists_comparison : ∃ E : A ≅ source q hq U hU, E.hom ≫ sourceInclusion q hq U hU = a := by
  have hr : range a.hom.left.base = range (sourceInclusion q hq U hU).hom.left.base :=
    hRange.trans (sourceInclusion_range q hq U hU).symm
  obtain ⟨k,_hk,hk⟩ := OriginalNativeSmoothOpenLocality.exists_native_open_lift
    (sourceInclusion q hq U hU) a (sourceInclusion_isOpenImmersion q hq U hU) ha hr.le
  obtain ⟨l,_hl,hl⟩ := OriginalNativeSmoothOpenLocality.exists_native_open_lift
    a (sourceInclusion q hq U hU) ha (sourceInclusion_isOpenImmersion q hq U hU) hr.symm.le
  have hkl : k ≫ l = 𝟙 A := by
    apply native_cancel _ _ a ha
    rw [Category.assoc,hl,hk,Category.id_comp]
  have hlk : l ≫ k = 𝟙 (source q hq U hU) := by
    apply native_cancel _ _ (sourceInclusion q hq U hU) (sourceInclusion_isOpenImmersion q hq U hU)
    rw [Category.assoc,hk,hl,Category.id_comp]
  exact ⟨⟨k,l,hkl,hlk⟩,hk⟩

def comparison : A ≅ source q hq U hU := (exists_comparison q hq U hU a ha hRange).choose

theorem comparison_inclusion : (comparison q hq U hU a ha hRange).hom ≫ sourceInclusion q hq U hU = a :=
  (exists_comparison q hq U hU a ha hRange).choose_spec

theorem comparison_scalar : (comparison q hq U hU a ha hRange).hom.hom.left ≫ (source q hq U hU).obj.hom = A.obj.hom :=
  Over.w (comparison q hq U hU a ha hRange).hom.hom

variable (h : PhysicalHistory (OriginalRelativelyCompactRestriction.restriction X U hU) A)
  (hSquare : h.projection ≫ OriginalRelativelyCompactRestriction.inclusion X U hU = a ≫ q)

include hSquare in
theorem comparison_projection : (comparison q hq U hU a ha hRange).hom ≫ projection q hq U hU = h.projection := by
  apply native_cancel _ _ (OriginalRelativelyCompactRestriction.inclusion X U hU)
    (OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion X U hU)
  calc
    _ = (comparison q hq U hU a ha hRange).hom ≫ (sourceInclusion q hq U hU ≫ q) :=
      (Category.assoc _ _ _).trans (congrArg (fun k => (comparison q hq U hU a ha hRange).hom ≫ k)
        (projection_square q hq U hU))
    _ = a ≫ q := by rw [← Category.assoc,comparison_inclusion]
    _ = _ := hSquare.symm

include hSquare in
theorem projection_eq_inverse : projection q hq U hU = (comparison q hq U hU a ha hRange).inv ≫ h.projection := by
  rw [← comparison_projection q hq U hU a ha hRange h hSquare,← Category.assoc,
    (comparison q hq U hU a ha hRange).inv_hom_id,Category.id_comp]

include ha hRange hSquare in
theorem finite : SmoothCentreModification.IsModification (projection q hq U hU) := by
  have hf := HironakaG1NativeModificationIsoTransport.isModification_precomp_iso
    h.singularModification.toIsModification (comparison q hq U hU a ha hRange).symm
  rw [projection_eq_inverse q hq U hU a ha hRange h hSquare]
  exact hf

end
end Hironaka.Analytic.Unibranch.OriginalNativeProperAtlasRestriction
