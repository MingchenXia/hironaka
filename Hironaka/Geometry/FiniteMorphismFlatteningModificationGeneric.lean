import Hironaka.Geometry.FiniteMorphismFlattening
import Hironaka.Geometry.ProjectiveCompactification
import Hironaka.Algebra.FunctionFieldDimensionGenericFiber

/-!
# The actual generic fibre underlying the finite strict transform

For a dominant map of affine domains, every nonzero blowup chart contains the
whole actual generic fibre of the original base change. Its canonical generic
tensor model is therefore an isomorphism, and the same schematic transform is
integral. No finite-flat or birationality certificate is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

namespace Hironaka.Geometry.FiniteMorphismFlattening

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An actual open pullback is an isomorphism when its open contains the entire image. -/
theorem isIso_openPullback_of_range_subset {X Y U V : Scheme.{u}}
    {f : X ⟶ Y} {f' : U ⟶ V} {iU : U ⟶ X} {iV : V ⟶ Y}
    [IsOpenImmersion iV] (H : IsPullback f' iU iV f)
    (h : Set.range f ⊆ Set.range iV) : IsIso iU := by
  let H' := IsOpenImmersion.isPullback_lift_id f iV h
  have he : (H.isoIsPullback _ _ H').hom = iU := by
    simpa using H.isoIsPullback_hom_snd _ _ H'
  rw [← he]
  infer_instance

variable (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
  (I : Ideal R) (g : R) (hg : g ∈ I) (hg0 : g ≠ 0)

/-- Every actual generic-fibre point belongs to the literal original tensor chart. -/
theorem genericFiberInclusion_range_subset_chart :
    Set.range (genericFiberInclusion R A I) ⊆
      Set.range (chartBaseChangedMap R A I g hg hg0) := by
  have hr := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (chartBaseChangedMap_isPullback R A I g hg hg0).flip
    (⊤ : (Spec (.of (affineBlowupFractionChart I g))).Opens)
  simp only [Scheme.Hom.preimage_top, Scheme.Hom.image_top_eq_opensRange] at hr
  rintro _ ⟨x, rfl⟩
  change genericFiberInclusion R A I x ∈
    (chartBaseChangedMap R A I g hg hg0).opensRange
  rw [hr]
  change baseChangedMap R A I (genericFiberInclusion R A I x) ∈
    (affineBlowupChartInclusion I g hg hg0).opensRange
  rw [affineBlowupChartInclusion_opensRange]
  apply affineBlowupStructure_preimage_le_chart I g hg
  have hx := congrArg (fun k => k x)
    ((baseChangedToBase R A I).fiber_fac (genericPoint (Spec (.of R))))
  simp only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] at hx
  change baseChangedToBase R A I (genericFiberInclusion R A I x) ∈
    PrimeSpectrum.basicOpen g
  have hmem : genericPoint (Spec (.of R)) ∈
      (PrimeSpectrum.basicOpen g : (Spec (.of R)).Opens) := by
    rw [genericPoint_eq_bot_of_affine]
    change g ∉ (⊥ : Ideal R)
    simpa using hg0
  exact hx.symm ▸ hmem

/-- The canonical generic tensor comparison is an actual isomorphism onto the entire native fibre. -/
theorem genericChartToGlobalFiber_isIso :
    IsIso (genericChartToGlobalFiber R A I g hg hg0) :=
  isIso_openPullback_of_range_subset
    (genericChartToGlobalFiber_isPullback R A I g hg hg0)
    (genericFiberInclusion_range_subset_chart R A I g hg hg0)

include g hg hg0 in
/-- Injectivity of the original coefficient map makes the same actual generic fibre integral. -/
theorem baseChanged_genericFiber_isIntegral [IsDomain A]
    (hinj : Function.Injective (algebraMap R A)) :
    IsIntegral ((baseChangedToBase R A I).fiber (genericPoint (Spec (.of R)))) := by
  let : IsDomain (FractionRing R ⊗[R] A) :=
    Algebra.FunctionFieldDimension.genericTensor_isDomain R A (FractionRing R) hinj
  let : IsIso (genericChartToGlobalFiber R A I g hg hg0) :=
    genericChartToGlobalFiber_isIso R A I g hg hg0
  exact IsIntegral.of_isIso (genericChartToGlobalFiber R A I g hg hg0)

/-- The actual schematic generic-fibre transform is integral for any nonzero blowup ideal
and any injective morphism of affine domains. Finiteness of the original algebra is unnecessary. -/
theorem globalTransform_isIntegral [IsDomain A]
    (hinj : Function.Injective (algebraMap R A)) (hI : I ≠ ⊥) :
    IsIntegral (globalTransform R A I) := by
  obtain ⟨g, hg, hg0⟩ : ∃ g ∈ I, g ≠ 0 := by
    by_contra! hzero
    apply hI
    apply le_antisymm ?_ bot_le
    intro a ha
    change a = 0
    exact hzero a ha
  let : IsIntegral ((baseChangedToBase R A I).fiber (genericPoint (Spec (.of R)))) :=
    baseChanged_genericFiber_isIntegral R A I g hg hg0 hinj
  exact ProjectiveCompactification.image_isIntegral (genericFiberInclusion R A I)

end Hironaka.Geometry.FiniteMorphismFlattening
