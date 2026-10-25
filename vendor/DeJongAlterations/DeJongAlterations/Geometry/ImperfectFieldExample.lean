/-
Copyright (c) 2026. All rights reserved.
-/
import DeJongAlterations.Algebra.ImperfectFieldExample
import DeJongAlterations.Algebra.RegularLocalDomain
import DeJongAlterations.Geometry.RegularSmooth
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# A genuine regular spectrum whose structure morphism is not smooth

The explicit finite purely inseparable extension `F₃(t)(t^(1/3)) / F₃(t)`
has a regular spectrum and a nonsmooth native structure map. The obstruction
uses the actual tensor product, smooth base change, and faithfully flat
equalizer descent. It does not supply or assume a nonsmoothness certificate.

This field example is the residue-field prerequisite for the stronger
regular-curve example in de Jong 2.10; it does not assert separable generation.
-/

noncomputable section

open scoped TensorProduct
open AlgebraicGeometry CategoryTheory

namespace DeJongAlterations.Geometry.ImperfectFieldExample

theorem isReduced_of_smooth (F A : Type*) [Field F] [CommRing A]
    [Algebra F A] [Algebra.Smooth F A] : IsReduced A := by
  let : IsRegularRing A := RegularSmooth.isRegularRing_of_smooth F A
  apply isReduced_ofLocalizationMaximal
  intro J hJ
  let : J.IsMaximal := hJ
  let : IsDomain (Localization.AtPrime J) :=
    DeJongAlterations.Algebra.RegularLocalDomain.isDomain_of_isRegularLocalRing _
  infer_instance

/-- A smooth purely inseparable extension of fields is the trivial extension. -/
theorem algebraMap_surjective_of_purelyInseparable_smooth (F E : Type*)
    [Field F] [Field E] [Algebra F E] [IsPurelyInseparable F E]
    [Algebra.Smooth F E] : Function.Surjective (algebraMap F E) := by
  let : IsReduced (E ⊗[F] E) := isReduced_of_smooth E (E ⊗[F] E)
  have hm : (Algebra.TensorProduct.includeLeft : E →ₐ[F] E ⊗[F] E) =
      Algebra.TensorProduct.includeRight := Subsingleton.elim _ _
  intro x
  apply ((Algebra.IsEffective.of_faithfullyFlat F E) x).mp
  change x ⊗ₜ[F] (1 : E) - (1 : E) ⊗ₜ[F] x = 0
  exact sub_eq_zero.mpr (AlgHom.congr_fun hm x)

open DeJongAlterations.Algebra.ImperfectFieldExample

theorem rootField_not_smooth : ¬ Algebra.Smooth BaseField RootField := by
  intro h
  let : Algebra.Smooth BaseField RootField := h
  exact algebraMap_not_surjective
    (algebraMap_surjective_of_purelyInseparable_smooth BaseField RootField)

/-- The literal structure map induced by the explicit extension's scalar map. -/
def structureMap : Spec (.of RootField) ⟶ Spec (.of BaseField) :=
  Spec.map (CommRingCat.ofHom (algebraMap BaseField RootField))

theorem specRootField_isRegular : IsRegularScheme (Spec (.of RootField)) :=
  isRegularScheme_spec_field RootField

theorem structure_isFinite : IsFinite structureMap := by
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr inferInstance

theorem structure_not_smooth : ¬ Smooth structureMap := by
  intro h
  exact rootField_not_smooth ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp h)

end DeJongAlterations.Geometry.ImperfectFieldExample
