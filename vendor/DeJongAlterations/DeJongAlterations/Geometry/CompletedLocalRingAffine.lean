import DeJongAlterations.Geometry.CompletedLocalRingOpen
import DeJongAlterations.Algebra.AdicCompletionTransportLocalization

/-! # The native completed stalk of an affine spectrum as a completed localization -/

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- For the identity affine structure, the actual coefficient map is the native to-stalk map. -/
theorem baseToStalk_id_spec (R : CommRingCat.{u}) (x : PrimeSpectrum R) :
    baseToStalk (𝟙 (Spec R)) x = StructureSheaf.toStalk R x := by
  unfold baseToStalk Modules.baseRingHom
  simp only [Hom.id_appTop, Category.comp_id, ΓSpecIso_inv]
  exact StructureSheaf.algebraMap_germ (R := R) ⊤ x trivial

/-- A literal affine coefficient map gives the expected actual coefficient map on stalks. -/
theorem baseToStalk_specMap {K R : CommRingCat.{u}} (f : K ⟶ R) (x : PrimeSpectrum R) :
    baseToStalk (Spec.map f) x = f ≫ StructureSheaf.toStalk R x := by
  have h := baseToStalk_comp f (𝟙 (Spec R)) x
  simpa only [Category.id_comp, baseToStalk_id_spec] using h.symm

/-- The actual stalk localization isomorphism induces an isomorphism of native completions. -/
def completedLocalRingSpecRingEquiv (R : CommRingCat.{u}) (x : PrimeSpectrum R) :
    (Spec R).completedLocalRing x ≃+*
      AdicCompletion (R := Localization.AtPrime x.asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime x.asIdeal))
        (Localization.AtPrime x.asIdeal) := by
  let e : (Spec R).presheaf.stalk x ≃+* Localization.AtPrime x.asIdeal :=
    (StructureSheaf.stalkIso R x).symm.toRingEquiv
  exact AdicCompletion.congrRingEquiv _ _ e
    (IsLocalRing.map_ringEquiv_maximalIdeal e).symm

@[simp]
theorem completedLocalRingSpecRingEquiv_toCompletedLocalRing
    (R : CommRingCat.{u}) (x : PrimeSpectrum R) (a : (Spec R).presheaf.stalk x) :
    completedLocalRingSpecRingEquiv R x ((Spec R).toCompletedLocalRing x a) =
      AdicCompletion.of _ _ ((StructureSheaf.stalkIso R x).symm a) := by
  rw [toCompletedLocalRing_apply]
  exact AdicCompletion.congrRingEquiv_of _ _ _ _ a

/-- The actual affine completed-stalk comparison preserves the specified base coefficients. -/
def completedLocalRingSpecAlgEquiv
    (K R : Type u) [CommRing K] [CommRing R] [Algebra K R]
    (x : PrimeSpectrum R) :
    letI := completedLocalRingAlgebra (Spec.map (CommRingCat.ofHom (algebraMap K R))) x
    (Spec (.of R)).completedLocalRing x ≃ₐ[K]
      AdicCompletion (R := Localization.AtPrime x.asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime x.asIdeal))
        (Localization.AtPrime x.asIdeal) := by
  letI := completedLocalRingAlgebra (Spec.map (CommRingCat.ofHom (algebraMap K R))) x
  refine AlgEquiv.ofRingEquiv (f := completedLocalRingSpecRingEquiv (.of R) x) ?_
  intro k
  change completedLocalRingSpecRingEquiv (.of R) x
    ((Spec (.of R)).toCompletedLocalRing x
      (baseToStalk (Spec.map (CommRingCat.ofHom (algebraMap K R))) x k)) = _
  rw [completedLocalRingSpecRingEquiv_toCompletedLocalRing, AdicCompletion.algebraMap_apply]
  congr 1
  rw [baseToStalk_specMap]
  change (StructureSheaf.stalkIso R x).symm (algebraMap R _ (algebraMap K R k)) = _
  rw [AlgEquiv.commutes]
  exact (IsScalarTower.algebraMap_apply K R (Localization.AtPrime x.asIdeal) k).symm

@[simp]
theorem completedLocalRingSpecAlgEquiv_coefficient
    (K R : Type u) [CommRing K] [CommRing R] [Algebra K R]
    (x : PrimeSpectrum R) (r : R) :
    completedLocalRingSpecAlgEquiv K R x
      ((Spec (.of R)).toCompletedLocalRing x (StructureSheaf.toStalk R x r)) =
        AdicCompletion.of _ _ (algebraMap R (Localization.AtPrime x.asIdeal) r) := by
  change completedLocalRingSpecRingEquiv (.of R) x
    ((Spec (.of R)).toCompletedLocalRing x (StructureSheaf.toStalk R x r)) = _
  rw [completedLocalRingSpecRingEquiv_toCompletedLocalRing]
  congr 1
  exact (StructureSheaf.stalkIso R x).symm.commutes r

end AlgebraicGeometry.Scheme
