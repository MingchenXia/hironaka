import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.Localization.AsSubring

/-!
# Generic quasi-finiteness from a common fraction field

Compatible fraction-field embeddings make the actual generic stalk of an affine source a
fraction field of the target ring too. Native affine stalk-map compatibility then proves
quasi-finiteness at the generic point of the specified affine morphism. No finite-type or
caller-supplied quasi-finiteness hypothesis is needed.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

namespace DeJongAlterations.Geometry.AffineBirational

universe u v w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R S : Type u) (K : Type v)
    [CommRing R] [CommRing S] [IsDomain S] [Field K]
    [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    [IsFractionRing R K] [IsFractionRing S K]

/-- Compatible fraction fields of `S` are canonically isomorphic over `R`. -/
def commonFractionFieldEquiv (L : Type w) [CommRing L] [Algebra S L] [Algebra R L]
    [IsScalarTower R S L] [IsFractionRing S L] : K ≃ₐ[R] L :=
  (IsLocalization.algEquiv (nonZeroDivisors S) K L).restrictScalars R

omit [IsDomain S] in
include K in
/-- A second fraction field of `S` is also a fraction field of `R` under the compatible embeddings. -/
theorem isFractionRing_of_commonFractionField (L : Type w) [CommRing L] [Algebra S L]
    [Algebra R L] [IsScalarTower R S L] [IsFractionRing S L] : IsFractionRing R L :=
  IsFractionRing.of_algEquiv (commonFractionFieldEquiv R S K L)

include K in
/-- The actual affine structure map is quasi-finite at the generic point of its integral source. -/
theorem quasiFiniteAt_genericPoint :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).QuasiFiniteAt
      (genericPoint (Spec (CommRingCat.of S))) := by
  let η : PrimeSpectrum S := genericPoint (Spec (CommRingCat.of S))
  let L : Type u := (Spec.structureSheaf S).presheaf.stalk η
  let : IsFractionRing S L := functionField_isFractionRing_of_affine (CommRingCat.of S)
  let : Algebra R L := ((algebraMap S L).comp (algebraMap R S)).toAlgebra
  let : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsFractionRing R L := isFractionRing_of_commonFractionField R S K L
  have HQ : ((algebraMap S L).comp (algebraMap R S)).QuasiFinite :=
    RingHom.quasiFinite_algebraMap.mpr (inferInstance : Algebra.QuasiFinite R L)
  change ((Spec.map (CommRingCat.ofHom (algebraMap R S))).stalkMap η).hom.QuasiFinite
  apply RingHom.QuasiFinite.of_comp (g :=
    (StructureSheaf.toStalk R (PrimeSpectrum.comap (algebraMap R S) η)).hom)
  have Hfac : StructureSheaf.toStalk R (PrimeSpectrum.comap (algebraMap R S) η) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap R S))).stalkMap η =
        CommRingCat.ofHom (algebraMap R S) ≫ StructureSheaf.toStalk S η :=
    stalkMap_toStalk (CommRingCat.ofHom (algebraMap R S)) η
  change (StructureSheaf.toStalk R (PrimeSpectrum.comap (algebraMap R S) η) ≫
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).stalkMap η).hom.QuasiFinite
  rw [Hfac]
  exact HQ

end DeJongAlterations.Geometry.AffineBirational
