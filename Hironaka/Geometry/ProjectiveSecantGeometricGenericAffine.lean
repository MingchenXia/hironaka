import Hironaka.Algebra.ProjectiveSecantGeometricGenericField
import Hironaka.Geometry.ProjectiveSecantGeometricReducedAffine
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Hironaka.Geometry.GenericSmoothness

/-!
# The exact original affine generic stalk is smooth from actual geometric reducedness
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The coefficient action on the actual native affine generic field is the literal original coefficient map followed by its native germ. -/
abbrev affineFunctionFieldAlgebra (k A : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A] :
    Algebra k (Spec (CommRingCat.of A)).functionField :=
  ((StructureSheaf.toStalk A (genericPoint (Spec (CommRingCat.of A)))).hom.comp (algebraMap k A)).toAlgebra

/-- The actual finite-type coefficient algebra supplies the native coefficient morphism's finite-type property. -/
instance coefficientSpec_locallyOfFiniteType
    (k A : Type u) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k A))) :=
  (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)

/-- Actual native affine geometric reducedness and finite type put the exact original generic point in the exact original smooth locus. -/
theorem affine_genericPoint_mem_smoothLocus_of_geometricallyReduced
    (k A : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap k A)))] :
    genericPoint (Spec (CommRingCat.of A)) ∈
      (Spec.map (CommRingCat.ofHom (algebraMap k A))).smoothLocus := by
  let X := Spec (CommRingCat.of A)
  let f := Spec.map (CommRingCat.ofHom (algebraMap k A))
  let x := genericPoint X
  let K := X.functionField
  let : Algebra A K := (StructureSheaf.toStalk A x).hom.toAlgebra
  let : IsFractionRing A K := functionField_isFractionRing_of_affine (CommRingCat.of A)
  let : Algebra k K := affineFunctionFieldAlgebra k A
  let : IsScalarTower k A K := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsGeometricallyReduced k A := isGeometricallyReduced_algebra_of_spec k A
  have hfs : Algebra.FormallySmooth k K := Algebra.ProjectiveSecant.formallySmooth_fractionRing_of_geometricallyReduced k A K
  have hcomm : StructureSheaf.toStalk k (f x) ≫ f.stalkMap x =
      CommRingCat.ofHom (algebraMap k A) ≫ StructureSheaf.toStalk A x := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp]
    simpa only [X, f, Spec.fromSpecStalk_eq'] using
      (Scheme.SpecMap_stalkMap_fromSpecStalk f (x := x))
  let e : k ≃ₐ[k] ((Spec.structureSheaf k).presheaf.stalk (f x)) :=
    IsLocalization.atUnits _ (f x).asIdeal.primeCompl
      (fun a ha => by aesop (add simp IsUnit.mem_submonoid_iff))
  have he : e.toRingEquiv.toCommRingCatIso.hom = StructureSheaf.toStalk k (f x) := by
    apply CommRingCat.hom_ext
    ext a
    exact e.commutes a
  let : IsIso (StructureSheaf.toStalk k (f x)) := by rw [← he]; infer_instance
  rw [Scheme.Hom.mem_smoothLocus]
  apply (RingHom.FormallySmooth.respectsIso.cancel_left_isIso
    (StructureSheaf.toStalk k (f x)) (f.stalkMap x)).mp
  exact Eq.mpr (congrArg (fun g : CommRingCat.of k ⟶ K => g.hom.FormallySmooth) hcomm) hfs

end Hironaka.Geometry.ProjectiveSecant
