import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# The SAME actual unramified morphism is locally quasi-finite, and finite if proper

This is the consumer after genuine singular-locus unramifiedness, not a
construction of the intrinsic relative singular subscheme. No integrality,
flatness, normality or Noetherian hypothesis is imposed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.RelativeUnramified

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Actual original affine ring maps make the SAME original morphism locally quasi-finite. -/
theorem locallyQuasiFinite [LocallyOfFiniteType f] [FormallyUnramified f] :
    LocallyQuasiFinite f where
  quasiFinite_appLE {U} hU {V} hV e := by
    have hft := f.finiteType_appLE hU hV e
    have hfu := f.formallyUnramified_appLE hU hV e
    algebraize [(f.appLE _ _ e).hom]
    exact inferInstanceAs (Algebra.QuasiFinite _ _)

/-- Native properness plus actual unramifiedness gives finiteness of the SAME original map. -/
theorem isFinite [IsProper f] [FormallyUnramified f] : IsFinite f := by
  let : LocallyQuasiFinite f := locallyQuasiFinite f
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

/-- Finiteness uses the ENTIRE actual canonical original residue-field action. -/
theorem pointResidue_finite [LocallyOfFiniteType f] [FormallyUnramified f] (x : X) :
    letI : Algebra (S.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    Module.Finite (S.residueField (f x)) (X.residueField x) := by
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (S.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
  have : Algebra.EssFiniteType (S.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  have : Algebra.FormallyUnramified (S.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact FormallyUnramified.stalkMap f x
  suffices h : Module.Finite
      (IsLocalRing.ResidueField <| S.presheaf.stalk (f x))
      (IsLocalRing.ResidueField <| X.presheaf.stalk x) by
    convert! h
    apply Module.ext
    funext a b
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective b
    rfl
  infer_instance

/-- The finite residue extension and separability use the SAME original canonical action. -/
theorem pointResidue_finite_separable [LocallyOfFiniteType f] [FormallyUnramified f] (x : X) :
    letI : Algebra (S.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    Module.Finite (S.residueField (f x)) (X.residueField x) ∧
      Algebra.IsSeparable (S.residueField (f x)) (X.residueField x) :=
  ⟨pointResidue_finite f x, inferInstance⟩

end Hironaka.Geometry.RelativeUnramified
