import DeJongAlterations.Algebra.AdicCompletionEtale
import DeJongAlterations.Geometry.CompletedLocalRing
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Completed local rings of actual etale charts

The only field comparison premise concerns the native residue-field map of the
actual morphism. The completed-stalk map, its inverse, and coefficient identities
are constructed internally. No Noetherian or local-node-model hypothesis is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace DeJongAlterations.Geometry.CompletedLocalRingEtale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X Y : Scheme.{u}}

/-- The actual local algebra structure determined by a scheme stalk map. -/
abbrev stalkMapAlgebra (f : X ⟶ Y) (x : X) :
    Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
  (f.stalkMap x).hom.toAlgebra

/-- The actual stalk algebra map is local. -/
theorem stalkMap_isLocalHom (f : X ⟶ Y) (x : X) :
    letI := stalkMapAlgebra f x
    IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
  inferInstanceAs (IsLocalHom (f.stalkMap x).hom)

/-- Essential finite type is derived from the actual morphism. -/
theorem stalkMap_essFiniteType (f : X ⟶ Y) [Etale f] (x : X) :
    letI := stalkMapAlgebra f x
    Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
  LocallyOfFiniteType.stalkMap f x

/-- Formal unramifiedness is derived on the native stalk map. -/
theorem stalkMap_formallyUnramified (f : X ⟶ Y) [Etale f] (x : X) :
    letI := stalkMapAlgebra f x
    Algebra.FormallyUnramified (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
  FormallyUnramified.stalkMap f x

/-- Formal smoothness is derived from the actual smooth locus of the etale morphism. -/
theorem stalkMap_formallySmooth (f : X ⟶ Y) [Etale f] (x : X) :
    letI := stalkMapAlgebra f x
    Algebra.FormallySmooth (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
  change (f.stalkMap x).hom.FormallySmooth
  apply Scheme.Hom.mem_smoothLocus.mp
  rw [f.smoothLocus_eq_top]
  trivial

/-- The actual completed local map of an etale morphism; it uses no residue comparison. -/
def completedLocalRingMap (f : X ⟶ Y) [Etale f] (x : X) :
    Y.completedLocalRing (f x) →+* X.completedLocalRing x := by
  letI := stalkMapAlgebra f x
  letI := stalkMap_isLocalHom f x
  letI := stalkMap_essFiniteType f x
  letI := stalkMap_formallyUnramified f x
  exact Algebra.AdicCompletionEtale.completionMap

/-- The native residue-field map is the residue map of the actual local algebra. -/
theorem residueFieldMap_bijective (f : X ⟶ Y) (x : X) [IsIso (f.residueFieldMap x)] :
    letI := stalkMapAlgebra f x
    letI := stalkMap_isLocalHom f x
    Function.Bijective (IsLocalRing.ResidueField.map
      (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x))) :=
  ConcreteCategory.bijective_of_isIso (f.residueFieldMap x)

/-- An actual etale chart with unchanged native residue field has equivalent native completions. -/
def completedLocalRingEquiv (f : X ⟶ Y) [Etale f] (x : X)
    [IsIso (f.residueFieldMap x)] :
    Y.completedLocalRing (f x) ≃+* X.completedLocalRing x := by
  letI := stalkMapAlgebra f x
  letI := stalkMap_isLocalHom f x
  letI := stalkMap_essFiniteType f x
  letI := stalkMap_formallyUnramified f x
  letI := stalkMap_formallySmooth f x
  exact Algebra.AdicCompletionEtale.completedRingEquiv (residueFieldMap_bijective f x)

/-- The forward equivalence is exactly the original completed stalk map. -/
theorem completedLocalRingEquiv_toRingHom (f : X ⟶ Y) [Etale f] (x : X)
    [IsIso (f.residueFieldMap x)] :
    (completedLocalRingEquiv f x).toRingHom = completedLocalRingMap f x := by
  let := stalkMapAlgebra f x
  let := stalkMap_isLocalHom f x
  let := stalkMap_essFiniteType f x
  let := stalkMap_formallyUnramified f x
  let := stalkMap_formallySmooth f x
  exact Algebra.AdicCompletionEtale.completedRingEquiv_toRingHom (residueFieldMap_bijective f x)

@[simp]
theorem completedLocalRingMap_toCompletedLocalRing (f : X ⟶ Y) [Etale f]
    (x : X) (a : Y.presheaf.stalk (f x)) :
    completedLocalRingMap f x (Y.toCompletedLocalRing (f x) a) =
      X.toCompletedLocalRing x (f.stalkMap x a) := by
  let := stalkMapAlgebra f x
  let := stalkMap_isLocalHom f x
  let := stalkMap_essFiniteType f x
  let := stalkMap_formallyUnramified f x
  rw [Scheme.toCompletedLocalRing_apply, Scheme.toCompletedLocalRing_apply]
  exact Algebra.AdicCompletionEtale.completionMap_of a

@[simp]
theorem completedLocalRingEquiv_toCompletedLocalRing (f : X ⟶ Y) [Etale f]
    (x : X) [IsIso (f.residueFieldMap x)] (a : Y.presheaf.stalk (f x)) :
    completedLocalRingEquiv f x (Y.toCompletedLocalRing (f x) a) =
      X.toCompletedLocalRing x (f.stalkMap x a) := by
  change (completedLocalRingEquiv f x).toRingHom _ = _
  rw [completedLocalRingEquiv_toRingHom]
  exact completedLocalRingMap_toCompletedLocalRing f x a

/-- The completed-stalk equivalence preserves the actual original affine-base coefficients. -/
def completedLocalRingAlgEquiv (f : X ⟶ Y) [Etale f]
    {R : CommRingCat.{u}} (p : Y ⟶ Spec R) (x : X) [IsIso (f.residueFieldMap x)] :
    letI := Scheme.completedLocalRingAlgebra p (f x)
    letI := Scheme.completedLocalRingAlgebra (f ≫ p) x
    Y.completedLocalRing (f x) ≃ₐ[R] X.completedLocalRing x := by
  letI := Scheme.completedLocalRingAlgebra p (f x)
  letI := Scheme.completedLocalRingAlgebra (f ≫ p) x
  refine AlgEquiv.ofRingEquiv (f := completedLocalRingEquiv f x) ?_
  intro r
  rw [Scheme.algebraMap_completedLocalRingAlgebra,
    Scheme.algebraMap_completedLocalRingAlgebra,
    completedLocalRingEquiv_toCompletedLocalRing]
  congr 1
  exact DFunLike.congr_fun
    (CommRingCat.hom_ext_iff.mp (Scheme.baseToStalk_comp_stalkMap f p x)) r

@[simp]
theorem completedLocalRingAlgEquiv_toCompletedLocalRing (f : X ⟶ Y) [Etale f]
    {R : CommRingCat.{u}} (p : Y ⟶ Spec R) (x : X) [IsIso (f.residueFieldMap x)]
    (a : Y.presheaf.stalk (f x)) :
    completedLocalRingAlgEquiv f p x (Y.toCompletedLocalRing (f x) a) =
      X.toCompletedLocalRing x (f.stalkMap x a) :=
  completedLocalRingEquiv_toCompletedLocalRing f x a

end DeJongAlterations.Geometry.CompletedLocalRingEtale
