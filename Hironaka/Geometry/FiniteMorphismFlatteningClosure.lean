import Hironaka.Geometry.ModuleFlattening
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Fiber

/-!
# The actual global generic-fibre closure of a base-changed finite morphism

The transform is the native scheme-theoretic image, retaining all original
nilpotents. Its native closed immersion, finite structure map, factorization
and exact topological closure are constructed without gluing witnesses.
Flatness requires the separate comparison with the actual affine algebra
images and is not asserted merely from this global construction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka.Geometry.FiniteMorphismFlattening

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]

/-- The literal original finite morphism, with its original algebra coefficients. -/
abbrev originalMap : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R A))

instance originalMap_isFinite [Module.Finite R A] : IsFinite (originalMap R A) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- The actual base change of the original affine finite morphism to the literal blowup. -/
abbrev baseChanged (I : Ideal R) : Scheme :=
  pullback (affineBlowupStructure I) (originalMap R A)

/-- The actual base-changed original finite morphism to the actual blowup. -/
abbrev baseChangedMap (I : Ideal R) : baseChanged R A I ⟶ affineBlowup I :=
  pullback.fst _ _

/-- The original coefficient map from the actual base change to the original base. -/
abbrev baseChangedToBase (I : Ideal R) : baseChanged R A I ⟶ Spec (CommRingCat.of R) :=
  baseChangedMap R A I ≫ affineBlowupStructure I

/-- The actual inclusion of the actual generic fibre of the base-changed original morphism. -/
abbrev genericFiberInclusion (I : Ideal R) :=
  (baseChangedToBase R A I).fiberι (genericPoint (Spec (CommRingCat.of R)))

instance genericFiberInclusion_isAffineHom (I : Ideal R) :
    IsAffineHom (genericFiberInclusion R A I) := by
  change IsAffineHom (pullback.fst _ _)
  have : IsAffineHom ((Spec (CommRingCat.of R)).fromSpecResidueField
      (genericPoint (Spec (CommRingCat.of R)))) := isAffineHom_of_isAffine _
  exact MorphismProperty.pullback_fst _ _ this

/-- The literal native closed generic-fibre transform inside the actual original base change. -/
abbrev globalTransform (I : Ideal R) : Scheme := (genericFiberInclusion R A I).image

/-- The actual closed immersion of the transform in the original base-changed scheme. -/
abbrev globalTransformInclusion (I : Ideal R) :
    globalTransform R A I ⟶ baseChanged R A I := (genericFiberInclusion R A I).imageι

/-- The actual structure map of the global closed generic-fibre transform. -/
abbrev globalTransformMap (I : Ideal R) : globalTransform R A I ⟶ affineBlowup I :=
  globalTransformInclusion R A I ≫ baseChangedMap R A I

instance globalTransformInclusion_isClosedImmersion (I : Ideal R) :
    IsClosedImmersion (globalTransformInclusion R A I) := inferInstance

/-- Global finiteness uses the original finite map, its actual base change, and the actual closed immersion. -/
instance globalTransformMap_isFinite [Module.Finite R A] (I : Ideal R) :
    IsFinite (globalTransformMap R A I) := inferInstance

/-- The actual generic fibre factors through its actual global transform. -/
@[reassoc (attr := simp)]
theorem genericFiber_toImage_inclusion (I : Ideal R) :
    (genericFiberInclusion R A I).toImage ≫ globalTransformInclusion R A I =
      genericFiberInclusion R A I := Scheme.Hom.toImage_imageι _

/-- The original generic fibre has dense image in the actual constructed transform. -/
theorem genericFiber_toImage_isDominant (I : Ideal R) :
    IsDominant (genericFiberInclusion R A I).toImage := inferInstance

/-- Exact support: the actual closed transform is the closure of the original generic fibre. -/
theorem globalTransformInclusion_range (I : Ideal R) :
    Set.range (globalTransformInclusion R A I) =
      closure (Set.range (genericFiberInclusion R A I)) := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker]

end Hironaka.Geometry.FiniteMorphismFlattening
