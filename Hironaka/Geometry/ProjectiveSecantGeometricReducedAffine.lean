import Hironaka.Algebra.ProjectiveSecantGeometricReducedLocalization
import Hironaka.Geometry.ProjectiveSecantGeometricOpen
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Actual native geometric reducedness on an affine original coefficient map supplies the original ring property
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

namespace Hironaka.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal native original affine coefficient morphism internally supplies geometric reducedness of the same actual original ring algebra. -/
theorem isGeometricallyReduced_algebra_of_spec
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    [GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap k A)))] :
    Algebra.IsGeometricallyReduced k A := by
  rw [Algebra.isGeometricallyReduced_field_iff]
  let L := AlgebraicClosure k
  let f := Spec.map (CommRingCat.ofHom (algebraMap k A))
  let g := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let : AlgebraicGeometry.IsReduced (pullback f g) :=
    GeometricallyReduced.geometrically_isReduced g _ _ (.of_hasPullback _ _)
  let : AlgebraicGeometry.IsReduced (Spec (CommRingCat.of (A ⊗[k] L))) :=
    isReduced_of_isOpenImmersion (pullbackSpecIso k A L).inv
  let : _root_.IsReduced (A ⊗[k] L) := (affine_isReduced_iff (CommRingCat.of (A ⊗[k] L))).mp inferInstance
  exact isReduced_of_injective (Algebra.TensorProduct.comm k L A).toRingHom
    (Algebra.TensorProduct.comm k L A).injective

end Hironaka.Geometry.ProjectiveSecant
