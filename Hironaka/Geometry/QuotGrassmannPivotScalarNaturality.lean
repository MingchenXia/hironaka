import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Actual original regular coefficients along the original native spectrum map

This is the native structural-ring identity on every original inverse-image
open, with the same original ring homomorphism and coefficient.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual native affine coefficient ring homomorphism, in its original structure-sheaf spelling. -/
def originalAffineCoefficientMap (B : Type u) [CommRing B] (U : (Spec (.of B)).Opens) :
    B →+* Γ(Spec (.of B), U) :=
  algebraMap B ((Spec.structureSheaf B).presheaf.obj (.op U))

/-- The actual spectrum morphism sends each original coefficient section to its exact original image. -/
theorem originalSpecMap_coefficient {B H : Type u} [CommRing B] [CommRing H]
    (φ : B →+* H) (b : B) (U : (Spec (.of B)).Opens) :
    (Spec.map (CommRingCat.ofHom φ)).app U (originalAffineCoefficientMap B U b) =
      originalAffineCoefficientMap H ((Spec.map (CommRingCat.ofHom φ)) ⁻¹ᵁ U) (φ b) := by
  exact ConcreteCategory.congr_hom (StructureSheaf.toOpen_comp_comap φ U) b

end Hironaka.Geometry.QuotGrassmann
