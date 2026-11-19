import Hironaka.Geometry.QuotGrassmannPivotTildeCoefficients
import Hironaka.Geometry.QuotGrassmannPivotMatrixSeparation

/-!
# True native affine pullback of the same original finite matrix sheaf map

Both sides are actual native sheaf morphisms, using the true native pullback
functor and the original entrywise coefficient map. No base-change or
flatness certificate, nor an open-immersion hypothesis, is supplied.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- True native pullback of the original actual finite matrix map is exactly the same original
entrywise coefficient matrix map, preserving both original free indices. -/
theorem originalMatrixQuotientSheaf_pullback {B H : Type u} [CommRing B] [CommRing H]
    (φ : B →+* H) {I E : Type u} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]
    (M : Matrix I E B) :
    originalPullbackFreeHom (Spec.map (CommRingCat.ofHom φ)) (originalMatrixQuotientSheaf B M) =
      originalMatrixQuotientSheaf H (M.map φ) := by
  let f := Spec.map (CommRingCat.ofHom φ)
  apply originalFreeHomCoefficient_ext_eq_top (Spec (.of H)) (f ⁻¹ᵁ ⊤) (Scheme.Hom.preimage_top f)
  intro j i
  calc
    _ = f.app ⊤ ((originalFreeHomCoefficient (originalMatrixQuotientSheaf B M) j i).val.app
        (.op ⊤) (1 : Γ(Spec (.of B), ⊤))) :=
      originalPullbackFreeHom_coefficient_one f _ j i ⊤
    _ = f.app ⊤ (originalAffineCoefficientMap B ⊤ (M i j)) :=
      congrArg (f.app ⊤) (originalMatrixQuotientSheaf_coefficient_one B M i j ⊤)
    _ = originalAffineCoefficientMap H (f ⁻¹ᵁ ⊤) (φ (M i j)) :=
      originalSpecMap_coefficient φ (M i j) ⊤
    _ = _ := (originalMatrixQuotientSheaf_coefficient_one H (M.map φ) i j (f ⁻¹ᵁ ⊤)).symm

end Hironaka.Geometry.QuotGrassmann
