import Hironaka.Geometry.QuotGrassmannPivotTildeCoordinates
import Hironaka.Geometry.QuotGrassmannPivotScalarNaturality

/-!
# Actual regular-function coefficients of the originally constructed matrix sheaf

The native original coordinate endomorphism is evaluated at one on every
actual original affine open. Its value is precisely the same original
matrix entry as an actual native regular function.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (B : Type u) [CommRing B]

/-- The original native scalar section map is literally the original coefficient-ring section map. -/
theorem originalTildeSelf_toOpen (U : (Spec (.of B)).Opens) (b : B) :
    tilde.toOpen (R := CommRingCat.of B) (ModuleCat.of B B) U b =
      originalAffineCoefficientMap B U b := rfl

/-- The actual native tilde scalar endomorphism has the same original regular-function coefficient. -/
theorem originalTildeScalarEnd_one (b : B) (U : (Spec (.of B)).Opens) :
    (tilde.map (R := CommRingCat.of B) (ModuleCat.ofHom (LinearMap.mulLeft B b))).val.app
      (.op U) (1 : Γ(Spec (.of B), U)) = originalAffineCoefficientMap B U b := by
  let m := ModuleCat.ofHom (LinearMap.mulLeft B b)
  have h := ConcreteCategory.congr_hom (tilde.toOpen_map_app (R := CommRingCat.of B) m U) (1 : B)
  change (tilde.map m).val.app (.op U)
      (tilde.toOpen (R := CommRingCat.of B) (ModuleCat.of B B) U (1 : B)) =
    tilde.toOpen (R := CommRingCat.of B) (ModuleCat.of B B) U (b * 1) at h
  have hmone : originalAffineCoefficientMap B U (1 : B) = (1 : Γ(Spec (.of B), U)) :=
    map_one (originalAffineCoefficientMap B U)
  have hone : tilde.toOpen (R := CommRingCat.of B) (ModuleCat.of B B) U (1 : B) =
      (1 : Γ(Spec (.of B), U)) :=
    (originalTildeSelf_toOpen B U 1).trans hmone
  rw [hone, mul_one] at h
  exact h.trans (originalTildeSelf_toOpen B U b)

/-- Every coefficient of the same original native matrix sheaf is its precise original regular function. -/
theorem originalMatrixQuotientSheaf_coefficient_one {I E : Type u}
    [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]
    (M : Matrix I E B) (i : I) (j : E) (U : (Spec (.of B)).Opens) :
    (originalFreeHomCoefficient (originalMatrixQuotientSheaf B M) j i).val.app (.op U)
      (1 : Γ(Spec (.of B), U)) = originalAffineCoefficientMap B U (M i j) := by
  have h := congrArg (fun m : End (SheafOfModules.unit (Spec (.of B)).ringCatSheaf) ↦
    m.val.app (.op U) (1 : Γ(Spec (.of B), U)))
      (originalMatrixQuotientSheaf_coefficient B M i j)
  exact h.trans (originalTildeScalarEnd_one B (M i j) U)

end Hironaka.Geometry.QuotGrassmann
