import Hironaka.Algebra.ProjectiveSecantGeometricReduced
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Actual geometric reducedness of the original coefficient algebra survives localization
-/

noncomputable section

open scoped TensorProduct

namespace Hironaka.Algebra.ProjectiveSecant

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual original localizations retain geometric reducedness under the original compatible coefficient action. -/
theorem isGeometricallyReduced_of_isLocalization
    (k : Type u) (A B : Type v) [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    (M : Submonoid A) [IsLocalization M B] [Algebra.IsGeometricallyReduced k A] :
    Algebra.IsGeometricallyReduced k B := by
  rw [Algebra.isGeometricallyReduced_field_iff]
  let L := AlgebraicClosure k
  let : IsReduced (L ⊗[k] A) := (Algebra.isGeometricallyReduced_field_iff k A).mp inferInstance
  let F : L ⊗[k] A →ₐ[L] L ⊗[k] B :=
    Algebra.TensorProduct.map (AlgHom.id L L) (IsScalarTower.toAlgHom k A B)
  let : Algebra (L ⊗[k] A) (L ⊗[k] B) := F.toRingHom.toAlgebra
  let : IsScalarTower L (L ⊗[k] A) (L ⊗[k] B) := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (F.commutes x).symm)
  have H : (algebraMap (L ⊗[k] A) (L ⊗[k] B)).comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap A B) := by
    ext a
    change F ((1 : L) ⊗ₜ[k] a) = (1 : L) ⊗ₜ[k] algebraMap A B a
    simp only [F, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.toAlgHom_apply]
  let : IsLocalization (M.map (Algebra.TensorProduct.includeRight (R := k) (A := L))) (L ⊗[k] B) :=
    IsLocalization.tensorProduct_tensorProduct_right k L M B H
  exact isReduced_localizationPreserves
    (M.map (Algebra.TensorProduct.includeRight (R := k) (A := L))) (L ⊗[k] B) inferInstance

end Hironaka.Algebra.ProjectiveSecant
