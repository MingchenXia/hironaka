import Hironaka.Geometry.QuotGrassmannPivotNativePrincipalCover
import Hironaka.Algebra.PluckerQuotTransitionLocalizationTensor

/-!
# SAME entire original localized quotient is the actual native point base change

Both the original ambient tensor source and the original native quotient
target are retained, with an internally proved whole-map comparison.
-/

noncomputable section

open TensorProduct

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuotTransition

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual native functor along the ORIGINAL algebra map uses the SAME original canonical scalar structure; the dependent tensor-target transport is derived from equality of those actual algebra structures. -/
theorem originalNativeGrassmannian_map_canonical_toSubmodule
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    {V : Type v} [AddCommGroup V] [Module R V] {r : ℕ}
    (N : Module.Grassmannian A (A ⊗[R] V) r) :
    (Module.Grassmannian.map (IsScalarTower.toAlgHom R A B) N).toSubmodule =
      (Module.Grassmannian.baseChangeMkQ B N.toSubmodule).ker := by
  let P := {a : Algebra A B // letI : Algebra A B := a; IsScalarTower R A B}
  let F : P → Submodule B (B ⊗[R] V) := fun a =>
    letI : Algebra A B := a.val
    letI : IsScalarTower R A B := a.property
    (Module.Grassmannian.baseChangeMkQ B N.toSubmodule).ker
  let f := IsScalarTower.toAlgHom R A B
  let a₁ : P := ⟨f.toAlgebra, by
    let : Algebra A B := f.toAlgebra
    exact IsScalarTower.of_algebraMap_eq' (by ext x; exact (f.commutes x).symm)⟩
  let a₂ : P := ⟨inferInstance, inferInstance⟩
  have hA : f.toAlgebra = (inferInstance : Algebra A B) := toAlgebra_algebraMap
  have ha : a₁ = a₂ := Subtype.ext hA
  change F a₁ = F a₂
  exact congrArg F ha

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (S : Submonoid A)
  (E : Type v) [Fintype E] [DecidableEq E] (r : ℕ)

/-- The WHOLE SAME localized original quotient, with original ambient tensor source, is the actual native Grassmannian base-change quotient under its actual native localized-target isomorphism. -/
theorem originalNativeGrassmannianLocalizedQuotient_tensor_triangle
    (N : Module.Grassmannian A (A ⊗[R] (E → R)) r) :
    (originalLocalizedCoordinateQuotient
      (originalNativeGrassmannianCoordinateQuotient R A E r N) S).comp
        (TensorProduct.piScalarRight R (Localization S) (Localization S) E).toLinearMap =
      (LocalizedModule.equivTensorProduct S ((A ⊗[R] (E → R)) ⧸ N.toSubmodule)).symm.toLinearMap.comp
        (Module.Grassmannian.baseChangeMkQ (Localization S) N.toSubmodule) := by
  have h := originalLocalizedCoordinateQuotient_originalTensor_triangle R A S E
    (originalNativeGrassmannianCoordinateQuotient R A E r N)
  rw [originalNativeGrassmannianCoordinateQuotient_tensor_triangle] at h
  exact h

/-- The ENTIRE submodule of the actual native functor image under original localization is the kernel of SAME original localized quotient, without a supplied kernel comparison. -/
theorem originalNativeGrassmannian_localization_map_toSubmodule
    (N : Module.Grassmannian A (A ⊗[R] (E → R)) r) :
    (Module.Grassmannian.map (IsScalarTower.toAlgHom R A (Localization S)) N).toSubmodule =
      ((originalLocalizedCoordinateQuotient
        (originalNativeGrassmannianCoordinateQuotient R A E r N) S).comp
          (TensorProduct.piScalarRight R (Localization S) (Localization S) E).toLinearMap).ker := by
  rw [originalNativeGrassmannian_map_canonical_toSubmodule,
    originalNativeGrassmannianLocalizedQuotient_tensor_triangle R A S E r N,
    LinearEquiv.ker_comp]

end Hironaka.Geometry.QuotGrassmann
