import Hironaka.Geometry.QuotGrassmannPivotNativeLocalizedPoint
import Mathlib.RingTheory.LocalProperties.Submodule

/-! Unit-ideal principal localizations detect the entire original native quotient. -/

noncomputable section

open TensorProduct

namespace Hironaka.Geometry.QuotGrassmann

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  {V : Type v} [AddCommGroup V] [Module R V]

/-- The whole original native base-change quotient on the actual scalar image of every
original tensor is the canonical scalar image of its original quotient class. -/
theorem originalNativeGrassmannian_baseChangeMkQ_scalar
    (P : Submodule A (A ⊗[R] V)) (x : A ⊗[R] V) :
    Module.Grassmannian.baseChangeMkQ B P
        (TensorProduct.map (IsScalarTower.toAlgHom R A B).toLinearMap
          (LinearMap.id : V →ₗ[R] V) x) =
      (1 : B) ⊗ₜ[A] P.mkQ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, IsScalarTower.toAlgHom_apply,
      LinearMap.id_apply, Module.Grassmannian.baseChangeMkQ, LinearMap.comp_apply,
      LinearEquiv.coe_coe, AlgebraTensorModule.cancelBaseChange_symm_tmul,
      LinearMap.baseChange_tmul]
    rw [show (a ⊗ₜ[R] v : A ⊗[R] V) = a • ((1 : A) ⊗ₜ[R] v) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
    rw [map_smul, TensorProduct.tmul_smul]
    rw [TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
  | add x y hx hy => simp only [map_add, hx, hy, TensorProduct.tmul_add]

/-- A unit-ideal principal family detects equality of the SAME entire original native
Grassmannian points, over arbitrary commutative rings and original modules. -/
theorem originalNativeGrassmannian_eq_of_principal_localizations
    {r : ℕ} (s : Set A) (hspan : Ideal.span s = ⊤)
    (N P : Module.Grassmannian A (A ⊗[R] V) r)
    (h : ∀ g ∈ s,
      Module.Grassmannian.map (IsScalarTower.toAlgHom R A (Localization.Away g)) N =
        Module.Grassmannian.map (IsScalarTower.toAlgHom R A (Localization.Away g)) P) : N = P := by
  have hle (N P : Module.Grassmannian A (A ⊗[R] V) r)
      (h : ∀ g ∈ s,
        Module.Grassmannian.map (IsScalarTower.toAlgHom R A (Localization.Away g)) N =
          Module.Grassmannian.map (IsScalarTower.toAlgHom R A (Localization.Away g)) P) :
      N.toSubmodule ≤ P.toSubmodule := by
    intro x hx
    apply (Submodule.Quotient.mk_eq_zero P.toSubmodule).mp
    apply Module.eq_zero_of_isLocalized_span s hspan
      (fun g : s => Localization.Away g.val ⊗[A] ((A ⊗[R] V) ⧸ P.toSubmodule))
      (fun g : s => TensorProduct.mk A (Localization.Away g.val)
        ((A ⊗[R] V) ⧸ P.toSubmodule) 1)
    intro g
    let y := TensorProduct.map
      (IsScalarTower.toAlgHom R A (Localization.Away g.val)).toLinearMap
      (LinearMap.id : V →ₗ[R] V) x
    have hy : y ∈ (Module.Grassmannian.map
        (IsScalarTower.toAlgHom R A (Localization.Away g.val)) N).toSubmodule := by
      rw [originalNativeGrassmannian_map_canonical_toSubmodule]
      change Module.Grassmannian.baseChangeMkQ (Localization.Away g.val) N.toSubmodule y = 0
      rw [originalNativeGrassmannian_baseChangeMkQ_scalar]
      simp only [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N.toSubmodule).mpr hx,
        TensorProduct.tmul_zero]
    rw [h g.val g.property, originalNativeGrassmannian_map_canonical_toSubmodule] at hy
    change Module.Grassmannian.baseChangeMkQ (Localization.Away g.val) P.toSubmodule y = 0 at hy
    rw [originalNativeGrassmannian_baseChangeMkQ_scalar] at hy
    exact hy
  apply Module.Grassmannian.ext
  exact le_antisymm (hle N P h) (hle P N (fun g hg => (h g hg).symm))

end Hironaka.Geometry.QuotGrassmann
