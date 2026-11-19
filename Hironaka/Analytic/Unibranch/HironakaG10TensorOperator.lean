import Hironaka.Analytic.Unibranch.HironakaG10TensorBilinearExtension

/-! # Actual action of parameter-tensor operator jets on parameter tensors -/
set_option autoImplicit false
open scoped TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10TensorOperator
open Hironaka.Analytic.Unibranch.HironakaG10TensorBilinearExtension

/-- Forget continuity while retaining the actual complex-linear operator. -/
noncomputable def continuousLinearUnderlying {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] :
    (E →L[ℂ] F) →ₗ[ℂ] (E →ₗ[ℂ] F) where
  toFun T := T.toLinearMap
  map_add' T S := by ext x; rfl
  map_smul' c T := by ext x; rfl

/-- The actual action of an operator-valued parameter tensor on a vector-valued
parameter tensor, retaining the whole algebraic tensor products. -/
noncomputable def tensorOperator {Γ E F : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] :
    (Γ ⊗[ℂ] (E →L[ℂ] F)) →ₗ[ℂ] ((Γ ⊗[ℂ] E) →ₗ[ℂ] (Γ ⊗[ℂ] F)) :=
  (TensorProduct.homTensorHomMap (RingHom.id ℂ) Γ E Γ F).comp
    (TensorProduct.map (LinearMap.mul ℂ Γ) continuousLinearUnderlying)

/-- On pure tensors, the operator action multiplies the parameter coefficients
and applies the original bounded operator. -/
theorem tensorOperator_tmul {Γ E F : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (a b : Γ) (T : E →L[ℂ] F) (v : E) :
    tensorOperator (a ⊗ₜ[ℂ] T) (b ⊗ₜ[ℂ] v) = (a*b) ⊗ₜ[ℂ] T v := by
  rfl

end Hironaka.Analytic.Unibranch.HironakaG10TensorOperator
