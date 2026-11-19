import Hironaka.Analytic.Unibranch.HironakaG10TensorOperatorParameterLinearity

/-! # Parameter-linear maps from whole operator tensors -/
set_option autoImplicit false
open scoped TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10TensorOperatorLinear
open Hironaka.Analytic.Unibranch.HironakaG10TensorOperator
  Hironaka.Analytic.Unibranch.HironakaG10TensorOperatorParameterLinearity

/-- The actual tensor operator action as a linear map over the original
parameter algebra. -/
noncomputable def tensorOperatorLinear
    {Γ E F : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : Γ ⊗[ℂ] (E →L[ℂ] F)) : (Γ ⊗[ℂ] E) →ₗ[Γ] (Γ ⊗[ℂ] F) where
  toFun := tensorOperator T
  map_add' := (tensorOperator T).map_add
  map_smul' := tensorOperator_map_parameter_smul T

/-- Parameter-linear maps from a scalar-extension tensor are determined on
the original vectors embedded as 1⊗v. -/
theorem parameterLinear_ext_one_tmul
    {Γ E H : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup H] [Module Γ H]
    (L R : (Γ ⊗[ℂ] E) →ₗ[Γ] H)
    (h : ∀ v : E, L ((1 : Γ) ⊗ₜ[ℂ] v) = R ((1 : Γ) ⊗ₜ[ℂ] v)) : L = R := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  | tmul a v =>
    have he : (a ⊗ₜ[ℂ] v) = a • ((1 : Γ) ⊗ₜ[ℂ] v) := by
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [he, map_smul, map_smul, h]

end Hironaka.Analytic.Unibranch.HironakaG10TensorOperatorLinear
