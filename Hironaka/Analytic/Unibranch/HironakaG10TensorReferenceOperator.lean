import Hironaka.Analytic.Unibranch.HironakaG10TensorOperator
import Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators

/-! # The actual reference operators in the finite coefficient model -/
set_option autoImplicit false
open scoped TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10TensorReferenceOperator
open Hironaka.Analytic.Unibranch.HironakaG10TensorOperator
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators

/-- The tensor of a fixed original operator with 1 acts exactly as the
coefficientwise operator on the actual finite coefficient Banach model. -/
theorem tensorOperator_one_coefficientCLM
    {Γ E F ι : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ Γ) (T : E →L[ℂ] F)
    (v : ι → E) :
    parameterTensorEquiv b (tensorOperator ((1 : Γ) ⊗ₜ[ℂ] T) ((parameterTensorEquiv b).symm v)) =
      coefficientCLM T v := by
  obtain ⟨z,rfl⟩ := (parameterTensorEquiv (E := E) b).surjective v
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' =>
    simp only [LinearEquiv.symm_apply_apply] at hz hz'
    simp [map_add, hz, hz']
  | tmul a x =>
    ext i
    simp [tensorOperator_tmul, parameterTensorEquiv_tmul]

end Hironaka.Analytic.Unibranch.HironakaG10TensorReferenceOperator
