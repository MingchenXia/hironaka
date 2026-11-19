import Hironaka.Analytic.Unibranch.HironakaG10TensorOperator
import Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! # Faithful action of finite-coefficient operator tensors -/
set_option autoImplicit false
open scoped TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10TensorOperatorFaithful
open Hironaka.Analytic.Unibranch.HironakaG10TensorOperator
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients

/-- The actual coefficient of the operator-tensor action on 1⊗v is the
corresponding actual operator coefficient applied to v. -/
theorem tensorOperator_apply_one_coordinate
    {Γ E F ι : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ Γ)
    (T : Γ ⊗[ℂ] (E →L[ℂ] F)) (v : E) (i : ι) :
    parameterTensorEquiv (E := F) b
      (tensorOperator (Γ := Γ) (E := E) (F := F) T ((1 : Γ) ⊗ₜ[ℂ] v)) i =
      (parameterTensorEquiv (E := E →L[ℂ] F) b T i) v := by
  induction T using TensorProduct.induction_on with
  | zero => simp
  | add T T' hT hT' => simp [map_add, hT, hT']
  | tmul a A => simp [tensorOperator_tmul, parameterTensorEquiv_tmul]

/-- The actual action of whole operator tensors is faithful for any finite
complex basis of the parameter algebra. -/
theorem tensorOperator_injective
    {Γ E F ι : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ Γ) :
    Function.Injective (tensorOperator (Γ := Γ) (E := E) (F := F)) := by
  intro T S hTS
  apply (parameterTensorEquiv (E := E →L[ℂ] F) b).injective
  ext i v
  have h := congrArg (fun L : (Γ ⊗[ℂ] E) →ₗ[ℂ] (Γ ⊗[ℂ] F) =>
    parameterTensorEquiv (E := F) b (L ((1 : Γ) ⊗ₜ[ℂ] v)) i) hTS
  simpa only [tensorOperator_apply_one_coordinate] using h

end Hironaka.Analytic.Unibranch.HironakaG10TensorOperatorFaithful
