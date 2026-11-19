import Hironaka.Analytic.Unibranch.HironakaG10CoefficientTensorOperator
import Hironaka.Analytic.Unibranch.HironakaG10TensorOperatorFaithful

/-! # Faithfulness of the Artinian coefficient model -/
set_option autoImplicit false
open scoped TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10CoefficientOperatorFaithful
open Hironaka.Analytic.Unibranch.HironakaG10TensorOperator
  Hironaka.Analytic.Unibranch.HironakaG10TensorOperatorFaithful
  Hironaka.Analytic.Unibranch.HironakaG10CoefficientTensorOperator
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients

/-- Transport to a finite coefficient model preserves the faithful action of
whole operator tensors: equality on all actual coefficient vectors detects
equality of the original operator jets. -/
theorem coefficientTensorOperator_injective
    {Γ E F ι : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ Γ) :
    Function.Injective (coefficientTensorOperator (E := E) (F := F) b) := by
  intro T S h
  apply tensorOperator_injective b
  apply LinearMap.ext
  intro x
  apply (parameterTensorEquiv (E := F) b).injective
  have h' := LinearMap.congr_fun h (parameterTensorEquiv (E := E) b x)
  change parameterTensorEquiv (E := F) b
      (tensorOperator T ((parameterTensorEquiv (E := E) b).symm ((parameterTensorEquiv (E := E) b) x))) =
    parameterTensorEquiv (E := F) b
      (tensorOperator S ((parameterTensorEquiv (E := E) b).symm ((parameterTensorEquiv (E := E) b) x))) at h'
  simpa only [LinearEquiv.symm_apply_apply] using h'

end Hironaka.Analytic.Unibranch.HironakaG10CoefficientOperatorFaithful
