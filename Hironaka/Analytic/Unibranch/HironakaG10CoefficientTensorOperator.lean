import Hironaka.Analytic.Unibranch.HironakaG10TensorOperatorComposition
import Hironaka.Analytic.Unibranch.HironakaG10TensorReferenceOperator

/-! # Whole operator-tensor actions in the finite coefficient model -/
set_option autoImplicit false
open scoped TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10CoefficientTensorOperator
open Hironaka.Analytic.Unibranch.HironakaG10TensorBilinearExtension
  Hironaka.Analytic.Unibranch.HironakaG10TensorOperator
  Hironaka.Analytic.Unibranch.HironakaG10TensorOperatorComposition
  Hironaka.Analytic.Unibranch.HironakaG10TensorReferenceOperator
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators

/-- The actual whole operator-tensor action transported to the finite
coefficient model. -/
noncomputable def coefficientTensorOperator
    {Γ E F ι : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ Γ)
    (T : Γ ⊗[ℂ] (E →L[ℂ] F)) : (ι → E) →ₗ[ℂ] (ι → F) :=
  (parameterTensorEquiv (E := F) b).toLinearMap.comp
    ((tensorOperator (Γ := Γ) (E := E) (F := F) T).comp
      (parameterTensorEquiv (E := E) b).symm.toLinearMap)

/-- Transport of a constant tensor is the actual coefficientwise reference
operator used by the Artinian Schur construction. -/
theorem coefficientTensorOperator_one
    {Γ E F ι : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ Γ) (T : E →L[ℂ] F) :
    coefficientTensorOperator b ((1 : Γ) ⊗ₜ[ℂ] T) = (coefficientCLM T).toLinearMap := by
  apply LinearMap.ext
  intro v
  exact tensorOperator_one_coefficientCLM b T v

/-- Transport of an actual operator-tensor product is actual composition
on all finite coefficient vectors. -/
theorem coefficientTensorOperator_comp
    {Γ E F G ι : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ Γ) (A : Γ ⊗[ℂ] (F →L[ℂ] G)) (B : Γ ⊗[ℂ] (E →L[ℂ] F)) :
    coefficientTensorOperator (E := E) (F := G) b
      (tensorBilinear (Γ := Γ) (E := F →L[ℂ] G) (F := E →L[ℂ] F) (G := E →L[ℂ] G)
        (ContinuousLinearMap.compL ℂ E F G) A B) =
      (coefficientTensorOperator (E := F) (F := G) b A).comp
        (coefficientTensorOperator (E := E) (F := F) b B) := by
  apply LinearMap.ext
  intro v
  simp only [coefficientTensorOperator, LinearMap.comp_apply, tensorOperator_comp]
  change parameterTensorEquiv (E := G) b
      (tensorOperator A (tensorOperator B ((parameterTensorEquiv (E := E) b).symm v))) =
    parameterTensorEquiv (E := G) b
      (tensorOperator A ((parameterTensorEquiv (E := F) b).symm
        (parameterTensorEquiv (E := F) b
          (tensorOperator B ((parameterTensorEquiv (E := E) b).symm v)))))
  rw [LinearEquiv.symm_apply_apply]

end Hironaka.Analytic.Unibranch.HironakaG10CoefficientTensorOperator
