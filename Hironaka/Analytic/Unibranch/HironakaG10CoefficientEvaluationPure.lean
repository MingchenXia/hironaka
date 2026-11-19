import Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix

/-! # Point evaluation of the original vector inside the coefficient model -/
set_option autoImplicit false
open scoped TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10CoefficientEvaluationPure
open Hironaka.HironakaG10FlatPolydiscAlgebra
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix

/-- Point evaluation of 1⊗v is the actual scalar point evaluation of v,
included into the original parameter algebra. -/
theorem coefficientEvaluation_one_tmul
    {Q X r ι : Type*} [NormedCommRing Q] [NormedAlgebra ℂ Q]
    [FiniteDimensional ℂ Q] [NormedAddCommGroup X] [NormedSpace ℂ X]
    {K : Set X} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ Q)
    (z : K) (v : r → holSubalgebra K) (j : r) :
    letI := parameterCoefficientModule (E := r → holSubalgebra K) b
    coefficientEvaluation b z (parameterTensorEquiv b ((1 : Q) ⊗ₜ[ℂ] v)) j =
      algebraMap ℂ Q (((v j : holSubalgebra K) : C(K,ℂ)) z) := by
  let := parameterCoefficientModule (E := r → holSubalgebra K) b
  change (scalarEvaluation (Q := Q) (r := r) z).liftBaseChange Q
    ((parameterTensorEquiv (E := r → holSubalgebra K) b).symm
      (parameterTensorEquiv b ((1 : Q) ⊗ₜ[ℂ] v))) j = _
  simp only [LinearEquiv.symm_apply_apply, LinearMap.liftBaseChange_tmul, scalarEvaluation,
    LinearMap.coe_mk, AddHom.coe_mk, one_smul]

end Hironaka.Analytic.Unibranch.HironakaG10CoefficientEvaluationPure
