import Hironaka.Analytic.Unibranch.HironakaG10TensorOperator

/-! # Whole parameter linearity of tensor operator actions -/
set_option autoImplicit false
open scoped TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10TensorOperatorParameterLinearity
open Hironaka.Analytic.Unibranch.HironakaG10TensorOperator

/-- The whole tensor action of every operator-valued parameter tensor is
linear over the actual parameter algebra, not merely over the complex scalars. -/
theorem tensorOperator_map_parameter_smul
    {Γ E F : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : Γ ⊗[ℂ] (E →L[ℂ] F)) (a : Γ) (v : Γ ⊗[ℂ] E) :
    tensorOperator T (a • v) = a • tensorOperator T v := by
  induction T using TensorProduct.induction_on with
  | zero => simp
  | add T T' hT hT' => simp [map_add, hT, hT', smul_add]
  | tmul b A =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add v v' hv hv' => simp [map_add, smul_add, hv, hv']
    | tmul c v => simp [TensorProduct.smul_tmul', tensorOperator_tmul, mul_left_comm]

end Hironaka.Analytic.Unibranch.HironakaG10TensorOperatorParameterLinearity
