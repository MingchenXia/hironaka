import Hironaka.Analytic.Unibranch.HironakaG10TensorOperator
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! # Actual composition of parameter-tensor operator actions -/
set_option autoImplicit false
open scoped TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10TensorOperatorComposition
open Hironaka.Analytic.Unibranch.HironakaG10TensorBilinearExtension
  Hironaka.Analytic.Unibranch.HironakaG10TensorOperator

/-- The action of a whole tensor of composed operators is exactly the
composition of the corresponding whole tensor actions. -/
theorem tensorOperator_comp {Γ E F G : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (A : Γ ⊗[ℂ] (F →L[ℂ] G)) (B : Γ ⊗[ℂ] (E →L[ℂ] F)) :
    tensorOperator (Γ := Γ) (E := E) (F := G)
      (tensorBilinear (Γ := Γ) (E := F →L[ℂ] G) (F := E →L[ℂ] F) (G := E →L[ℂ] G)
        (ContinuousLinearMap.compL ℂ E F G) A B) =
      (tensorOperator (Γ := Γ) (E := F) (F := G) A).comp
        (tensorOperator (Γ := Γ) (E := E) (F := F) B) := by
  induction A using TensorProduct.induction_on with
  | zero => simp
  | add A A' hA hA' => simp [map_add, LinearMap.add_comp, hA, hA']
  | tmul a A =>
    induction B using TensorProduct.induction_on with
    | zero => simp
    | add B B' hB hB' => simp [map_add, LinearMap.comp_add, hB, hB']
    | tmul b B =>
      apply LinearMap.ext
      intro v
      induction v using TensorProduct.induction_on with
      | zero => simp
      | add v v' hv hv' => simp [map_add, hv, hv']
      | tmul c v =>
        simp only [tensorBilinear_tmul, ContinuousLinearMap.compL_apply,
          tensorOperator_tmul, LinearMap.comp_apply, ContinuousLinearMap.comp_apply, mul_assoc]

/-- The parameter tensor of the identity acts as the whole identity map. -/
theorem tensorOperator_one_id {Γ E : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] :
    tensorOperator ((1 : Γ) ⊗ₜ[ℂ] ContinuousLinearMap.id ℂ E) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v v' hv hv' => simp [map_add, hv, hv']
  | tmul a v => simp [tensorOperator_tmul]

end Hironaka.Analytic.Unibranch.HironakaG10TensorOperatorComposition
