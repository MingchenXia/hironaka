import Hironaka.Analytic.Unibranch.HironakaG10TensorOperator
import Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
import Hironaka.Analytic.Unibranch.HironakaG10NormalizedBanachTaylor

/-! # Evaluation of the actual operator jet on an original Banach vector -/
set_option autoImplicit false
open Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10OperatorJetEvaluation
open Hironaka Hironaka
  Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
  Hironaka.Analytic.Unibranch.HironakaG10NormalizedBanachTaylor
  Hironaka.Analytic.Unibranch.HironakaG10TensorOperator

/-- Applying an operator tensor to the constant vector tensor is exactly
scalar extension of evaluation at the original vector. -/
theorem tensorOperator_apply_one
    {Γ E F : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : Γ ⊗[ℂ] (E →L[ℂ] F)) (v : E) :
    tensorOperator T ((1 : Γ) ⊗ₜ[ℂ] v) =
      (ContinuousLinearMap.apply ℂ F v).toLinearMap.baseChange Γ T := by
  induction T using TensorProduct.induction_on with
  | zero => simp
  | add T T' hT hT' => simp [map_add, hT, hT']
  | tmul a A => simp [tensorOperator_tmul, LinearMap.baseChange_tmul]

/-- The entire actual operator parameter jet acting on 1⊗v equals the
parameter jet of the actual evaluated family s ↦ A(s)v. -/
theorem operatorJet_apply_one
    {Γ E F : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Γ)
    (A : ComplexModel d → (E →L[ℂ] F))
    (hA : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ A z) (v : E) :
    tensorOperator (Γ := Γ) (E := E) (F := F)
      (banachJet (E := E →L[ℂ] F) d q φ A) ((1 : Γ) ⊗ₜ[ℂ] v) =
      banachJet d q φ (fun z => A z v) := by
  rw [tensorOperator_apply_one]
  symm
  exact banachJet_map d q φ A
    ((has_normalized_powerSeriesAt A hA).analyticAt.contDiffAt) (ContinuousLinearMap.apply ℂ F v)

end Hironaka.Analytic.Unibranch.HironakaG10OperatorJetEvaluation
