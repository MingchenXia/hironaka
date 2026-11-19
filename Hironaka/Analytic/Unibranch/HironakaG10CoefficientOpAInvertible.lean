import Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators
import Hironaka.Resolution.HironakaG10LocDirectPersistence
set_option autoImplicit false
namespace Hironaka.Analytic.Unibranch.HironakaG10CoefficientOpAInvertible
open Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
  Hironaka.HironakaG10LocDirectPersistence
noncomputable section

theorem coefficientCLM_invertible_and_inverse
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype ι]
    (T : E →L[ℂ] E) (hT : T.IsInvertible) :
    (coefficientCLM (ι := ι) T).IsInvertible ∧
      (coefficientCLM (ι := ι) T).inverse = coefficientCLM T.inverse := by
  have hcoeff : (coefficientCLM (ι := ι) T).IsInvertible := by
    obtain ⟨e,he⟩ := hT
    refine ⟨ContinuousLinearEquiv.piCongrRight (fun _ : ι => e), ?_⟩
    ext v i
    exact congrArg (fun f : E →L[ℂ] E => f (v i)) he
  refine ⟨hcoeff, ?_⟩
  ext v i
  have heq := hcoeff.self_apply_inverse v
  have hpoint := congrFun heq i
  change T (((coefficientCLM (ι := ι) T).inverse v) i) = v i at hpoint
  apply hT.injective
  change T (((coefficientCLM (ι := ι) T).inverse v) i) = T (T.inverse (v i))
  rw [hpoint,hT.self_apply_inverse]

/-- The coefficientwise reference comparison has a parameter-linear actual inverse. -/
theorem coefficient_opA_invertible_parameter_inverse
    {A E₂ E₁ ι : Type*} [CommRing A] [Algebra ℂ A]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ A) (g₀ gr : E₂ →L[ℂ] E₁) (R₀ : E₁ →L[ℂ] E₂)
    (hA : (opA (g₀.comp R₀) R₀ gr).IsInvertible) :
    letI := parameterCoefficientModule (E := E₁) b
    let B := opA ((coefficientCLM g₀).comp (coefficientCLM R₀)) (coefficientCLM R₀) (coefficientCLM gr)
    ∃ (_hB : B.IsInvertible) (BInvA : Module.End A (ι → E₁)), ∀ x, BInvA x = B.inverse x := by
  let := parameterCoefficientModule (E := E₁) b
  let C : E₁ →L[ℂ] E₁ := opA (g₀.comp R₀) R₀ gr
  let B : (ι → E₁) →L[ℂ] (ι → E₁) :=
    opA ((coefficientCLM g₀).comp (coefficientCLM R₀)) (coefficientCLM R₀) (coefficientCLM gr)
  have hBC : B = coefficientCLM C := by
    ext v i
    simp [B, C, opA_apply]
  have hCI := coefficientCLM_invertible_and_inverse (ι := ι) C hA
  have hB : B.IsInvertible := hBC.symm ▸ hCI.1
  refine ⟨hB, coefficientMap b C.inverse.toLinearMap, ?_⟩
  intro x
  rw [coefficientCLM_eq_parameterMap b C.inverse]
  change (coefficientCLM C.inverse) x = B.inverse x
  rw [hBC, hCI.2]

end
end Hironaka.Analytic.Unibranch.HironakaG10CoefficientOpAInvertible
