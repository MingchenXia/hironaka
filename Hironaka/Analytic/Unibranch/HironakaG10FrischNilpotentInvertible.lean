import Hironaka.Analytic.Unibranch.HironakaG10FlatNilpotentContinuous
import Hironaka.Analytic.Unibranch.HironakaG10FlatFrischCoefficientUniversal

/-! # Automatic Frisch comparison invertibility on nilpotent tests -/
set_option autoImplicit false
namespace Hironaka.Analytic.Unibranch.HironakaG10FrischNilpotentInvertible
open Hironaka.HironakaG10LocDirectPersistence
open Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators
  Hironaka.Analytic.Unibranch.HironakaG10FlatNilpotentContinuous

/-- Frisch's comparison operator is automatically invertible for an
  operator reducing to the reference modulo a nilpotent parameter ideal. -/
theorem opC_invertible_on_nilpotent_coefficients
    {A E₂ E₁ E₀ ι : Type*} [CommRing A] [Algebra ℂ A]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ A)
    (g₀ : E₂ →L[ℂ] E₁) (f₀ : E₁ →L[ℂ] E₀)
    (R₀ : E₁ →L[ℂ] E₂) (S₀ : E₀ →L[ℂ] E₁)
    (hcomp : ∀ e, f₀ (g₀ e) = 0) (I : Ideal A) (hnil : ∃ n : ℕ, I ^ n = ⊥) :
    letI := parameterCoefficientModule (E := E₁) b
    letI := parameterCoefficientModule (E := E₀) b
    ∀ (F : (ι → E₁) →L[ℂ] (ι → E₀)) (FA : (ι → E₁) →ₗ[A] (ι → E₀)),
      (∀ x, FA x = F x) →
      (∀ x, FA x - coefficientMap b f₀.toLinearMap x ∈ I • (⊤ : Submodule A (ι → E₀))) →
      (opC ((coefficientCLM g₀).comp (coefficientCLM R₀))
        ((coefficientCLM f₀).comp (coefficientCLM S₀)) (coefficientCLM S₀) F).IsInvertible := by
  let := parameterCoefficientModule (E := E₁) b
  let := parameterCoefficientModule (E := E₀) b
  intro F FA hF hmod
  let P : (ι → E₁) →L[ℂ] (ι → E₁) := (coefficientCLM g₀).comp (coefficientCLM R₀)
  let T : (ι → E₀) →L[ℂ] (ι → E₁) := (.id ℂ _ - P).comp (coefficientCLM S₀)
  let PA : (ι → E₁) →ₗ[A] (ι → E₁) := coefficientMap b (g₀.comp R₀).toLinearMap
  let TA : (ι → E₀) →ₗ[A] (ι → E₁) := (LinearMap.id - PA).comp (coefficientMap b S₀.toLinearMap)
  let uA : Module.End A (ι → E₀) := (coefficientMap b f₀.toLinearMap - FA).comp TA
  let u : (ι → E₀) →L[ℂ] (ι → E₀) := ((coefficientCLM f₀) - F).comp T
  have hTA (x : ι → E₀) : TA x = T x := by
    funext i
    simp [TA,T,PA,P,coefficientMap_apply]
  have hu (x : ι → E₀) : uA x = u x := by
    change coefficientMap b f₀.toLinearMap (TA x) - FA (TA x) = _
    rw [coefficientCLM_eq_parameterMap b f₀, hF, hTA]
    rfl
  have himage (x : ι → E₀) : uA x ∈ I • (⊤ : Submodule A (ι → E₀)) := by
    change coefficientMap b f₀.toLinearMap (TA x) - FA (TA x) ∈ _
    simpa only [neg_sub] using (I • (⊤ : Submodule A (ι → E₀))).neg_mem (hmod (TA x))
  have hinv := isInvertible_id_sub_of_parameter_nilpotent I uA u hu hnil himage
  have heq : .id ℂ (ι → E₀) - u = opC P ((coefficientCLM f₀).comp (coefficientCLM S₀)) (coefficientCLM S₀) F := by
    ext x i
    simp only [opC_apply, _root_.sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, Pi.sub_apply]
    dsimp [u,T,P]
    simp only [_root_.sub_apply,ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply,coefficientCLM_apply,Pi.sub_apply,map_sub,hcomp]
    abel
  rw [heq] at hinv
  exact hinv

end Hironaka.Analytic.Unibranch.HironakaG10FrischNilpotentInvertible
