import Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators
import Hironaka.Analytic.Unibranch.HironakaG10FlatFrischNilpotentReference

/-! # Frisch's nilpotent universal direction on actual finite coefficients -/
set_option autoImplicit false
open scoped TensorProduct

namespace Hironaka.Analytic.Unibranch.HironakaG10FlatFrischCoefficientUniversal
open Hironaka HironakaG10LocDirectPersistence HironakaG10LocFrischLocus
open Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators
  Hironaka.Analytic.Unibranch.HironakaG10FlatFrischNilpotentReference

/-- Frisch's universal Schur-vanishing direction on the concrete finite
  coefficient Banach spaces of a nilpotent parameter algebra. The target
  flatness, reference parameter-linearity, and reference direct-exactness
  are all derived from the original complex Banach data. -/
theorem schurOp_eq_zero_on_coefficients
    {A E₂ E₁ E₀ ι : Type*} [CommRing A] [Algebra ℂ A]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ A)
    (g₀ : E₂ →L[ℂ] E₁) (f₀ : E₁ →L[ℂ] E₀)
    (R₀ : E₁ →L[ℂ] E₂) (S₀ : E₀ →L[ℂ] E₁)
    (hR₀ : ∀ e, g₀ (R₀ (g₀ e)) = g₀ e)
    (hS₀ : ∀ x, f₀ (S₀ (f₀ x)) = f₀ x)
    (hcomp : ∀ e, f₀ (g₀ e) = 0)
    (hex : ∀ x, f₀ x = 0 → ∃ e, g₀ e = x) :
    letI := parameterCoefficientModule (E := E₁) b
    letI := parameterCoefficientModule (E := E₀) b
    ∀ (F : (ι → E₁) →L[ℂ] (ι → E₀))
      (_hC : (opC ((coefficientCLM g₀).comp (coefficientCLM R₀))
        ((coefficientCLM f₀).comp (coefficientCLM S₀)) (coefficientCLM S₀) F).IsInvertible)
      (FA : (ι → E₁) →ₗ[A] (ι → E₀)) (_hF : ∀ x, FA x = F x)
      (_hflat : Module.Flat A ((ι → E₀) ⧸ LinearMap.range FA))
      (I : Ideal A) (_hnil : ∃ n : ℕ, I ^ n = ⊥),
      (∀ x, FA x - coefficientMap b f₀.toLinearMap x ∈ I • (⊤ : Submodule A (ι → E₀))) →
      schurOp ((coefficientCLM g₀).comp (coefficientCLM R₀))
        ((coefficientCLM f₀).comp (coefficientCLM S₀)) (coefficientCLM S₀) F = 0 := by
  let := parameterCoefficientModule (E := E₁) b
  let := parameterCoefficientModule (E := E₀) b
  intro F hC FA hF hflat I hnil hmod
  let : Module.Flat A (ι → E₀) := parameterCoefficient_flat b
  let : Module.Flat A ((ι → E₀) ⧸ LinearMap.range FA) := hflat
  obtain ⟨hR,hS,hcomp',hex'⟩ := reference_direct_exact_on_coefficients (ι := ι) g₀ f₀ R₀ S₀
    hR₀ hS₀ hcomp hex
  let f₀A := coefficientMap b f₀.toLinearMap
  let πA := coefficientMap b (g₀.comp R₀).toLinearMap
  have hf₀ : ∀ x, f₀A x = coefficientCLM f₀ x := coefficientCLM_eq_parameterMap b f₀
  have hπ : ∀ x, πA x = coefficientCLM g₀ (coefficientCLM R₀ x) := by
    intro x
    funext i
    rw [coefficientMap_apply]
    rfl
  exact schurOp_eq_zero_of_flat_and_special_fibre hR hS hex' hcomp' F hC FA f₀A πA
    hF hf₀ hπ I hnil hmod

end Hironaka.Analytic.Unibranch.HironakaG10FlatFrischCoefficientUniversal
