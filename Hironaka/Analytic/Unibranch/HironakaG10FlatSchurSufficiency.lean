import Hironaka.Analytic.Unibranch.HironakaG10ParameterLinearGeneralizedInverse
import Hironaka.Analytic.Unibranch.HironakaG10InvertibleParameterLinear
import Hironaka.Resolution.HironakaG10LocFrischLocus

set_option autoImplicit false
namespace Hironaka.Analytic.Unibranch.HironakaG10FlatSchurSufficiency
open Hironaka HironakaG10LocDirectPersistence HironakaG10LocFrischLocus
open Hironaka.Analytic.Unibranch.HironakaG10FlatGeneralizedInverse
  Hironaka.Analytic.Unibranch.HironakaG10InvertibleParameterLinear
noncomputable section

/-- The literal Schur obstruction vanishing makes the full parameter-linear
operator cokernel flat when its target is flat. -/
theorem flat_cokernel_of_schur_zero
    {A E₂ E₁ E₀ : Type*} [CommRing A]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [Module A E₁]
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀] [Module A E₀] [Module.Flat A E₀]
    (g₀ : E₂ →L[ℂ] E₁) (f₀ : E₁ →L[ℂ] E₀)
    (R₀ : E₁ →L[ℂ] E₂) (S₀ : E₀ →L[ℂ] E₁)
    (hR : ∀ x, g₀ (R₀ (g₀ x)) = g₀ x)
    (hS : ∀ x, f₀ (S₀ (f₀ x)) = f₀ x)
    (hex : ∀ x, f₀ x = 0 → ∃ y, g₀ y = x)
    (f : E₁ →L[ℂ] E₀) (FA : E₁ →ₗ[A] E₀)
    (PA : E₁ →ₗ[A] E₁) (QA : E₀ →ₗ[A] E₀) (SA : E₀ →ₗ[A] E₁)
    (hFA : ∀ x, FA x = f x) (hPA : ∀ x, PA x = g₀ (R₀ x))
    (hQA : ∀ x, QA x = f₀ (S₀ x)) (hSA : ∀ x, SA x = S₀ x)
    (hC : (opC (g₀.comp R₀) (f₀.comp S₀) S₀ f).IsInvertible)
    (hT : schurOp (g₀.comp R₀) (f₀.comp S₀) S₀ f = 0) :
    Module.Flat A (E₀ ⧸ LinearMap.range FA) := by
  let C := opC (g₀.comp R₀) (f₀.comp S₀) S₀ f
  let CA : E₀ →ₗ[A] E₀ := FA.comp ((LinearMap.id - PA).comp SA) + (LinearMap.id - QA)
  have hCA (x : E₀) : CA x = C x := by
    change FA (SA x - PA (SA x)) + (x - QA x) =
      f (S₀ x - g₀ (R₀ (S₀ x))) + (x - f₀ (S₀ x))
    simp only [hFA,hPA,hQA,hSA]
  obtain ⟨CI,hCI⟩ := exists_parameterLinear_inverse C CA hCA hC
  let S : E₀ →ₗ[A] E₁ := (LinearMap.id - PA).comp (SA.comp CI)
  have hS' (x : E₀) : S x = S₀ (C.inverse x) - g₀ (R₀ (S₀ (C.inverse x))) := by
    simp only [S, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, hPA, hSA, hCI]
  apply cokernel_flat_of_generalized_inverse FA S
  intro x
  have hk := f_kerSec hR hS hex hC hT x
  change f (x - (S₀ (C.inverse (f x)) - g₀ (R₀ (S₀ (C.inverse (f x)))))) = 0 at hk
  have hf : f x = f (S₀ (C.inverse (f x)) - g₀ (R₀ (S₀ (C.inverse (f x))))) := by
    exact sub_eq_zero.mp (by simpa only [map_sub] using hk)
  simpa only [hFA,hS'] using hf.symm
end
end Hironaka.Analytic.Unibranch.HironakaG10FlatSchurSufficiency
