import Hironaka.Analytic.Unibranch.HironakaG10FlatSchurSufficiency
import Hironaka.Analytic.Unibranch.HironakaG10KernelSectionRelation

/-! A zero actual Schur obstruction yields a parameter-linear kernel
section and a full relation lift with the same residue. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Hironaka HironakaG10LocDirectPersistence HironakaG10LocFrischLocus
  Hironaka.Analytic.Unibranch.HironakaG10InvertibleParameterLinear
  Hironaka.Analytic.Unibranch.HironakaG10KernelSectionRelation
namespace Hironaka.Analytic.Unibranch.HironakaG10SchurParameterRelation
noncomputable section

theorem exists_parameter_kernel_section_of_schur_zero
    {A E₂ E₁ E₀ : Type*} [CommRing A]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [Module A E₁]
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀] [Module A E₀]
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
    ∃ S : E₀ →ₗ[A] E₁, ∀ x, FA (x - S (FA x)) = 0 := by
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
  refine ⟨S, fun x => ?_⟩
  have hk := f_kerSec hR hS hex hC hT x
  change f (x - (S₀ (C.inverse (f x)) - g₀ (R₀ (S₀ (C.inverse (f x)))))) = 0 at hk
  simpa only [hFA,hS'] using hk

/-- The same parameter-linear kernel section lifts all reference relations
and retains their full congruence modulo the given ideal. -/
theorem exists_parameter_relation_of_schur_zero
    {A E₂ E₁ E₀ : Type*} [CommRing A]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [Module A E₂]
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [Module A E₁]
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀] [Module A E₀]
    (I : Ideal A) (g₀ : E₂ →L[ℂ] E₁) (f₀ : E₁ →L[ℂ] E₀)
    (R₀ : E₁ →L[ℂ] E₂) (S₀ : E₀ →L[ℂ] E₁)
    (hR : ∀ x, g₀ (R₀ (g₀ x)) = g₀ x)
    (hS : ∀ x, f₀ (S₀ (f₀ x)) = f₀ x)
    (hex : ∀ x, f₀ x = 0 → ∃ y, g₀ y = x) (hcomp : ∀ x, f₀ (g₀ x) = 0)
    (f : E₁ →L[ℂ] E₀) (FA : E₁ →ₗ[A] E₀)
    (F₀A : E₁ →ₗ[A] E₀) (G₀A : E₂ →ₗ[A] E₁)
    (PA : E₁ →ₗ[A] E₁) (QA : E₀ →ₗ[A] E₀) (SA : E₀ →ₗ[A] E₁)
    (hFA : ∀ x, FA x = f x) (hF₀A : ∀ x, F₀A x = f₀ x) (hG₀A : ∀ x, G₀A x = g₀ x)
    (hPA : ∀ x, PA x = g₀ (R₀ x)) (hQA : ∀ x, QA x = f₀ (S₀ x)) (hSA : ∀ x, SA x = S₀ x)
    (hmod : ∀ x, FA x - F₀A x ∈ I • (⊤ : Submodule A E₀))
    (hC : (opC (g₀.comp R₀) (f₀.comp S₀) S₀ f).IsInvertible)
    (hT : schurOp (g₀.comp R₀) (f₀.comp S₀) S₀ f = 0) :
    ∃ G : E₂ →ₗ[A] E₁, (∀ x, FA (G x) = 0) ∧
      ∀ x, G x - G₀A x ∈ I • (⊤ : Submodule A E₁) := by
  obtain ⟨S,hker⟩ := exists_parameter_kernel_section_of_schur_zero g₀ f₀ R₀ S₀ hR hS hex
    f FA PA QA SA hFA hPA hQA hSA hC hT
  apply exists_relation_lift_of_kernel_section I F₀A G₀A FA S
  · intro x
    rw [hF₀A,hG₀A,hcomp]
  · exact hmod
  · exact hker
end
end Hironaka.Analytic.Unibranch.HironakaG10SchurParameterRelation
