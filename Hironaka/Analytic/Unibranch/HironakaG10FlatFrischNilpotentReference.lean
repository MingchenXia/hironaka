import Hironaka.Analytic.Unibranch.HironakaG10FlatFrischNilpotentUniversal

/-! # Frisch non-reduced universality from agreement with the special fibre -/
set_option autoImplicit false

namespace Hironaka.Analytic.Unibranch.HironakaG10FlatFrischNilpotentReference
open Hironaka
  HironakaG10LocDirectPersistence HironakaG10LocFrischLocus
open Hironaka.Analytic.Unibranch.HironakaG10FlatFrischNilpotentUniversal

/-- If the parameter-linear presentation reduces to the reference
  presentation modulo a nilpotent ideal, flatness of its target and cokernel
  forces the actual Banach Schur operator to vanish. -/
theorem schurOp_eq_zero_of_flat_and_special_fibre
    {A E₂ E₁ E₀ : Type*} [CommRing A]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [Module A E₁]
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀] [Module A E₀]
    {g₀ : E₂ →L[ℂ] E₁} {f₀ : E₁ →L[ℂ] E₀}
    {R₀ : E₁ →L[ℂ] E₂} {S₀ : E₀ →L[ℂ] E₁}
    (hR₀ : ∀ e, g₀ (R₀ (g₀ e)) = g₀ e)
    (hS₀ : ∀ x, f₀ (S₀ (f₀ x)) = f₀ x)
    (hex : ∀ x, f₀ x = 0 → ∃ e, g₀ e = x)
    (hcomp : ∀ e, f₀ (g₀ e) = 0)
    (f : E₁ →L[ℂ] E₀)
    (hC : (opC (g₀.comp R₀) (f₀.comp S₀) S₀ f).IsInvertible)
    (fA f₀A : E₁ →ₗ[A] E₀) (πA : E₁ →ₗ[A] E₁)
    (hf : ∀ x, fA x = f x) (hf₀ : ∀ x, f₀A x = f₀ x)
    (hπ : ∀ x, πA x = g₀ (R₀ x))
    [Module.Flat A E₀] [Module.Flat A (E₀ ⧸ LinearMap.range fA)]
    (I : Ideal A) (hnil : ∃ n : ℕ, I ^ n = ⊥)
    (hmod : ∀ x, fA x - f₀A x ∈ I • (⊤ : Submodule A E₀)) :
    schurOp (g₀.comp R₀) (f₀.comp S₀) S₀ f = 0 := by
  apply schurOp_eq_zero_of_flat_nilpotent hR₀ hS₀ hex f hC fA πA hf hπ I hnil
  intro x
  have hz : f₀A (πA x) = 0 := by rw [hf₀,hπ,hcomp]
  simpa only [hz,sub_zero] using hmod (πA x)

end Hironaka.Analytic.Unibranch.HironakaG10FlatFrischNilpotentReference
