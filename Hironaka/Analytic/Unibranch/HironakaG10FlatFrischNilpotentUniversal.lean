import Hironaka.Analytic.Unibranch.HironakaG10FlatArtinianProjection
import Hironaka.Resolution.HironakaG10LocFrischLocus

/-! # Frisch's Schur obstruction vanishes over nilpotent parameter rings

An actual algebraic flatness-to-projected-kernel implication is combined
with Frisch's existing Banach operator criterion. -/
set_option autoImplicit false

namespace Hironaka.Analytic.Unibranch.HironakaG10FlatFrischNilpotentUniversal
open Hironaka
  HironakaG10LocDirectPersistence HironakaG10LocFrischLocus
open Hironaka.Analytic.Unibranch.HironakaG10FlatArtinianProjection

/-- The non-reduced operator form of Frisch's universal direction: if a
  parameter-linear presentation has flat target and cokernel over a ring
  with nilpotent ideal `I`, and the reference projected vectors become
  relations modulo `I`, then the actual Frisch Schur operator vanishes.
  The equalities `hf` and `hπ` identify the parameter-linear maps with the
  actual Banach presentation and reference projection. -/
theorem schurOp_eq_zero_of_flat_nilpotent
    {A E₂ E₁ E₀ : Type*} [CommRing A]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [Module A E₁]
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀] [Module A E₀]
    {g₀ : E₂ →L[ℂ] E₁} {f₀ : E₁ →L[ℂ] E₀}
    {R₀ : E₁ →L[ℂ] E₂} {S₀ : E₀ →L[ℂ] E₁}
    (hR₀ : ∀ e, g₀ (R₀ (g₀ e)) = g₀ e)
    (hS₀ : ∀ x, f₀ (S₀ (f₀ x)) = f₀ x)
    (hex : ∀ x, f₀ x = 0 → ∃ e, g₀ e = x)
    (f : E₁ →L[ℂ] E₀)
    (hC : (opC (g₀.comp R₀) (f₀.comp S₀) S₀ f).IsInvertible)
    (fA : E₁ →ₗ[A] E₀) (πA : E₁ →ₗ[A] E₁)
    (hf : ∀ x, fA x = f x) (hπ : ∀ x, πA x = g₀ (R₀ x))
    [Module.Flat A E₀] [Module.Flat A (E₀ ⧸ LinearMap.range fA)]
    (I : Ideal A) (hnil : ∃ n : ℕ, I ^ n = ⊥)
    (hres : ∀ x, fA (πA x) ∈ I • (⊤ : Submodule A E₀)) :
    schurOp (g₀.comp R₀) (f₀.comp S₀) S₀ f = 0 := by
  have hp : ∀ x, πA (πA x) = πA x := by
    intro x
    calc
      πA (πA x) = g₀ (R₀ (πA x)) := hπ _
      _ = g₀ (R₀ (g₀ (R₀ x))) := by rw [hπ]
      _ = g₀ (R₀ x) := hR₀ (R₀ x)
      _ = πA x := (hπ x).symm
  have hlift := projected_kernel_surjective_of_flat_nilpotent fA πA hp I hnil hres
  apply (schurOp_eq_zero_iff hR₀ hS₀ hex hC).2
  intro x
  obtain ⟨y,hy,hproj⟩ := hlift x
  refine ⟨y,?_,?_⟩
  · rw [← hf y]; exact hy
  · rw [← hπ y, ← hπ x]; exact hproj

end Hironaka.Analytic.Unibranch.HironakaG10FlatFrischNilpotentUniversal
