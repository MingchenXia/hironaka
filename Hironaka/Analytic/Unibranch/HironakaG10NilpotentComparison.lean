import Hironaka.Analytic.Unibranch.HironakaG10FlatNilpotentEndomorphism

/-! A parameter-linear map congruent to the identity modulo a nilpotent
ideal has an internally constructed parameter-linear inverse. -/
set_option autoImplicit false
namespace Hironaka.Analytic.Unibranch.HironakaG10NilpotentComparison
open Hironaka.Analytic.Unibranch.HironakaG10FlatNilpotentEndomorphism

/-- No topology, finite generation, locality, or nontriviality is assumed. -/
theorem exists_linearEquiv_of_nilpotent_difference
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) (hnil : ∃ n : ℕ, I ^ n = ⊥) (F : Module.End A M)
    (hmod : ∀ x, F x - x ∈ I • (⊤ : Submodule A M)) :
    ∃ e : M ≃ₗ[A] M, ∀ x, e x = F x := by
  let u : Module.End A M := 1 - F
  have hu (x : M) : u x ∈ I • (⊤ : Submodule A M) := by
    change x - F x ∈ I • (⊤ : Submodule A M)
    simpa only [neg_sub] using (I • (⊤ : Submodule A M)).neg_mem (hmod x)
  have hn := endomorphism_nilpotent_of_range I u hnil hu
  have hunit : IsUnit F := by
    have h := hn.isUnit_one_sub
    simpa [u] using h
  exact ⟨LinearEquiv.ofBijective F ((Module.End.isUnit_iff F).mp hunit), fun _ => rfl⟩
end Hironaka.Analytic.Unibranch.HironakaG10NilpotentComparison
