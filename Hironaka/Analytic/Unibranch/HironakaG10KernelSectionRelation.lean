import Mathlib.RingTheory.Ideal.Operations
import Mathlib.LinearAlgebra.Quotient.Basic

/-! A parameter-linear kernel section gives a whole relation lift retaining
its exact reference matrix modulo any specified parameter ideal. -/
set_option autoImplicit false
namespace Hironaka.Analytic.Unibranch.HironakaG10KernelSectionRelation

/-- The reference relation is lifted by the kernel section, and the
residue congruence follows from parameter linearity alone. -/
theorem exists_relation_lift_of_kernel_section
    {A W U V : Type*} [CommRing A] [AddCommGroup W] [Module A W]
    [AddCommGroup U] [Module A U] [AddCommGroup V] [Module A V]
    (I : Ideal A) (f₀ : U →ₗ[A] V) (g₀ : W →ₗ[A] U)
    (f : U →ₗ[A] V) (s : V →ₗ[A] U)
    (hcomp : ∀ w, f₀ (g₀ w) = 0)
    (hmod : ∀ u, f u - f₀ u ∈ I • (⊤ : Submodule A V))
    (hker : ∀ u, f (u - s (f u)) = 0) :
    ∃ G : W →ₗ[A] U, (∀ w, f (G w) = 0) ∧
      ∀ w, G w - g₀ w ∈ I • (⊤ : Submodule A U) := by
  let G : W →ₗ[A] U := (LinearMap.id - s.comp f).comp g₀
  refine ⟨G, ?_, ?_⟩
  · intro w
    exact hker (g₀ w)
  · intro w
    have hf : f (g₀ w) ∈ I • (⊤ : Submodule A V) := by
      simpa only [hcomp, sub_zero] using hmod (g₀ w)
    have hmap : (I • (⊤ : Submodule A V)).map s ≤ I • (⊤ : Submodule A U) := by
      rw [Submodule.map_smul'', Submodule.map_top]
      exact smul_mono_right I le_top
    have hs : s (f (g₀ w)) ∈ I • (⊤ : Submodule A U) :=
      hmap (Submodule.mem_map_of_mem hf)
    change (g₀ w - s (f (g₀ w))) - g₀ w ∈ I • (⊤ : Submodule A U)
    have hn := (I • (⊤ : Submodule A U)).neg_mem hs
    convert hn using 1; abel
end Hironaka.Analytic.Unibranch.HironakaG10KernelSectionRelation
