import Hironaka.Analytic.Unibranch.HironakaG10AlgebraicRelationFlat
import Hironaka.Analytic.Unibranch.HironakaG10NilpotentComparison

set_option autoImplicit false
namespace Hironaka.Analytic.Unibranch.HironakaG10NilpotentRelationFlat
open Hironaka.Analytic.Unibranch.HironakaG10AlgebraicRelationFlat
  Hironaka.Analytic.Unibranch.HironakaG10NilpotentComparison
noncomputable section

/-- Over a nilpotent parameter thickening, lifting the complete reference
relation module makes the literal cokernel flat over the parameter ring. -/
theorem flat_cokernel_of_nilpotent_lifted_relation
    {A W U V : Type*} [CommRing A] [AddCommGroup W] [Module A W]
    [AddCommGroup U] [Module A U] [AddCommGroup V] [Module A V] [Module.Flat A V]
    (I : Ideal A) (hnil : ∃ n : ℕ, I ^ n = ⊥)
    (g₀ : W →ₗ[A] U) (f₀ : U →ₗ[A] V)
    (R₀ : U →ₗ[A] W) (S₀ : V →ₗ[A] U)
    (hR : ∀ w, g₀ (R₀ (g₀ w)) = g₀ w)
    (hS : ∀ u, f₀ (S₀ (f₀ u)) = f₀ u)
    (hcomp : ∀ w, f₀ (g₀ w) = 0)
    (hex : ∀ u, f₀ u = 0 → ∃ w, g₀ w = u)
    (F : U →ₗ[A] V) (G : W →ₗ[A] U) (hFG : ∀ w, F (G w) = 0)
    (hmodF : ∀ u, F u - f₀ u ∈ I • (⊤ : Submodule A V))
    (hmodG : ∀ w, G w - g₀ w ∈ I • (⊤ : Submodule A U)) :
    Module.Flat A (V ⧸ LinearMap.range F) := by
  let P : U →ₗ[A] U := g₀.comp R₀
  have hP (u : U) : P (P u) = P u := hR (R₀ u)
  let B : Module.End A U := P.comp (G.comp (R₀.comp P)) + (LinearMap.id - P)
  have hB (u : U) : B u - u ∈ I • (⊤ : Submodule A U) := by
    have hd := hmodG (R₀ (P u))
    have hmap : (I • (⊤ : Submodule A U)).map P ≤ I • (⊤ : Submodule A U) := by
      rw [Submodule.map_smul'', Submodule.map_top]
      exact smul_mono_right I le_top
    have hp : P (G (R₀ (P u)) - g₀ (R₀ (P u))) ∈ I • (⊤ : Submodule A U) :=
      hmap (Submodule.mem_map_of_mem hd)
    have hp3 : P (g₀ (R₀ (P u))) = P u := by
      change P (P (P u)) = P u
      rw [hP,hP]
    have heq : B u - u = P (G (R₀ (P u)) - g₀ (R₀ (P u))) := by
      change (P (G (R₀ (P u))) + (u - P u)) - u = _
      rw [map_sub, hp3]
      abel
    rw [heq]
    exact hp
  let C : Module.End A V := F.comp ((LinearMap.id - P).comp S₀) + (LinearMap.id - f₀.comp S₀)
  have hC (v : V) : C v - v ∈ I • (⊤ : Submodule A V) := by
    have hd := hmodF (S₀ v - P (S₀ v))
    have hzero : f₀ (P (S₀ v)) = 0 := hcomp (R₀ (S₀ v))
    have heq : C v - v = F (S₀ v - P (S₀ v)) - f₀ (S₀ v - P (S₀ v)) := by
      change (F (S₀ v - P (S₀ v)) + (v - f₀ (S₀ v))) - v = _
      simp only [map_sub, hzero, sub_zero]
      abel
    rw [heq]
    exact hd
  obtain ⟨eB,heB⟩ := exists_linearEquiv_of_nilpotent_difference I hnil B hB
  obtain ⟨eC,heC⟩ := exists_linearEquiv_of_nilpotent_difference I hnil C hC
  apply flat_cokernel_of_lifted_relation_and_comparisons g₀ f₀ R₀ S₀ hR hS hex F G hFG eB eC
  · intro u
    rw [heB]
    rfl
  · intro v
    rw [heC]
    rfl
end
end Hironaka.Analytic.Unibranch.HironakaG10NilpotentRelationFlat
