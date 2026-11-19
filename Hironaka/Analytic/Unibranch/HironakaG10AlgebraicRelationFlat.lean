import Hironaka.Analytic.Unibranch.HironakaG10ParameterLinearGeneralizedInverse

set_option autoImplicit false
namespace Hironaka.Analytic.Unibranch.HironakaG10AlgebraicRelationFlat
open Hironaka.Analytic.Unibranch.HironakaG10FlatGeneralizedInverse
noncomputable section

/-- Purely algebraic Frisch sufficiency: a lifted relation and invertible
comparisons force the literal cokernel to be flat over the parameter ring. -/
theorem flat_cokernel_of_lifted_relation_and_comparisons
    {A W U V : Type*} [CommRing A] [AddCommGroup W] [Module A W]
    [AddCommGroup U] [Module A U] [AddCommGroup V] [Module A V] [Module.Flat A V]
    (g₀ : W →ₗ[A] U) (f₀ : U →ₗ[A] V)
    (R₀ : U →ₗ[A] W) (S₀ : V →ₗ[A] U)
    (hR : ∀ w, g₀ (R₀ (g₀ w)) = g₀ w)
    (hS : ∀ u, f₀ (S₀ (f₀ u)) = f₀ u)
    (hex : ∀ u, f₀ u = 0 → ∃ w, g₀ w = u)
    (F : U →ₗ[A] V) (G : W →ₗ[A] U) (hFG : ∀ w, F (G w) = 0)
    (eA : U ≃ₗ[A] U) (eC : V ≃ₗ[A] V)
    (hA : ∀ u, eA u = g₀ (R₀ (G (R₀ (g₀ (R₀ u))))) + (u - g₀ (R₀ u)))
    (hC : ∀ v, eC v = F (S₀ v - g₀ (R₀ (S₀ v))) + (v - f₀ (S₀ v))) :
    Module.Flat A (V ⧸ LinearMap.range F) := by
  let P : U →ₗ[A] U := g₀.comp R₀
  have hP (u : U) : P (P u) = P u := hR (R₀ u)
  have hcompare (u : U) : P (G (R₀ (P u))) = P (eA u) := by
    rw [hA]
    change P (G (R₀ (P u))) = P (P (G (R₀ (P u))) + (u - P u))
    rw [map_add, map_sub, hP, hP, sub_self, add_zero]
  have hlift (x : U) : ∃ y, F y = 0 ∧ P y = P x := by
    refine ⟨G (R₀ (P (eA.symm x))), hFG _, ?_⟩
    rw [hcompare, eA.apply_symm_apply]
  have hone (u : U) : S₀ (f₀ u) - P (S₀ (f₀ u)) = u - P u := by
    have hk : f₀ (S₀ (f₀ u) - u) = 0 := by rw [map_sub, hS, sub_self]
    obtain ⟨w,hw⟩ := hex _ hk
    have h2 : P (S₀ (f₀ u)) - P u = S₀ (f₀ u) - u := by
      rw [← map_sub, ← hw]
      exact hR w
    rw [← sub_eq_zero, show S₀ (f₀ u) - P (S₀ (f₀ u)) - (u - P u) =
      (S₀ (f₀ u) - u) - (P (S₀ (f₀ u)) - P u) by abel, h2, sub_self]
  have hfun (u : U) : F (u - P u) = eC (f₀ u) := by
    rw [hC, hS, sub_self, add_zero]
    exact congrArg F (hone u).symm
  let s : V →ₗ[A] U := (LinearMap.id - P).comp (S₀.comp eC.symm.toLinearMap)
  apply cokernel_flat_of_generalized_inverse F s
  intro x
  obtain ⟨y,hy,hpy⟩ := hlift x
  have hfx : F x = eC (f₀ (x-y)) := by
    rw [← hfun, map_sub P, hpy, sub_self, sub_zero, map_sub F, hy, sub_zero]
  change F (S₀ (eC.symm (F x)) - P (S₀ (eC.symm (F x)))) = F x
  rw [hfx, eC.symm_apply_apply, hfun, hS]
end
end Hironaka.Analytic.Unibranch.HironakaG10AlgebraicRelationFlat
