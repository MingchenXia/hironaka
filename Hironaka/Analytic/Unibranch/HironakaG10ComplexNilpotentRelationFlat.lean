import Hironaka.Analytic.Unibranch.HironakaG10NilpotentRelationFlat
import Hironaka.Analytic.Unibranch.HironakaG10AlgebraicReferenceInverse
import Hironaka.Analytic.Unibranch.HironakaG10FlatComplexScalarExtension

set_option autoImplicit false
open scoped TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10ComplexNilpotentRelationFlat
open Hironaka.Analytic.Unibranch.HironakaG10AlgebraicReferenceInverse
  Hironaka.Analytic.Unibranch.HironakaG10NilpotentRelationFlat
  Hironaka.Analytic.Unibranch.HironakaG10FlatComplexScalarExtension
noncomputable section

/-- Algebraic exactness of the entire reference relation module and an
actual lifted relation over a nilpotent complex parameter algebra force
flatness of the entire scalar-extended cokernel. -/
theorem flat_cokernel_of_complex_nilpotent_lifted_relation
    {A W U V : Type*} [CommRing A] [Algebra ℂ A]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
    [AddCommGroup V] [Module ℂ V]
    (I : Ideal A) (hnil : ∃ n : ℕ, I ^ n = ⊥)
    (g₀ : W →ₗ[ℂ] U) (f₀ : U →ₗ[ℂ] V)
    (hcomp : ∀ w, f₀ (g₀ w) = 0)
    (hex : ∀ u, f₀ u = 0 → ∃ w, g₀ w = u)
    (F : (A ⊗[ℂ] U) →ₗ[A] (A ⊗[ℂ] V))
    (G : (A ⊗[ℂ] W) →ₗ[A] (A ⊗[ℂ] U)) (hFG : ∀ w, F (G w) = 0)
    (hmodF : ∀ u, F u - f₀.baseChange A u ∈ I • (⊤ : Submodule A (A ⊗[ℂ] V)))
    (hmodG : ∀ w, G w - g₀.baseChange A w ∈ I • (⊤ : Submodule A (A ⊗[ℂ] U))) :
    Module.Flat A ((A ⊗[ℂ] V) ⧸ LinearMap.range F) := by
  let : Module.Flat A (A ⊗[ℂ] V) := flat_tensor_complex
  obtain ⟨R₀,hR⟩ := exists_generalized_inverse g₀
  obtain ⟨S₀,hS⟩ := exists_generalized_inverse f₀
  have hR' (w : A ⊗[ℂ] W) :
      g₀.baseChange A (R₀.baseChange A (g₀.baseChange A w)) = g₀.baseChange A w := by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a w => simp only [LinearMap.baseChange_tmul, hR]
    | add x y hx hy => simp only [map_add,hx,hy]
  have hS' (u : A ⊗[ℂ] U) :
      f₀.baseChange A (S₀.baseChange A (f₀.baseChange A u)) = f₀.baseChange A u := by
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul a u => simp only [LinearMap.baseChange_tmul, hS]
    | add x y hx hy => simp only [map_add,hx,hy]
  have hcomp' (w : A ⊗[ℂ] W) : f₀.baseChange A (g₀.baseChange A w) = 0 := by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a w => simp only [LinearMap.baseChange_tmul,hcomp,TensorProduct.tmul_zero]
    | add x y hx hy => simp only [map_add,hx,hy,add_zero]
  have he : Function.Exact g₀ f₀ := by
    apply LinearMap.exact_iff.mpr
    ext u
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · exact hex u
    · rintro ⟨w,rfl⟩
      exact hcomp w
  have he' := Module.Flat.lTensor_exact A he
  have hex' (u : A ⊗[ℂ] U) (hu : f₀.baseChange A u = 0) :
      ∃ w, g₀.baseChange A w = u := by
    have := (LinearMap.exact_iff.mp he')
    have hm : u ∈ LinearMap.range (g₀.lTensor A) := by
      rw [← this]
      exact hu
    exact hm
  exact flat_cokernel_of_nilpotent_lifted_relation I hnil (g₀.baseChange A) (f₀.baseChange A)
    (R₀.baseChange A) (S₀.baseChange A) hR' hS' hcomp' hex' F G hFG hmodF hmodG
end
end Hironaka.Analytic.Unibranch.HironakaG10ComplexNilpotentRelationFlat
