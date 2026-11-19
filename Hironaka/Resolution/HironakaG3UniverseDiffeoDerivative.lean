import Hironaka.Manifold.ComplexManifold
import Mathlib.Geometry.Manifold.Diffeomorph
set_option autoImplicit false
open Function
open scoped Manifold ContDiff
universe u v
namespace Hironaka.HironakaG3UniverseDiffeoDerivative
noncomputable section


/-- A biholomorphism has bijective manifold derivative, even across universes. -/
theorem diffeo_mfderiv_bijective {n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) X]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n X] [IsComplexManifold n Y]
    (e : X ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ Y) (x : X) :
    Bijective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) e x) := by
  have he : ∀ z, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) e z :=
    fun z => e.contMDiff.mdifferentiableAt (by simp)
  have hs : ∀ z, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) e.symm z :=
    fun z => e.symm.contMDiff.mdifferentiableAt (by simp)
  have h1 : (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) e.symm (e x)).comp
      (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) e x) = ContinuousLinearMap.id ℂ _ := by
    rw [← mfderiv_comp x (hs _) (he x), show e.symm ∘ e = id from funext e.symm_apply_apply]
    exact mfderiv_id
  have h2 : (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) e (e.symm (e x))).comp
      (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) e.symm (e x)) = ContinuousLinearMap.id ℂ _ := by
    rw [← mfderiv_comp (e x) (he _) (hs (e x)), show e ∘ e.symm = id from funext e.apply_symm_apply]
    exact mfderiv_id
  rw [e.symm_apply_apply] at h2
  exact ⟨Function.LeftInverse.injective (g := mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) e.symm (e x))
      fun v => DFunLike.congr_fun h1 v,
    Function.RightInverse.surjective (g := mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) e.symm (e x))
      fun v => DFunLike.congr_fun h2 v⟩
end
end Hironaka.HironakaG3UniverseDiffeoDerivative
