import Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
import Hironaka.Analytic.Unibranch.HironakaG10BilinearTaylorReduction

/-! # Reduction of the actual bilinear parameter jet to finite polynomials -/
set_option autoImplicit false
open Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10BilinearJetTaylorReduction
open Hironaka Hironaka
  Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
  Hironaka.Analytic.Unibranch.HironakaG10BanachTaylorRemainder
  Hironaka.Analytic.Unibranch.HironakaG10BilinearTaylorReduction

/-- The entire parameter tensor jet of a bilinear product is unchanged
when both original holomorphic factors are replaced by their actual finite
Taylor polynomials. -/
theorem banachJet_bilinear_taylorPartial
    {Γ E F G : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Γ)
    (B : E →L[ℂ] F →L[ℂ] G) (f : ComplexModel d → E) (g : ComplexModel d → F)
    (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ f z)
    (hg : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ g z) :
    banachJet d q φ (fun x => B (f x) (g x)) =
      banachJet d q φ (fun x => B (taylorPartial f (q+1) x) (taylorPartial g (q+1) x)) := by
  classical
  simp only [banachJet]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro w hw
  rw [iteratedFDeriv_bilinear_taylorPartial B f g hf hg (q+1) k (Finset.mem_range.mp hk)]

end Hironaka.Analytic.Unibranch.HironakaG10BilinearJetTaylorReduction
