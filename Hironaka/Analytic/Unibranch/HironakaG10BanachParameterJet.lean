import Hironaka.Resolution.HironakaActualMultilinearTaylorCoordinates
import Hironaka.Resolution.HironakaHolomorphicJetMonomialSpan
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! # The actual finite Banach-valued parameter jet

The finite sum is built from the actual iterated derivatives and images of
original parameter-coordinate germs. It does not choose a tensor norm.
-/
set_option autoImplicit false
open Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
open Hironaka Hironaka
  HironakaHolomorphicJetMonomialSpan

noncomputable section

/-- The actual truncated parameter jet of a Banach-valued holomorphic
  family, evaluated in the given original scalar-germ algebra map. -/
def banachJet {Γ E : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Γ)
    (f : ComplexModel d → E) : Γ ⊗[ℂ] E :=
  ∑ k ∈ Finset.range (q+1), ∑ w : Fin k → Fin d,
    φ (∏ i : Fin k, coordinateGerm (w i)) ⊗ₜ[ℂ]
      ((Nat.factorial k : ℂ)⁻¹ • (iteratedFDeriv ℂ k f 0)
        (fun i => EuclideanSpace.single (w i) (1 : ℂ)))

/-- The jet is natural for every continuous complex-linear map, on the
  entire tensor product and without any finite-dimensional target hypothesis. -/
theorem banachJet_map {Γ E F : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Γ)
    (f : ComplexModel d → E) (hf : ContDiffAt ℂ ⊤ f 0) (L : E →L[ℂ] F) :
    banachJet d q φ (L ∘ f) = L.toLinearMap.baseChange Γ (banachJet d q φ f) := by
  classical
  simp only [banachJet, map_sum, LinearMap.baseChange_tmul]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro w hw
  rw [L.iteratedFDeriv_comp_left hf (by simp)]
  simp only [map_smul]
  rfl

end
end Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
