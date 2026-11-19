import Hironaka.Analytic.Unibranch.HironakaG10BanachJetScalarization
import Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients

/-! # Scalar evaluations of the concrete finite coefficient Banach jet -/
set_option autoImplicit false
open Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10BanachJetCoordinates
open Hironaka Hironaka
open Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
  Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
  Hironaka.Analytic.Unibranch.HironakaG10BanachJetScalarization

/-- Scalarizing any whole tensor is the sum of the scalar evaluations
  of its actual finite coefficient vectors in the chosen parameter basis. -/
theorem scalarization_eq_coefficient_sum
    {Γ E ι : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ Γ) (L : E →L[ℂ] ℂ) (z : Γ ⊗[ℂ] E) :
    (TensorProduct.rid ℂ Γ) (L.toLinearMap.baseChange Γ z) =
      ∑ i, (L (parameterTensorEquiv b z i)) • b i := by
  classical
  have hz : z = ∑ i, b i ⊗ₜ[ℂ] (parameterTensorEquiv b z i) := by
    apply (parameterTensorEquiv b).injective
    ext i
    simp [parameterTensorEquiv_tmul]
  conv_lhs => rw [hz]
  simp only [map_sum, LinearMap.baseChange_tmul, TensorProduct.rid_tmul]
  rfl

/-- Every scalar evaluation of the finite coefficient Banach jet is exactly
  the original scalar germ evaluated by the given Artinian test map. -/
theorem scalar_germ_eq_coefficient_jet
    {Γ E ι : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ Γ)
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Γ)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    (f : ComplexModel d → E)
    (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ f z)
    (L : E →L[ℂ] ℂ) :
    φ (HolGerm.mk (L ∘ f) (hf.mono fun _ h => L.differentiableAt.comp _ h)) =
      ∑ i, (L (parameterTensorEquiv b (banachJet d q φ f) i)) • b i := by
  rw [← scalarization_eq_coefficient_sum]
  exact (scalarize_banachJet d q φ hφ f hf L).symm

end Hironaka.Analytic.Unibranch.HironakaG10BanachJetCoordinates
