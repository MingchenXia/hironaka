import Hironaka.Analytic.Unibranch.HironakaG10CoefficientTensorOperator
import Hironaka.Analytic.Unibranch.HironakaG10ActualSchurJet

/-! # Original Schur jet in the Artinian coefficient model -/
set_option autoImplicit false
open Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10CoefficientSchurJet
open Hironaka Hironaka
  HironakaG10LocDirectPersistence HironakaG10LocFrischLocus
  Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
  Hironaka.Analytic.Unibranch.HironakaG10TensorBilinearExtension
  Hironaka.Analytic.Unibranch.HironakaG10CoefficientTensorOperator
  Hironaka.Analytic.Unibranch.HironakaG10ActualInverseJet
  Hironaka.Analytic.Unibranch.HironakaG10ActualSchurJet
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators

/-- The original Schur family acts on every coefficient vector as the
composition of its three original, scalar-extended operator jets. -/
theorem coefficientTensorOperator_actual_schur
    {Γ E₁ E₀ ι : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀] [CompleteSpace E₀]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ Γ)
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Γ)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    (P : E₁ →L[ℂ] E₁) (Q : E₀ →L[ℂ] E₀) (S₀ : E₀ →L[ℂ] E₁)
    (f : ComplexModel d → (E₁ →L[ℂ] E₀))
    (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ f z)
    (hC0 : opC P Q S₀ (f 0) = ContinuousLinearMap.id ℂ E₀) :
    coefficientTensorOperator (E := E₁) (F := E₀) b
      (banachJet (E := E₁ →L[ℂ] E₀) d q φ (fun z => schurOp P Q S₀ (f z))) =
      (coefficientCLM (ContinuousLinearMap.id ℂ E₀ - Q)).toLinearMap.comp
        ((coefficientTensorOperator (E := E₀) (F := E₀) b
          (banachJet (E := E₀ →L[ℂ] E₀) d q φ (fun z => (opC P Q S₀ (f z)).inverse))).comp
          (coefficientTensorOperator (E := E₁) (F := E₀) b (banachJet (E := E₁ →L[ℂ] E₀) d q φ f))) := by
  rw [banachJet_actual_schur d q φ hφ P Q S₀ f hf hC0,
    coefficientTensorOperator_comp, coefficientTensorOperator_comp,
    coefficientTensorOperator_one]

end Hironaka.Analytic.Unibranch.HironakaG10CoefficientSchurJet
