import Hironaka.Analytic.Unibranch.HironakaG10ActualInverseJet
import Hironaka.Resolution.HironakaG10LocFrischLocus

/-! # The actual Frisch Schur operator after finite parameter substitution -/
set_option autoImplicit false
open Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10ActualSchurJet
open Hironaka Hironaka
  HironakaG10LocDirectPersistence HironakaG10LocFrischLocus
  Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
  Hironaka.Analytic.Unibranch.HironakaG10TensorBilinearExtension
  Hironaka.Analytic.Unibranch.HironakaG10OperatorJetNaturality

/-- The actual holomorphic Frisch Schur operator has the explicitly composed
whole parameter jet, using the actual nearby inverse family. -/
theorem banachJet_actual_schur
    {Γ E₁ E₀ : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀] [CompleteSpace E₀]
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Γ)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    (P : E₁ →L[ℂ] E₁) (Q : E₀ →L[ℂ] E₀) (S₀ : E₀ →L[ℂ] E₁)
    (f : ComplexModel d → (E₁ →L[ℂ] E₀))
    (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ f z)
    (hC0 : opC P Q S₀ (f 0) = ContinuousLinearMap.id ℂ E₀) :
    banachJet d q φ (fun z => schurOp P Q S₀ (f z)) =
      tensorBilinear (ContinuousLinearMap.compL ℂ E₁ E₀ E₀)
        ((1 : Γ) ⊗ₜ[ℂ] (ContinuousLinearMap.id ℂ E₀ - Q))
        (tensorBilinear (ContinuousLinearMap.compL ℂ E₁ E₀ E₀)
          (banachJet d q φ (fun z => (opC P Q S₀ (f z)).inverse))
          (banachJet d q φ f)) := by
  let C := fun z => opC P Q S₀ (f z)
  have hC : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ C z := by
    filter_upwards [hf] with z hz
    exact (hz.clm_comp (differentiableAt_const _)).add (differentiableAt_const _)
  have hCi : ∀ᶠ z in 𝓝 (0 : ComplexModel d), (C z).IsInvertible :=
    hC.self_of_nhds.continuousAt (show {T : E₀ →L[ℂ] E₀ | T.IsInvertible} ∈ 𝓝 (C 0) by
      rw [show C 0 = ContinuousLinearMap.id ℂ E₀ from hC0]
      exact isInvertible_mem_nhds_id)
  have hI : ∀ᶠ z in 𝓝 (0 : ComplexModel d),
      DifferentiableAt ℂ (fun z => (C z).inverse) z := by
    filter_upwards [hC,hCi] with z hz hzi
    exact ((hzi.contDiffAt_map_inverse (n := 1)).differentiableAt one_ne_zero).comp z hz
  have hinner : ∀ᶠ z in 𝓝 (0 : ComplexModel d),
      DifferentiableAt ℂ (fun z => (C z).inverse.comp (f z)) z := by
    filter_upwards [hI,hf] with z hz hfz
    exact hz.clm_comp hfz
  have hc : ∀ᶠ z in 𝓝 (0 : ComplexModel d),
      DifferentiableAt ℂ (fun _ => ContinuousLinearMap.id ℂ E₀ - Q) z :=
    Eventually.of_forall fun _ => differentiableAt_const _
  change banachJet d q φ (fun z => (ContinuousLinearMap.id ℂ E₀ - Q).comp
      ((C z).inverse.comp (f z))) = _
  rw [banachJet_operator_comp d q φ hφ _ _ hc hinner,
    banachJet_const d q φ hφ,
    banachJet_operator_comp d q φ hφ _ _ hI hf]

end Hironaka.Analytic.Unibranch.HironakaG10ActualSchurJet
