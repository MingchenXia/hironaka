import Hironaka.Analytic.Unibranch.HironakaG10OperatorJetNaturality
import Hironaka.Resolution.HironakaG10LocDirectPersistence

/-! # Parameter jets of the actual nearby operator inverse -/
set_option autoImplicit false
open Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10ActualInverseJet
open Hironaka Hironaka
  HironakaG10LocDirectPersistence
  Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
  Hironaka.Analytic.Unibranch.HironakaG10TensorBilinearExtension
  Hironaka.Analytic.Unibranch.HironakaG10OperatorJetNaturality

/-- A holomorphic bounded-operator family equal to the identity at the base
point has an actual holomorphic inverse nearby. The two actual parameter jets
are mutual inverses in the whole parameter tensor operator algebra. -/
theorem banachJet_actual_inverse
    {Γ E : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Γ)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    (C : ComplexModel d → (E →L[ℂ] E))
    (hC : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ C z)
    (hC0 : C 0 = ContinuousLinearMap.id ℂ E) :
    tensorBilinear (ContinuousLinearMap.compL ℂ E E E) (banachJet d q φ C)
        (banachJet d q φ (fun z => (C z).inverse)) =
        (1 : Γ) ⊗ₜ[ℂ] ContinuousLinearMap.id ℂ E ∧
    tensorBilinear (ContinuousLinearMap.compL ℂ E E E) (banachJet d q φ (fun z => (C z).inverse))
        (banachJet d q φ C) = (1 : Γ) ⊗ₜ[ℂ] ContinuousLinearMap.id ℂ E := by
  have hCi : ∀ᶠ z in 𝓝 (0 : ComplexModel d), (C z).IsInvertible :=
    hC.self_of_nhds.continuousAt (show {T : E →L[ℂ] E | T.IsInvertible} ∈ 𝓝 (C 0) by
      rw [hC0]
      exact isInvertible_mem_nhds_id)
  have hI : ∀ᶠ z in 𝓝 (0 : ComplexModel d),
      DifferentiableAt ℂ (fun z => (C z).inverse) z := by
    filter_upwards [hC,hCi] with z hz hzi
    exact ((hzi.contDiffAt_map_inverse (n := 1)).differentiableAt one_ne_zero).comp z hz
  have hCI : ∀ᶠ z in 𝓝 (0 : ComplexModel d),
      (C z).comp ((C z).inverse) = ContinuousLinearMap.id ℂ E :=
    hCi.mono fun _ h => h.self_comp_inverse
  have hIC : ∀ᶠ z in 𝓝 (0 : ComplexModel d),
      ((C z).inverse).comp (C z) = ContinuousLinearMap.id ℂ E :=
    hCi.mono fun _ h => h.inverse_comp_self
  exact banachJet_operator_inverse d q φ hφ C (fun z => (C z).inverse) hC hI hCI hIC

end Hironaka.Analytic.Unibranch.HironakaG10ActualInverseJet
