import Hironaka.Analytic.Unibranch.HironakaG10ActualSchurJet

/-! Holomorphy of the actual Schur family near its original exact start. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace Hironaka.Analytic.Unibranch.HironakaG10ActualSchurHolomorphic
open Hironaka Hironaka
  HironakaG10LocDirectPersistence HironakaG10LocFrischLocus

/-- At an identity comparison operator, the actual Frisch Schur family
is holomorphic on one neighborhood of the original parameter point. -/
theorem actual_schur_holomorphic
    {E₁ E₀ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₀] [NormedSpace ℂ E₀] [CompleteSpace E₀]
    (d : ℕ) (P : E₁ →L[ℂ] E₁) (Q : E₀ →L[ℂ] E₀) (S₀ : E₀ →L[ℂ] E₁)
    (f : ComplexModel d → (E₁ →L[ℂ] E₀))
    (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ f z)
    (hC0 : opC P Q S₀ (f 0) = ContinuousLinearMap.id ℂ E₀) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ (fun z => schurOp P Q S₀ (f z)) z := by
  let C : ComplexModel d → (E₀ →L[ℂ] E₀) := fun z => opC P Q S₀ (f z)
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
  filter_upwards [hI,hf] with z hz hfz
  change DifferentiableAt ℂ (fun z => (ContinuousLinearMap.id ℂ E₀ - Q).comp
    ((C z).inverse.comp (f z))) z
  exact (differentiableAt_const _).clm_comp (hz.clm_comp hfz)
end Hironaka.Analytic.Unibranch.HironakaG10ActualSchurHolomorphic
