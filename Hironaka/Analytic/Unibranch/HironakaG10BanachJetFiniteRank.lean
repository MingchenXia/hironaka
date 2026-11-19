import Hironaka.Analytic.Unibranch.HironakaG10BanachJetScalarization

/-! # Actual jets of finite-rank holomorphic parameter families -/
set_option autoImplicit false
open Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10BanachJetFiniteRank
open Hironaka Hironaka
  Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
  Hironaka.Analytic.Unibranch.HironakaG10BanachJetScalarization
  Hironaka.Analytic.Unibranch.HironakaG10NormalizedBanachTaylor

/-- Finite parameter jets preserve addition of actual smooth families. -/
theorem banachJet_add
    {Γ E : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Γ)
    (f g : ComplexModel d → E) (hf : ContDiffAt ℂ ⊤ f 0) (hg : ContDiffAt ℂ ⊤ g 0) :
    banachJet d q φ (f+g) = banachJet d q φ f + banachJet d q φ g := by
  classical
  simp only [banachJet, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro w hw
  rw [iteratedFDeriv_add_apply (hf.of_le (by simp)) (hg.of_le (by simp))]
  simp only [add_apply, smul_add, TensorProduct.tmul_add]

/-- The jet of an actual scalar holomorphic germ times a fixed Banach vector
is precisely the corresponding pure parameter tensor. -/
theorem banachJet_smul_const
    {Γ E : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Γ)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    (f : ComplexModel d → ℂ)
    (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ f z) (e : E) :
    banachJet d q φ (fun z => f z • e) = φ (HolGerm.mk f hf) ⊗ₜ[ℂ] e := by
  let I : ℂ →L[ℂ] ℂ := ContinuousLinearMap.id ℂ ℂ
  let T : ℂ →L[ℂ] E := I.smulRight e
  have hc : ContDiffAt ℂ ⊤ f 0 := (has_normalized_powerSeriesAt f hf).analyticAt.contDiffAt
  have hscalar := scalarize_banachJet d q φ hφ f hf I
  have hjet : banachJet d q φ f = φ (HolGerm.mk f hf) ⊗ₜ[ℂ] (1 : ℂ) := by
    apply (TensorProduct.rid ℂ Γ).injective
    simpa [I] using hscalar
  have hm := banachJet_map d q φ f hc T
  rw [hjet, LinearMap.baseChange_tmul] at hm
  have hfun : T ∘ f = fun z => f z • e := by
    funext z
    simp [T,I]
  rw [hfun] at hm
  simpa [T,I] using hm

end Hironaka.Analytic.Unibranch.HironakaG10BanachJetFiniteRank
