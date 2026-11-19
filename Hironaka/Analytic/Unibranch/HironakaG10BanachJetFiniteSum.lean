import Hironaka.Analytic.Unibranch.HironakaG10BanachJetFiniteRank

/-! # Finite-rank scalar decompositions of actual Banach parameter jets -/
set_option autoImplicit false
open Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10BanachJetFiniteSum
open Hironaka Hironaka
  Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
  Hironaka.Analytic.Unibranch.HironakaG10BanachJetFiniteRank
  Hironaka.Analytic.Unibranch.HironakaG10NormalizedBanachTaylor

/-- For an actual finite sum of scalar holomorphic functions times fixed
Banach vectors, the entire jet is the corresponding finite sum of pure
parameter tensors of the original scalar germs. -/
theorem banachJet_finite_rank_sum
    {Γ E ι : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Γ)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    (s : Finset ι) (f : ι → ComplexModel d → ℂ) (v : ι → E)
    (hf : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ (f i) z) :
    banachJet d q φ (fun z => ∑ i ∈ s, f i z • v i) =
      ∑ i ∈ s, φ (HolGerm.mk (f i) (hf i)) ⊗ₜ[ℂ] v i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have hz := banachJet_smul_const d q φ hφ (fun _ => (0 : ℂ))
      (Eventually.of_forall fun _ => differentiableAt_const 0) (0 : E)
    simpa using hz
  | @insert i s his ih =>
    have hfi := hf i
    have hfs : ∀ j ∈ s, ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ (f j) z :=
      fun j _ => hf j
    have hsum : ∀ᶠ z in 𝓝 (0 : ComplexModel d),
        DifferentiableAt ℂ (fun z => ∑ j ∈ s, f j z • v j) z := by
      filter_upwards [(eventually_all_finset s).mpr hfs] with z hz
      exact DifferentiableAt.fun_sum fun j hj => (hz j hj).smul_const (v j)
    have hterm : ∀ᶠ z in 𝓝 (0 : ComplexModel d),
        DifferentiableAt ℂ (fun z => f i z • v i) z :=
      hfi.mono fun _ h => h.smul_const (v i)
    have hfun : (fun z => ∑ j ∈ insert i s, f j z • v j) =
        (fun z => f i z • v i) + (fun z => ∑ j ∈ s, f j z • v j) := by
      funext z
      simp [his]
    rw [hfun, banachJet_add d q φ _ _
      (has_normalized_powerSeriesAt _ hterm).analyticAt.contDiffAt
      (has_normalized_powerSeriesAt _ hsum).analyticAt.contDiffAt,
      banachJet_smul_const d q φ hφ (f i) hfi (v i), ih]
    simp [his]

end Hironaka.Analytic.Unibranch.HironakaG10BanachJetFiniteSum
