import Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
import Hironaka.Analytic.Unibranch.HironakaG10ScalarTaylorEvaluation

/-! # Scalar evaluation of the actual Banach parameter jet -/
set_option autoImplicit false
open Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10BanachJetScalarization
open Hironaka Hironaka
  HironakaHolomorphicJetMonomialSpan HironakaRelativeNormalIdeal
open Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
  Hironaka.Analytic.Unibranch.HironakaG10ScalarTaylorEvaluation
  Hironaka.Analytic.Unibranch.HironakaG10NormalizedBanachTaylor

private theorem scalar_taylor_transport
    {Γ : Type*} [CommRing Γ] [Algebra ℂ Γ] (d q n : ℕ) (h : n = 0+d)
    (φ : HolGerm (ComplexModel n) →ₐ[ℂ] Γ)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    (g : ComplexModel n → ℂ)
    (hg : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ g z) :
    φ (HolGerm.mk g hg) =
      ∑ k ∈ Finset.range (q+1), ∑ w : Fin k → Fin d,
        φ (∏ i : Fin k, coordinateGerm (Fin.cast h.symm ((w i).natAdd 0))) *
          algebraMap ℂ Γ ((Nat.factorial k : ℂ)⁻¹ • (iteratedFDeriv ℂ k g 0)
            (fun i => EuclideanSpace.single (Fin.cast h.symm ((w i).natAdd 0)) (1 : ℂ))) := by
  subst n
  simpa only [Fin.cast_refl, id_eq, normalCoordinate] using
    scalar_germ_eq_finite_taylor d q φ hφ g hg

/-- Continuous scalarization of the actual finite Banach jet is exactly the
  original scalar holomorphic germ evaluated in the given Artinian test map. -/
theorem scalarize_banachJet
    {Γ E : Type*} [CommRing Γ] [Algebra ℂ Γ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (d q : ℕ) (φ : HolGerm (ComplexModel d) →ₐ[ℂ] Γ)
    (hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom)
    (f : ComplexModel d → E)
    (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ f z)
    (L : E →L[ℂ] ℂ) :
    (TensorProduct.rid ℂ Γ) (L.toLinearMap.baseChange Γ (banachJet d q φ f)) =
      φ (HolGerm.mk (L ∘ f) (hf.mono fun _ h => L.differentiableAt.comp _ h)) := by
  classical
  have hc : ContDiffAt ℂ ⊤ f 0 := (has_normalized_powerSeriesAt f hf).analyticAt.contDiffAt
  rw [← banachJet_map d q φ f hc L]
  have hs := scalar_taylor_transport d q d (Nat.zero_add d).symm φ hφ (L ∘ f)
    (hf.mono fun _ h => L.differentiableAt.comp _ h)
  have hcast (i : Fin d) : Fin.cast (Nat.zero_add d) (i.natAdd 0) = i := by
    apply Fin.ext
    simp
  simp only [hcast] at hs
  rw [hs]
  simp only [banachJet, map_sum, TensorProduct.rid_tmul, Algebra.smul_def]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro w hw
  exact mul_comm _ _

end Hironaka.Analytic.Unibranch.HironakaG10BanachJetScalarization
