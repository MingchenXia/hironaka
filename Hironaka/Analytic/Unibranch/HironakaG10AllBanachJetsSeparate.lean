import Hironaka.Analytic.Unibranch.HironakaG10BanachJetScalarization
import Hironaka.Resolution.HironakaG10ArtinianFlatQuotient
import Hironaka.Resolution.HironakaActualWholeIdealJetDetection
import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-! All original finite parameter jets detect a Banach-valued holomorphic germ. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Filter Set
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10AllBanachJetsSeparate
open Hironaka Hironaka
  HolGerm OkaGermBridge HironakaRelativeNormalIdeal
  HironakaG10ArtinianBaseChange HironakaG10ArtinianFlatQuotient
  HironakaActualWholeIdealJetDetection
  Hironaka.Analytic.Unibranch.HironakaG10BanachParameterJet
  Hironaka.Analytic.Unibranch.HironakaG10BanachJetScalarization
  Hironaka.Analytic.Unibranch.HironakaG10NormalizedBanachTaylor
noncomputable section
local instance (n : ℕ) : Algebra ℂ (HolGerm (ComplexModel n)) :=
  (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel n)).toAlgebra

/-- A Banach-valued holomorphic family whose actual parameter jets vanish
in every maximal-ideal truncation vanishes on one neighborhood. -/
theorem eventually_zero_of_all_banachJets_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (d : ℕ) (f : ComplexModel d → E)
    (hf : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ f x)
    (hjets : ∀ q : ℕ, banachJet d q (parameterQuotientMap d q ⊥) f = 0) :
    f =ᶠ[𝓝 (0 : ComplexModel d)] fun _ => 0 := by
  have hscalar (L : E →L[ℂ] ℂ) : (L ∘ f) =ᶠ[𝓝 (0 : ComplexModel d)] fun _ => 0 := by
    have hL : ∀ᶠ z in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ (L ∘ f) z :=
      hf.mono fun _ h => L.differentiableAt.comp _ h
    let g : HolGerm (ComplexModel d) := HolGerm.mk (L ∘ f) hL
    have hg : g ∈ (⊥ : Ideal (HolGerm (ComplexModel d))) := by
      apply (mem_original_ideal_iff_all_positive_thickenings ⊥ g).mpr
      intro q
      have hq := scalarize_banachJet d q (parameterQuotientMap d q ⊥)
        (parameterQuotientMap_kills d q ⊥) f hf L
      rw [hjets q] at hq
      have hmap : (parameterQuotientMap d q ⊥) g = 0 := by simpa [g] using hq.symm
      exact Ideal.Quotient.eq_zero_iff_mem.mp hmap
    have hg0 : g = 0 := Ideal.mem_bot.mp hg
    apply (germAt_eq_zero_iff hL).mp
    rw [germAt_of_holAt hL]
    simpa only [g, zero_add, Function.comp_def] using hg0
  have hc : ContDiffAt ℂ ⊤ f 0 := (has_normalized_powerSeriesAt f hf).analyticAt.contDiffAt
  have hderiv : ∀ k : ℕ, iteratedFDeriv ℂ k f 0 = 0 := by
    intro k
    ext v
    apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ)
    intro L
    have hs := ((hscalar L).iteratedFDeriv ℂ k).self_of_nhds
    have hcomp := L.iteratedFDeriv_comp_left hc (i := k) (by simp)
    have hv := congrArg (fun T => T v) hs
    simpa [hcomp] using hv
  have hseries := has_normalized_powerSeriesAt f hf
  have hz : (fun n => (Nat.factorial n : ℂ)⁻¹ • iteratedFDeriv ℂ n f 0) = 0 := by
    funext n
    simp [hderiv n]
  rw [hz] at hseries
  exact hseries.eventually_eq_zero
end
end Hironaka.Analytic.Unibranch.HironakaG10AllBanachJetsSeparate
