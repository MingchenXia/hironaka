import Hironaka.MarkedIdeal.MarkedIdealOperationsTransform
import Hironaka.Invariant.IdealOrderArithmetic
import Hironaka.Analytic.RegularAtDimTransport
import Hironaka.Blowup.BlowupExistenceCodimOne
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u v w
namespace Hironaka.G3UniverseVanishingIdeal
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  GermIdealOrder IdealWeightPowers GermIdealTotalTransform GermIdealPullbackCalculus
  HadamardBridge MarkedIdeals BlowupStrictSubmanifold IdealOrderArithmetic
noncomputable section
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {M' : Type v} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']
  {φ : M' → M} {ψ : M → M'}
theorem pullback_vanishingIdeal_preimage {m : ℕ} {Z : Type w} [TopologicalSpace Z]
    [ChartedSpace (ComplexModel m) Z] [IsComplexManifold m Z] {g : Z → M'}
    (hφ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ φ)
    (hψ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ψ)
    (hφψ : ∀ x, φ (ψ x) = x) (hψφ : ∀ p, ψ (φ p) = p)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g) (A : Set M) :
    GermIdeal.pullback (m := m) g (vanishingIdeal (n := n) (φ ⁻¹' A)) =
      GermIdeal.pullback (m := m) (φ ∘ g) (vanishingIdeal (n := n) A) := by
  have hφd : ∀ q, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) φ q :=
    fun q => (hφ q).mdifferentiableAt (by simp)
  have hψd : ∀ q, MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ψ q :=
    fun q => (hψ q).mdifferentiableAt (by simp)
  have hgd : ∀ q, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) g q :=
    fun q => (hg q).mdifferentiableAt (by simp)
  have hφgd : ∀ q, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) (φ ∘ g) q :=
    fun q => (hφd (g q)).comp q (hgd q)
  refine GermIdeal.ext (funext fun z => funext fun f => propext ⟨fun hf => ?_, fun hf => ?_⟩)
  · refine RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
      (RelativePrincipalizationSpan.IsInSpanAt.trans ?_
        (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hf))
    rintro s ⟨t, ht, rfl⟩
    have htψ : (vanishingIdeal (n := n) A).mem ((φ ∘ g) z) (t ∘ ψ) := by
      refine ⟨?_, ?_⟩
      · have h1 : HolomorphicAt n t (ψ ((φ ∘ g) z)) := by
          simpa only [Function.comp_apply, hψφ] using ht.1
        exact holomorphicAt_comp_map (Eventually.of_forall hψd) h1
      · have hT : Tendsto ψ (𝓝 ((φ ∘ g) z)) (𝓝 (g z)) := by
          have := (hψ.continuous.tendsto ((φ ∘ g) z))
          simpa only [Function.comp_apply, hψφ] using this
        filter_upwards [hT.eventually ht.2] with a ha haA
        exact ha (by simp only [mem_preimage, hφψ]; exact haA)
    have heq : t ∘ g = (t ∘ ψ) ∘ (φ ∘ g) := funext fun q => by simp [hψφ]
    rw [heq]
    exact InvertibleIdealQuotient.isInSpanAt_self ⟨t ∘ ψ, htψ, rfl⟩
      (holomorphicAt_comp_map (Eventually.of_forall hφgd) htψ.1)
  · refine RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
      (RelativePrincipalizationSpan.IsInSpanAt.trans ?_
        (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hf))
    rintro s ⟨t, ht, rfl⟩
    have htφ : (vanishingIdeal (n := n) (φ ⁻¹' A)).mem (g z) (t ∘ φ) := by
      refine ⟨holomorphicAt_comp_map (Eventually.of_forall hφd) ht.1, ?_⟩
      filter_upwards [(hφ.continuous.tendsto (g z)).eventually ht.2] with a ha haA
      exact ha haA
    exact InvertibleIdealQuotient.isInSpanAt_self (S := fun s => ∃ a,
        (vanishingIdeal (n := n) (φ ⁻¹' A)).mem (g z) a ∧ s = a ∘ g) ⟨t ∘ φ, htφ, rfl⟩
      (show HolomorphicAt m ((t ∘ φ) ∘ g) z from holomorphicAt_comp_map (Eventually.of_forall hgd) htφ.1)

end
end Hironaka.G3UniverseVanishingIdeal
