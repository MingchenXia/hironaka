/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeGeometry
import Hironaka.MarkedIdeal.RestrictedIdealExtension

/-! Pullback of a sum of coherent ideals along a holomorphic map, with independent carrier universes. -/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u v

namespace Hironaka.G3UniversePullbackSum
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open NormalCrossings BlowupFlatCoordinates RegularAtDimTransport SimultaneousNormalCrossings
  DivisorExponentAlong MarkedIdeals ResolutionInvariantSpec HironakaSmoothSubmersionMonomialOrdering
  HironakaSmoothSubmersionNormalCrossings HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionDivisorExponents OrderTaylor RelativePrincipalizationSpan HadamardBridge
  RestrictedIdealExtension GermIdealPullbackCalculus IdealOrderArithmetic
  HironakaSmoothSubmersionCoefficientIdeals
noncomputable section

variable {n m : ℕ} {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) X] [ChartedSpace (ComplexModel m) Y]
  [IsComplexManifold n X] [IsComplexManifold m Y]

/-- Entire sums of coherent original ideals pull back in arbitrary ambient dimensions. -/
theorem pullback_sumIdeal_dimensions {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {I J : GermIdeal n X} (hI : I.IsCoherent) (hJ : J.IsCoherent) :
    GermIdeal.pullback (m := m) f (sumIdeal I J) =
      sumIdeal (GermIdeal.pullback (m := m) f I) (GermIdeal.pullback (m := m) f J) := by
  have hfat : ∀ {y : Y}, ∀ᶠ z in 𝓝 y,
      ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f z :=
    Eventually.of_forall fun _ => hf.contMDiffAt
  have h𝔞 : ∀ x g, I.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg
  have h𝔟 : ∀ x g, J.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hJ hg
  refine GermIdeal.ext (funext fun y => funext fun g => propext ⟨fun hg => ?_,fun hg => ?_⟩)
  · refine mem_sumIdeal_iff.mpr (IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hg))
    rintro _ ⟨a,ha,rfl⟩
    obtain ⟨_,K,r,c,hr,hc,hsum⟩ := mem_sumIdeal_iff.mp ha
    have heq : (fun p => ∑ k, (c k ∘ f) p * (r k ∘ f) p) =ᶠ[𝓝 y] a ∘ f :=
      ((hf.continuous.tendsto y).eventually hsum).mono fun p hp => hp.symm
    refine DerivativeIdeal.isInSpanAt_congr (IsInSpanAt.sum Finset.univ fun k _ => ?_) heq
    refine IsInSpanAt.mul_left ((hc k).comp_contMDiff hfat) ?_
    rcases hr k with hrk | hrk
    · refine InvertibleIdealQuotient.isInSpanAt_self (Or.inl ?_)
        ((h𝔞 _ _ hrk).comp_contMDiff hfat)
      exact GermIdeal.mem_pullback_iff.mpr (InvertibleIdealQuotient.isInSpanAt_self
        ⟨r k,hrk,rfl⟩ ((h𝔞 _ _ hrk).comp_contMDiff hfat))
    · refine InvertibleIdealQuotient.isInSpanAt_self (Or.inr ?_)
        ((h𝔟 _ _ hrk).comp_contMDiff hfat)
      exact GermIdeal.mem_pullback_iff.mpr (InvertibleIdealQuotient.isInSpanAt_self
        ⟨r k,hrk,rfl⟩ ((h𝔟 _ _ hrk).comp_contMDiff hfat))
  · refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.trans ?_ (mem_sumIdeal_iff.mp hg))
    rintro _ (hs | hs)
    · exact (GermIdeal.mem_pullback_iff.mp hs).mono fun _ ⟨a,ha,h⟩ =>
        ⟨a,le_sumIdeal_left' (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg) _ a ha,h⟩
    · exact (GermIdeal.mem_pullback_iff.mp hs).mono fun _ ⟨b,hb,h⟩ =>
        ⟨b,le_sumIdeal_right' (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hJ hg) _ b hb,h⟩

end
end Hironaka.G3UniversePullbackSum
