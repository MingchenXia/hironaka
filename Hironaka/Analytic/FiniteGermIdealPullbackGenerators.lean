/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.FiniteSpanRangeExact
import Hironaka.Coherence.CoherentIdealColon
import Hironaka.Analytic.IdealSpanCalculus

set_option autoImplicit false

/-! # The actual ideal pullback retains the complete literal original finite generators -/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.FiniteGermIdealPullbackGenerators

open Hironaka.HolomorphicIdealSheaves RelativePrincipalizationSpan
  InvertibleIdealQuotient

noncomputable section

/-- The actual ideal pullback has exactly the literal original finite generators composed with f. -/
theorem mem_pullback_iff_of_finite_generation {n m s : ℕ} {X Y : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
    {f : Y → X} {y : Y}
    (hf : ∀ᶠ z in 𝓝 y, ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f z)
    (I : GermIdeal n X) (G : Fin s → X → ℂ)
    (hG : ∀ i, HolomorphicAt n (G i) (f y))
    (hgen : ∀ a : X → ℂ, I.mem (f y) a ↔
      IsInSpanAt (n := n) (· ∈ Set.range G) (f y) a) (F : Y → ℂ) :
    (GermIdeal.pullback (m := m) f I).mem y F ↔
      IsInSpanAt (n := m) (· ∈ Set.range fun i => G i ∘ f) y F := by
  have hcont : ContinuousAt f y := hf.self_of_nhds.continuousAt
  constructor
  · intro hF
    apply RelativePrincipalizationSpan.IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hF)
    rintro a ⟨b, hb, rfl⟩
    obtain ⟨hbh, c, hc, heq⟩ := CoherentIdealColon.isInSpanAt_range_iff.mp ((hgen b).mp hb)
    apply CoherentIdealColon.isInSpanAt_range_iff.mpr
    exact ⟨hbh.comp_contMDiff hf, fun i => c i ∘ f,
      fun i => (hc i).comp_contMDiff hf, hcont.eventually heq⟩
  · intro hF
    apply GermIdeal.mem_pullback_iff.mpr
    apply RelativePrincipalizationSpan.IsInSpanAt.trans ?_ hF
    rintro _ ⟨i, rfl⟩
    have hi : I.mem (f y) (G i) := (hgen (G i)).mpr (isInSpanAt_self ⟨i, rfl⟩ (hG i))
    exact isInSpanAt_self ⟨G i, hi, rfl⟩ ((hG i).comp_contMDiff hf)

/-- Actual coherence chooses all source generators and supplies their full target presentation. -/
theorem exists_finite_generators_pullback_of_isCoherent {n m : ℕ} {X Y : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]
    {f : Y → X} {y : Y}
    (hf : ∀ᶠ z in 𝓝 y, ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f z)
    (I : GermIdeal n X) (hI : I.IsCoherent) :
    ∃ U : Set X, IsOpen U ∧ f y ∈ U ∧ ∃ (s : ℕ) (G : Fin s → X → ℂ),
      (∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (G i) U) ∧
      (∀ x ∈ U, ∀ a : X → ℂ, I.mem x a ↔
        IsInSpanAt (n := n) (· ∈ Set.range G) x a) ∧
      (∀ F : Y → ℂ, (GermIdeal.pullback (m := m) f I).mem y F ↔
        IsInSpanAt (n := m) (· ∈ Set.range fun i => G i ∘ f) y F) := by
  obtain ⟨U, hU, hyU, s, G, hG, hgen⟩ := hI (f y)
  refine ⟨U, hU, hyU, s, G, hG, hgen, ?_⟩
  exact mem_pullback_iff_of_finite_generation hf I G
    (fun i => holomorphicAt_of_mdifferentiableOn hU (hG i) hyU) (hgen (f y) hyU)

end
end Hironaka.FiniteGermIdealPullbackGenerators
