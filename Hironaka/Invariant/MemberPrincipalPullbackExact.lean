/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.MemberPullback

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.MemberPullback
open Hironaka Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupFlatCoordinates BlowupMonomialCharts BlowupLocalSurjectivity BlowupExceptionalDivisor BlowupStrictSubmanifold BlowupStrictIdeal BlowupSNCTransform NormalCrossings SimultaneousNormalCrossings RelativePrincipalizationSpan DerivativeIdeal
noncomputable section
variable {n : ℕ}
section Principal
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- Generators that agree near the point span the same germs. -/
theorem isInSpanAt_eq_congr {x : M} {h h' : M → ℂ} (hhh' : h =ᶠ[𝓝 x] h') (g : M → ℂ) :
    IsInSpanAt (n := n) (· = h) x g ↔ IsInSpanAt (n := n) (· = h') x g := by
  constructor
  · intro hg
    obtain ⟨hgh, a, ha, heq⟩ := isInSpanAt_eq_iff.mp hg
    refine isInSpanAt_eq_iff.mpr ⟨hgh, a, ha, ?_⟩
    filter_upwards [heq, hhh'] with y h1 h2
    rw [h1, h2]
  · intro hg
    obtain ⟨hgh, a, ha, heq⟩ := isInSpanAt_eq_iff.mp hg
    refine isInSpanAt_eq_iff.mpr ⟨hgh, a, ha, ?_⟩
    filter_upwards [heq, hhh'] with y h1 h2
    rw [h1, h2]


end Principal
section Pullback
variable {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- **The pullback of a principal ideal is principal**: if `𝔞 = (h)` at `f z`, then `f^*𝔞 = (h ∘ f)`
at `z`. -/
theorem pullback_mem_iff_of_generator {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f) {𝔞 : GermIdeal n X}
    {h : X → ℂ} {z : Y} (hh : HolomorphicAt n h (f z))
    (hgen : ∀ g, 𝔞.mem (f z) g ↔ IsInSpanAt (n := n) (· = h) (f z) g) (g : Y → ℂ) :
    (GermIdeal.pullback (m := n) f 𝔞).mem z g ↔ IsInSpanAt (n := n) (· = h ∘ f) z g := by
  have hfat : ∀ᶠ y in 𝓝 z, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f y :=
    Eventually.of_forall fun y => hf y
  constructor
  · intro hg
    refine IsInSpanAt.of_forall_eq_mul ?_ (GermIdeal.mem_pullback_iff.mp hg)
    rintro s ⟨a, ha, rfl⟩
    obtain ⟨-, c, hc, hac⟩ := isInSpanAt_eq_iff.mp ((hgen a).mp ha)
    refine ⟨c ∘ f, hc.comp_contMDiff hfat, ?_⟩
    filter_upwards [hf.continuous.continuousAt.eventually hac] with y hy
    exact hy
  · intro hg
    refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.trans (fun s hs => ?_) hg)
    subst hs
    exact isInSpanAt_of_eq_mul ⟨h, (hgen h).mpr (isInSpanAt_of_eq_mul rfl hh
      (holomorphicAt_const 1) (Eventually.of_forall fun _ => by simp)), rfl⟩
      (hh.comp_contMDiff hfat) (holomorphicAt_const 1) (Eventually.of_forall fun _ => by simp)

end Pullback
end
end Hironaka.MemberPullback
