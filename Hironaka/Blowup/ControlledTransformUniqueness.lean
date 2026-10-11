/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupControlledTransform

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.BlowupControlledTransform
open Hironaka
noncomputable section
open BlowupSequences HolomorphicIdealSheaves GermIdealTotalTransform GermIdealPullbackCalculus
open IdealWeightPowers InvertibleIdealQuotient RelativePrincipalizationSpan BlowupExceptionalDivisor
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Cancellation of an invertible ideal**: `(𝔩 𝔠 : 𝔩) = 𝔠` for `𝔩` invertible and `𝔠`
coherent. -/
theorem colon_mul_eq {𝔩 𝔠 : GermIdeal n M} (h𝔩 : 𝔩.IsInvertible) (h𝔠 : 𝔠.IsCoherent) :
    colon (𝔩.mul 𝔠) 𝔩 = 𝔠 := by
  refine GermIdeal.ext (funext fun x => funext fun f => propext ⟨fun hf => ?_, fun hf => ?_⟩)
  · obtain ⟨hfhol, hfmul⟩ := mem_colon_iff.mp hf
    obtain ⟨U, hU, hxU, h₀, hh₀d, hnon, hgen⟩ := h𝔩 x
    have hh₀ : HolomorphicAt n h₀ x := holomorphicAt_of_mdifferentiableOn hU hh₀d hxU
    have hh₀mem : 𝔩.mem x h₀ := (hgen x hxU h₀).mpr (isInSpanAt_self rfl hh₀)
    obtain ⟨-, K, u, c, hu, hc, husum⟩ := mem_mul_iff.mp (hfmul h₀ hh₀mem)
    choose p q hp hq hpq using hu
    choose e he hee using fun j => (isInSpanAt_eq_iff.mp ((hgen x hxU (p j)).mp (hp j))).2
    have hqhol : ∀ j, HolomorphicAt n (q j) x :=
      fun j => GermIdeal.IsCoherent.holomorphicAt_mem h𝔠 (hq j)
    have hFhol : HolomorphicAt n (fun y => ∑ j, (c j y * e j y) * q j y) x :=
      HolomorphicAt.sum _ fun j _ => ((hc j).mul (he j)).mul (hqhol j)
    have hfeq : f =ᶠ[𝓝 x] fun y => ∑ j, (c j y * e j y) * q j y := by
      refine eventuallyEq_of_mul_eventuallyEq hU hnon hxU hfhol hFhol ?_
      filter_upwards [husum, eventually_all.mpr hee] with y hy hy'
      rw [hy, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hpq j]
      show c j y * (p j y * q j y) = h₀ y * (c j y * e j y * q j y)
      rw [hy' j]
      ring
    exact mem_of_isInSpanAt_mem h𝔠
      ⟨hfhol, K, q, fun j y => c j y * e j y, hq, fun j => (hc j).mul (he j), hfeq⟩
  · refine mem_colon_iff.mpr ⟨GermIdeal.IsCoherent.holomorphicAt_mem h𝔠 hf, fun g hg => ?_⟩
    have hghol : HolomorphicAt n g x := GermIdeal.IsInvertible.holomorphicAt_mem h𝔩 hg
    exact mem_mul_of_mem_mem hg hf (hghol.mul (GermIdeal.IsCoherent.holomorphicAt_mem h𝔠 hf))


universe u
variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- **Uniqueness of the controlled transform**: a coherent `𝔠` with `π^*𝔞 = 𝒪_Y(-μD) · 𝔠` is the
controlled transform (Wlodarczyk: "the controlled transform is well defined"). -/
theorem eq_controlledTransform_of_eq_mul (hπ : IsBlowupAlong n C π)
    {𝔞 : GermIdeal n X} {μ : ℕ} {𝔠 : GermIdeal n Y} (h𝔠 : 𝔠.IsCoherent)
    (heq : GermIdeal.pullback (m := n) π 𝔞 = (idealPow (exceptionalDivisor hπ).ideal μ).mul 𝔠) :
    𝔠 = controlledTransform hπ 𝔞 μ := by
  rw [controlledTransform, heq, colon_mul_eq (isInvertible_idealPow_exceptionalDivisor hπ μ) h𝔠]


end
end Hironaka.BlowupControlledTransform
