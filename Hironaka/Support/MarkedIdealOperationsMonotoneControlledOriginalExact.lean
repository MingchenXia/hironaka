/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.MarkedIdeal.MarkedIdealOperationsTransform
import Hironaka.MarkedIdeal.ControlledProductTransformExact

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MarkedIdealOperationsTransform

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.GermIdealOrder Hironaka.IdealWeightPowers
  Hironaka.RestrictedIdealExtension Hironaka.GermIdealTotalTransform
  Hironaka.GermIdealPullbackCalculus Hironaka.BlowupExceptionalDivisor
  Hironaka.BlowupControlledTransform Hironaka.IdealOrderArithmetic
  Hironaka.BlowupTowers Hironaka.MarkedIdeals

noncomputable section

section Algebra

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Products are monotone. -/
theorem mul_le_mul' {𝔞 𝔞' 𝔟 𝔟' : GermIdeal n M} (h𝔞 : 𝔞.Le 𝔞') (h𝔟 : 𝔟.Le 𝔟') :
    (𝔞.mul 𝔟).Le (𝔞'.mul 𝔟') := fun x _ hg =>
  mem_mul_iff.mpr ((mem_mul_iff.mp hg).mono fun _ ⟨a, b, ha, hb, hs⟩ => ⟨a, b, h𝔞 x a ha, h𝔟 x b hb, hs⟩)

/-- Powers are monotone in the ideal. -/
theorem idealPow_mono {𝔞 𝔟 : GermIdeal n M} (h : 𝔞.Le 𝔟) :
    ∀ k : ℕ, (idealPow 𝔞 k).Le (idealPow 𝔟 k)
  | 0 => fun _ _ hg => hg
  | k + 1 => mul_le_mul' (idealPow_mono h k) h

end Algebra

section Controlled

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X} {𝔞 𝔟 : GermIdeal n X} {μ ν : ℕ}

/-- **`σ^c(𝔞^k, μk) = σ^c(𝔞, μ)^k`**. -/
theorem controlledTransform_idealPow (hπ : IsBlowupAlong n C π) (h𝔞 : 𝔞.IsCoherent)
    (hle𝔞 : 𝔞.Le (idealPow (vanishingIdeal (n := n) C) μ)) (k : ℕ) :
    controlledTransform hπ (idealPow 𝔞 k) (μ * k) = idealPow (controlledTransform hπ 𝔞 μ) k := by
  have hc𝔞 := isCoherent_controlledTransform hπ h𝔞 hle𝔞
  refine (eq_controlledTransform_of_eq_mul hπ (isCoherent_idealPow hc𝔞 k) ?_).symm
  rw [BlowupExceptionalDivisor.pullback_idealPow hπ.contMDiff h𝔞,
    pullback_eq_mul_controlledTransform hπ h𝔞 hle𝔞, idealPow_mul (isCoherent_D hπ μ) hc𝔞,
    idealPow_idealPow (isCoherent_ideal _)]

/-- **`σ^c(𝔞 + 𝔟, μ) = σ^c(𝔞, μ) + σ^c(𝔟, μ)`**. -/
theorem controlledTransform_sumIdeal (hπ : IsBlowupAlong n C π) (h𝔞 : 𝔞.IsCoherent)
    (h𝔟 : 𝔟.IsCoherent) (hle𝔞 : 𝔞.Le (idealPow (vanishingIdeal (n := n) C) μ))
    (hle𝔟 : 𝔟.Le (idealPow (vanishingIdeal (n := n) C) μ)) :
    controlledTransform hπ (sumIdeal 𝔞 𝔟) μ =
      sumIdeal (controlledTransform hπ 𝔞 μ) (controlledTransform hπ 𝔟 μ) := by
  have hc𝔞 := isCoherent_controlledTransform hπ h𝔞 hle𝔞
  have hc𝔟 := isCoherent_controlledTransform hπ h𝔟 hle𝔟
  have hol : ∀ {𝔠 : GermIdeal n Y}, 𝔠.IsCoherent → ∀ y g, 𝔠.mem y g → HolomorphicAt n g y :=
    fun h𝔠 _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔠 hg
  refine (eq_controlledTransform_of_eq_mul hπ (isCoherent_sumIdeal hc𝔞 hc𝔟) ?_).symm
  rw [pullback_sumIdeal hπ.contMDiff (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg)
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔟 hg),
    pullback_eq_mul_controlledTransform hπ h𝔞 hle𝔞, pullback_eq_mul_controlledTransform hπ h𝔟 hle𝔟,
    mul_sumIdeal (hol (isCoherent_D hπ μ)) (hol hc𝔞) (hol hc𝔟)]

end Controlled

end

end Hironaka.MarkedIdealOperationsTransform
