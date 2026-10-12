/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.MarkedIdealOperationsTransform
import Hironaka.Blowup.BlowupControlledTransform
import Hironaka.Blowup.ControlledTransformUniqueness

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.MarkedIdealOperationsTransform
open Hironaka Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open GermIdealOrder IdealWeightPowers RestrictedIdealExtension GermIdealTotalTransform GermIdealPullbackCalculus BlowupExceptionalDivisor BlowupControlledTransform IdealOrderArithmetic BlowupTowers MarkedIdeals
noncomputable section
variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {C : Set X} {π : Y → X} {𝔞 𝔟 : GermIdeal n X} {μ ν : ℕ}

theorem isCoherent_D (hπ : IsBlowupAlong n C π) (μ : ℕ) :
    (idealPow (exceptionalDivisor hπ).ideal μ).IsCoherent :=
  isCoherent_idealPow (isCoherent_ideal _) μ

/-- **`σ^c(𝔞𝔟, μ + ν) = σ^c(𝔞, μ) σ^c(𝔟, ν)`**. -/
theorem controlledTransform_mul (hπ : IsBlowupAlong n C π) (h𝔞 : 𝔞.IsCoherent) (h𝔟 : 𝔟.IsCoherent)
    (hle𝔞 : 𝔞.Le (idealPow (vanishingIdeal (n := n) C) μ))
    (hle𝔟 : 𝔟.Le (idealPow (vanishingIdeal (n := n) C) ν)) :
    controlledTransform hπ (𝔞.mul 𝔟) (μ + ν) =
      (controlledTransform hπ 𝔞 μ).mul (controlledTransform hπ 𝔟 ν) := by
  have hc𝔞 := isCoherent_controlledTransform hπ h𝔞 hle𝔞
  have hc𝔟 := isCoherent_controlledTransform hπ h𝔟 hle𝔟
  refine (eq_controlledTransform_of_eq_mul hπ (IdealWeightPowers.isCoherent_mul hc𝔞 hc𝔟) ?_).symm
  rw [pullback_mul hπ.contMDiff h𝔞 h𝔟, pullback_eq_mul_controlledTransform hπ h𝔞 hle𝔞,
    pullback_eq_mul_controlledTransform hπ h𝔟 hle𝔟,
    mul_mul_mul_comm (isCoherent_D hπ μ) hc𝔞 (isCoherent_D hπ ν) hc𝔟,
    ← RestrictLeCalculus.idealPow_add (isCoherent_ideal _)]


end
end Hironaka.MarkedIdealOperationsTransform
