/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.MarkedIdeal.HadamardBridge

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HadamardBridge

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.IdealWeightPowers Hironaka.GermIdealOrder
  Hironaka.DerivativeIdeal Hironaka.HolomorphicTaylorTail
  Hironaka.OrderTaylor Hironaka.BlowupFlatCoordinates

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

section Consumers

open BlowupExceptionalDivisor BlowupControlledTransform MarkedIdeals

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C : Set X} {π : Y → X} {𝔞 : GermIdeal n X} {μ : ℕ}

/-- **The controlled transform along a centre in the cosupport is coherent.** -/
theorem isCoherent_controlledTransform_of_subset_cosupport (hπ : IsBlowupAlong n C π)
    (h𝔞 : 𝔞.IsCoherent) (hsub : C ⊆ cosupport n univ 𝔞 μ) :
    (controlledTransform hπ 𝔞 μ).IsCoherent :=
  isCoherent_controlledTransform hπ h𝔞
    (le_idealPow_vanishingIdeal_of_subset_cosupport h𝔞 hπ.1 hsub)

end Consumers

end

end Hironaka.HadamardBridge
