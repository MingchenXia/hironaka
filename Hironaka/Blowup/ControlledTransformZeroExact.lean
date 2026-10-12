/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupControlledTransform
import Hironaka.Blowup.ControlledTransformUniqueness

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.BlowupControlledTransform
open Hironaka Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealTotalTransform GermIdealPullbackCalculus IdealWeightPowers InvertibleIdealQuotient RelativePrincipalizationSpan BlowupExceptionalDivisor
noncomputable section
section Cancel
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

theorem colon_unitIdeal {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) :
    colon 𝔞 (unitIdeal n M) = 𝔞 := by
  have h := colon_mul_eq (isInvertible_unitIdeal (n := n) (M := M)) h𝔞
  rwa [RestrictLeCalculus.mul_comm', RestrictLeCalculus.mul_unitIdeal h𝔞] at h

end Cancel
section Controlled
variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

theorem controlledTransform_zero (hπ : IsBlowupAlong n C π) {𝔞 : GermIdeal n X}
    (h𝔞 : 𝔞.IsCoherent) :
    controlledTransform hπ 𝔞 0 = GermIdeal.pullback (m := n) π 𝔞 := by
  rw [controlledTransform, idealPow_zero, colon_unitIdeal (isCoherent_pullback hπ.contMDiff h𝔞)]


end Controlled
end
end Hironaka.BlowupControlledTransform
