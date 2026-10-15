/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Blowup.BlowupControlledTransform
import Hironaka.Blowup.ControlledTransformUniqueness

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupControlledTransform

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  GermIdealTotalTransform GermIdealPullbackCalculus IdealWeightPowers InvertibleIdealQuotient
  RelativePrincipalizationSpan BlowupExceptionalDivisor

noncomputable section

/-! ### Cancellation of an invertible ideal -/

section Cancel

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The colon ideal by the unit ideal is the ideal itself, for a coherent ideal. -/
theorem colon_unitIdeal {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) :
    colon 𝔞 (unitIdeal n M) = 𝔞 := by
  have h := colon_mul_eq (isInvertible_unitIdeal (n := n) (M := M)) h𝔞
  rwa [RestrictLeCalculus.mul_comm', RestrictLeCalculus.mul_unitIdeal h𝔞] at h

end Cancel
end
end Hironaka.BlowupControlledTransform
