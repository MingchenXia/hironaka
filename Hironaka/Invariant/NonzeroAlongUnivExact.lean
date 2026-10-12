/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.AmbientDivisorExponent
import Hironaka.Invariant.DivisorExponentAlong

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.DivisorExponentAlong
open Hironaka Hironaka.HolomorphicIdealSheaves DivisorExponent
noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {𝔞 : GermIdeal n M}
theorem isNonzeroAlongAt_univ_iff {x : M} : IsNonzeroAlongAt univ 𝔞 x ↔ IsNonzeroAt 𝔞 x := by
  simp [IsNonzeroAlongAt, IsNonzeroAt]


end
end Hironaka.DivisorExponentAlong
