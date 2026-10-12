/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.MarkedIdeals.MarkedIdeal
open Hironaka Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupStrictSubmanifold
noncomputable section
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M'] {C : Set M} {π : M' → M}
theorem geoStrictTransform_eq_empty_of_subset {A : Set M} (hA : A ⊆ C) :
    geoStrictTransform π C A = ∅ := by
  rw [geoStrictTransform, sdiff_eq_empty.mpr hA, preimage_empty, closure_empty]

end
end Hironaka.MarkedIdeals.MarkedIdeal
