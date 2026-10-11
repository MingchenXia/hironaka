/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.ThinDimensionDrop

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold
namespace Hironaka.ThinDimensionDrop
noncomputable section
open Hironaka AnalyticDimensionBasics
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Thin analytic subsets have smaller dimension**, as a dimension bound: `dim T' ≤ a - 1`. -/
theorem dimLE_pred_of_thin {T T' : Set M} (hT : IsComplexAnalyticSubset (n := n) T)
    (hT'T : T' ⊆ T) (hthin : ∀ O : Set M, IsOpen O → O ∩ T ⊆ T' → O ∩ T = ∅) {a : ℕ}
    (hdim : DimLE (n := n) T a) : DimLE (n := n) T' (a - 1) := fun y k hy => by
  have := lt_of_regularAtDim_of_thin hT hT'T hthin hdim hy
  omega

end
end Hironaka.ThinDimensionDrop
