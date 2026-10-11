/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.GeometricPureDimension
import Hironaka.Analytic.AnalyticDimensionBasics

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold
namespace Hironaka.AnalyticDimensionBasics
noncomputable section
open Hironaka
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

omit [IsComplexManifold n M] in
theorem IsPureDim.dimLE {A : Set M} {k : ℕ} (h : IsPureDim (n := n) A k) : DimLE (n := n) A k :=
  fun y j hy => (h y j hy).le

end
end Hironaka.AnalyticDimensionBasics
