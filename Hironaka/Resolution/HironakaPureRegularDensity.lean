/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaEmbeddedReducible

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaEmbeddedReducible
open Hironaka
noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **An irreducible subvariety of dimension `< n` is of pure dimension** (so the theorems above contain the irreducible case;
`PureDimension.eq_dim_of_regularAtDim` is not needed: the closure of the regular locus of the component through a regular
point of dimension `dim V` is `V`). -/
theorem subset_closure_regularLocus (V : ClosedIrreducibleAnalyticSubvariety n M) :
    V.carrier ⊆ closure (regularLocus (n := n) V.carrier V.dim) := by
  refine (HironakaEmbeddedResolutionLocal.subset_closure_inter_regularOpen V).trans (closure_mono fun x hx => ?_)
  exact EmbeddedFromResolution.regularAtDim_of_mem_regularOpen hx.1 hx.2


end
end Hironaka.HironakaEmbeddedReducible
