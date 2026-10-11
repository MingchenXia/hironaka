/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.RegularComponentClosureGeometry
import Hironaka.Analytic.AnalyticIrreducibleComponents

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.IrreducibleComponentFilling
open Hironaka
noncomputable section
open RegularLocusComponent
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The closure of the connected component of the regular locus of `A` through a regular
point `c`, as a closed irreducible analytic subvariety of dimension the dimension of `A`
at `c`. -/
def componentSubvariety {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A) {c : M} {k : ℕ}
    (hc : RegularAtDim (n := n) A c k) : ClosedIrreducibleAnalyticSubvariety n M where
  carrier := closure (component (n := n) A c)
  isClosed_carrier := isClosed_closure
  irreducible_carrier := isComplexAnalyticallyIrreducible_closure_component hA hc
  dim := k
  dim_le := hc.1
  regularLocus_nonempty := ⟨c, regularAtDim_closure_component hc (mem_component_self hc)⟩

@[simp] theorem componentSubvariety_carrier {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) {c : M} {k : ℕ}
    (hc : RegularAtDim (n := n) A c k) :
    (componentSubvariety hA hc).carrier = closure (component (n := n) A c) :=
  rfl

theorem componentSubvariety_subset {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A)
    {c : M} {k : ℕ} (hc : RegularAtDim (n := n) A c k) :
    (componentSubvariety hA hc).carrier ⊆ A :=
  closure_minimal (component_subset (n := n) A c) hA.isClosed


end
end Hironaka.IrreducibleComponentFilling
