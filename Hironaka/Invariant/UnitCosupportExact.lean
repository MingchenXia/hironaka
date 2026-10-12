/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.GermIdealOrder

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.GermIdealOrder
open Hironaka Hironaka.HolomorphicIdealSheaves IdealWeightPowers
noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] {N : Set M}
theorem cosupport_unitIdeal {d : ℕ} (hd : 1 ≤ d) : cosupport n N (unitIdeal n M) d = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx => ?_
  have h1 := (hx.2 (fun _ => (1 : ℂ)) (holomorphicAt_const 1)).mono hd
  have := (vanishesToOrderOn_one_iff hx.1 (holomorphicAt_const (n := n) (M := M) (x := x) 1)).mp h1
  exact one_ne_zero this

end
end Hironaka.GermIdealOrder
