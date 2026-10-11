/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.GermIdealOrder

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.GermIdealOrder
open Hironaka HolomorphicIdealSheaves
noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

variable (n) in
/-- **The order `ord_x(𝔞|_N) ∈ ℕ∞`**: the supremum of the `q` with `𝔞_x|_N ⊆ 𝔪_{N,x}^q`
(`⊤` when `𝔞|_N` vanishes near `x`, e.g. for the zero ideal). -/
def order (N : Set M) (𝔞 : GermIdeal n M) (x : M) : ℕ∞ :=
  ⨆ (q : ℕ) (_ : OrderGE n N 𝔞 x q), (q : ℕ∞)


end
end Hironaka.GermIdealOrder
