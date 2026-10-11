/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.GermIdealOrder
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Hironaka.GermIdealOrder
open Hironaka HolomorphicIdealSheaves IdealWeightPowers
noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
/-- `𝔪_x^{q+1} ⊆ 𝔪_x^q`. -/
theorem idealPow_pointIdeal_succ_le (x : M) (q : ℕ) :
    (idealPow (pointIdeal n x) (q + 1)).Le (idealPow (pointIdeal n x) q) :=
  idealPow_succ_le (fun _ _ hg => holomorphicAt_of_mem_pointIdeal hg) q


end
end Hironaka.GermIdealOrder
