/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.HolomorphicGermRing

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology
namespace Hironaka.HolGerm
noncomputable section
open Hironaka
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem mem_maximalIdeal_iff (g : HolGerm E) :
    g ∈ IsLocalRing.maximalIdeal (HolGerm E) ↔ eval g = 0 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_eval_ne_zero, not_not]

end
end Hironaka.HolGerm
