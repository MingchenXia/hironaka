/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.ResolutionInvariantOrder

set_option autoImplicit false
namespace Hironaka.ResolutionInvariantOrder
open Hironaka
noncomputable section
open Set Filter
open scoped Topology
variable {X Y Λ : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {f : X → Λ} {s t : Set X}

/-- **Superlevel sets are closed** (for a closed domain). -/
theorem IsInvUSCOn.isClosed_superlevel [LinearOrder Λ] (hf : IsInvUSCOn f s) (hs : IsClosed s) (l : Λ) :
    IsClosed {x | x ∈ s ∧ l ≤ f x} := by
  refine isOpen_compl_iff.mp (isOpen_iff_mem_nhds.mpr fun y hy => ?_)
  by_cases hys : y ∈ s
  · have hlt : f y < l := lt_of_not_ge fun h => hy ⟨hys, h⟩
    filter_upwards [hf y hys] with z hz hzmem
    exact absurd ((hz hzmem.1).trans_lt hlt) (not_lt.mpr hzmem.2)
  · filter_upwards [hs.isOpen_compl.mem_nhds hys] with z hz hzmem
    exact hz hzmem.1


end
end Hironaka.ResolutionInvariantOrder
