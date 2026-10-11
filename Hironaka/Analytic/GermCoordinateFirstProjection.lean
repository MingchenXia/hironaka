/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.GermCoordinateTower

set_option autoImplicit false
namespace Hironaka.HolGerm
open Hironaka
noncomputable section
open Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem ofFst_mk (f : E → ℂ) (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) :
    ofFst (mk f hf) = mk (fun x : E × ℂ => f x.1)
      (eventually_differentiableAt_comp_clm (ContinuousLinearMap.fst ℂ E ℂ) hf) :=
  rfl


end
end Hironaka.HolGerm
