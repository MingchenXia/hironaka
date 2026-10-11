/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.HolomorphicGermRing

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Filter
open scoped Topology
namespace Hironaka
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem eventually_differentiableAt_sub {f g : E → ℂ}
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) (hg : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ g z) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun z => f z - g z) z :=
  hf.and hg |>.mono fun _ h => h.1.sub h.2

end Hironaka
