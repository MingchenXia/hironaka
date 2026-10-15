/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Analytic.HolomorphicGermRing

set_option autoImplicit false

namespace Hironaka

open Filter Topology

noncomputable section

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace HolGerm

variable {E}

theorem mk_mul' (f g : E → ℂ) (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z)
    (hg : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ g z) :
    mk (f * g) (eventually_differentiableAt_mul hf hg) = mk f hf * mk g hg :=
  rfl

end HolGerm
end
end Hironaka
