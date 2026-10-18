/- Complete original prerequisites; statements and mathematical proofs are unchanged. -/
import Hironaka.Analytic.HolomorphicGermRing

set_option autoImplicit false


namespace Hironaka


open Filter Topology


section Differentiability


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]


theorem eventually_differentiableAt_sub {f g : E → ℂ}
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) (hg : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ g z) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun z => f z - g z) z :=
  hf.and hg |>.mono fun _ h => h.1.sub h.2

end Differentiability


variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]


namespace HolGerm


variable {E}


theorem mk_sub (f g : E → ℂ) (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z)
    (hg : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ g z) :
    mk (fun z => f z - g z) (eventually_differentiableAt_sub hf hg) = mk f hf - mk g hg :=
  rfl

end HolGerm


end Hironaka
