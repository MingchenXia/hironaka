/- Complete original prerequisite; statement and mathematical proof unchanged. -/
import Hironaka.Support.HolGermSubExact

set_option autoImplicit false
namespace Hironaka
open Filter Topology
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace HolGerm
variable {E}
theorem mk_sub' (f g : E → ℂ) (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z)
    (hg : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ g z) :
    mk (f - g) (eventually_differentiableAt_sub hf hg) = mk f hf - mk g hg :=
  rfl

theorem constHom_apply (c : ℂ) :
    constHom c = mk (fun _ : E => c) (eventually_differentiableAt_const c) :=
  rfl
end HolGerm
end Hironaka
