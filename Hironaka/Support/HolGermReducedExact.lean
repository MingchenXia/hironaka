/- Exact complete original reducedness theorem and instance; no domain assumption. -/
import Hironaka.Analytic.HolomorphicGermRing
set_option autoImplicit false
open Filter Topology
namespace Hironaka.HolGerm
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Holomorphic germs have no nonzero nilpotents.  This only uses the
pointwise fact that a complex number whose power vanishes is zero; it does
not use an identity theorem or the stronger domain property for holomorphic
germs. -/
theorem isReduced : IsReduced (HolGerm E) := by
  constructor
  intro g hg
  obtain ⟨n, hn⟩ := hg
  induction g using induction_on with
  | h f hf =>
    rw [← mk_zero]
    apply mk_eq_mk_iff.mpr
    have hn' : mk (fun z : E => f z ^ n) (eventually_differentiableAt_pow hf n) =
        mk (fun _ : E => 0) eventually_differentiableAt_zero := by
      calc
        mk (fun z : E => f z ^ n) (eventually_differentiableAt_pow hf n) =
            mk f hf ^ n := mk_pow f hf n
        _ = 0 := hn
        _ = mk (fun _ : E => 0) eventually_differentiableAt_zero := mk_zero.symm
    have hfn : ∀ᶠ z in 𝓝 (0 : E), f z ^ n = 0 := mk_eq_mk_iff.mp hn'
    filter_upwards [hfn] with z hz
    exact eq_zero_of_pow_eq_zero hz

/-- The preceding pointwise theorem supplies the standard reduced-ring
instance for holomorphic germs. -/
instance : IsReduced (HolGerm E) := isReduced

end
end Hironaka.HolGerm
