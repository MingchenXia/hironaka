import Hironaka.Analytic.UscRegularizationContinuous

set_option autoImplicit false

/-!
# Germ locality of upper-semicontinuous regularization

Upper-semicontinuous regularization depends only on the germ of the function
at its evaluation point.  This standalone form is useful when a local PSH
function is extended by `-∞` outside its domain before taking a regularization.
-/

open Filter
open scoped Topology

namespace Hironaka

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- Upper-semicontinuous regularization is unchanged when its input functions
agree eventually at the evaluation point. -/
theorem uscRegularization_congr_of_eventuallyEq {f g : X → EReal} {x : X}
    (hfg : f =ᶠ[𝓝 x] g) : uscRegularization f x = uscRegularization g x :=
  le_antisymm
    (uscRegularization_le_of_eventually_le (upperSemicontinuous_uscRegularization g x)
      (hfg.mono fun y hy => hy ▸ le_uscRegularization g y))
    (uscRegularization_le_of_eventually_le (upperSemicontinuous_uscRegularization f x)
      (hfg.mono fun y hy => hy ▸ le_uscRegularization f y))

end

end Hironaka
