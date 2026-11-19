import Hironaka.Resolution.HironakaG8SuccExponents

set_option autoImplicit false

/-!
# Geometric criterion for exceptional-term divisibility

For a positive exponent, the order-one cosupport of the exceptional term is
exactly the carrier intersected with every listed closed member. Thus its
near-divisibility along any set is exactly the local geometric containment
of that set's carrier trace in all listed members. This criterion is valid at
any stage, independently of how the lists and carrier arose.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG11ExceptionalDivisibilityGeometry

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers GermIdealOrder DivisorExponentAlong HironakaG8SuccExponents
  HironakaG11InvBMLower

noncomputable section

variable {n : ℕ} {Y : CMfd.{0} n}

/-- Order-one divisibility of the positive exceptional term along `D` is
exactly local containment of `N ∩ D` in each listed closed member. -/
theorem isDivNearAlong_exceptionalTerm_one_iff
    {N D : Set Y} {S : List (Set Y)} (hS : ∀ H ∈ S, IsClosed H)
    {e : ℕ} (he : 1 ≤ e) (x : Y) :
    IsDivNearAlong n N (exceptionalTermBM (n := n) S e) D 1 x ↔
      ∀ᶠ y in 𝓝 x, y ∈ N → y ∈ D → ∀ H ∈ S, y ∈ H := by
  constructor
  · intro h
    filter_upwards [h] with y hy hyN hyD
    exact mem_of_mem_cosupport_one_exceptionalTermBM (Y := Y) hS (hy hyN hyD)
  · intro h
    filter_upwards [h] with y hy hyN hyD
    exact cosupport_anti he (mem_cosupport_exceptionalTermBM hyN (hy hyN hyD))

end

end Hironaka.HironakaG11ExceptionalDivisibilityGeometry
