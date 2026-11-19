import Hironaka.Analytic.Unibranch.HironakaG10VanishingStalkLocality
import Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener

/-! # Scheme boundary coincidence at a common flattener point -/

set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10BoundaryGermCoincidence

open Hironaka HironakaIntrinsicReducedCentreOpenPullback
open Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10VanishingStalkLocality

/-- Near a common support point, two local flatteners have the same
  supports, and the same possibly nonreduced boundary ideals for any set S. -/
theorem eventually_scheme_boundary_eq {X Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (Z Z' : LocalFlattener f) (S : Set X.obj.left)
    {x : X.obj.left} (hx : x ∈ Z.support) (hx' : x ∈ Z'.support) :
    ∀ᶠ y in 𝓝 x,
      intrinsicCentreStalkRange X.obj.left (closure ((S ∩ Z.V) \ Z.support)) y ⊔ Z.H y =
        intrinsicCentreStalkRange X.obj.left (closure ((S ∩ Z'.V) \ Z'.support)) y ⊔ Z'.H y := by
  have hH := Z.eventually_eq Z' hx hx'
  have hV := Z.isOpen.mem_nhds hx.1
  have hV' := Z'.isOpen.mem_nhds hx'.1
  have hsupport : ∀ᶠ y in 𝓝 x, y ∈ Z.support ↔ y ∈ Z'.support := by
    filter_upwards [hH,hV,hV'] with y hy hyV hyV'
    change (y ∈ Z.V ∧ Z.H y ≠ ⊤) ↔ (y ∈ Z'.V ∧ Z'.H y ≠ ⊤)
    simp only [hyV,hyV',true_and,hy]
  have hsets : ∀ᶠ y in 𝓝 x,
      y ∈ ((S ∩ Z.V) \ Z.support) ↔ y ∈ ((S ∩ Z'.V) \ Z'.support) := by
    filter_upwards [hsupport,hV,hV'] with y hy hyV hyV'
    simp only [Set.mem_sdiff, Set.mem_inter_iff, hyV, hyV', and_true, hy]
  have hclos : ∀ᶠ y in 𝓝 x,
      y ∈ closure ((S ∩ Z.V) \ Z.support) ↔ y ∈ closure ((S ∩ Z'.V) \ Z'.support) := by
    filter_upwards [hsets.eventually_nhds] with y hy
    rw [mem_closure_iff_frequently, mem_closure_iff_frequently]
    exact frequently_congr hy
  filter_upwards [hclos.eventually_nhds,hH] with y hy hyH
  rw [intrinsicCentreStalkRange_eq_of_eventually _ _ y hy,hyH]

end Hironaka.Analytic.Unibranch.HironakaG10BoundaryGermCoincidence
