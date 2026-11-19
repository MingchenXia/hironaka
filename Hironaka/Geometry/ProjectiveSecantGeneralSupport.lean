import Hironaka.Geometry.ProjectiveSecantGeneralIntersection
import Hironaka.Geometry.ProjectiveSecantSupport

/-!
# Whole original source intersection support for the actual native secant line
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveProjectionCenter
open Algebra.ProjectiveSecant Algebra.ProjectiveProjectionFinite

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)

variable {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1))
  [IsClosedImmersion i] (hdim : topologicalKrullDim X < n)

/-- Every actual original line/source intersection point on the native line is the original standard endpoint. -/
theorem generalSecantLine_intersection_eq_standard (v : Fin (n + 2) → k) (hv : v ≠ 0)
    (hc : vectorPoint k n v hv ∈ generalSecantCenterOpen k n i hdim)
    (y : projectiveSpace k 1) (hy : generalSecantLine k n i hdim v hv hc y ∈ Set.range i) :
    y = centrePoint k 0 :=
  linePoint_eq_standard_of_outside_chart k y
    (generalSecantLine_intersection_outside_chart k n i hdim v hv hc y hy)

/-- The actual original pullback's literal second projection is supported at the specified original line endpoint. -/
theorem generalSecantLine_pullback_snd_eq_standard (v : Fin (n + 2) → k) (hv : v ≠ 0)
    (hc : vectorPoint k n v hv ∈ generalSecantCenterOpen k n i hdim)
    (z : (Limits.pullback i (generalSecantLine k n i hdim v hv hc) : Scheme)) :
    Limits.pullback.snd i (generalSecantLine k n i hdim v hv hc) z = centrePoint k 0 :=
  linePoint_eq_standard_of_outside_chart k _ (generalSecantLine_pullback_support k n i hdim v hv hc z)

/-- If the specified original point lies on the source, its actual original line intersects that source only at this point. -/
theorem generalSecantLine_range_inter_range (v : Fin (n + 2) → k) (hv : v ≠ 0)
    (hc : vectorPoint k n v hv ∈ generalSecantCenterOpen k n i hdim)
    (hq : centrePoint k n ∈ Set.range i) :
    Set.range (generalSecantLine k n i hdim v hv hc) ∩ Set.range i = {centrePoint k n} := by
  ext z
  constructor
  · rintro ⟨⟨y, rfl⟩, hy⟩
    rw [generalSecantLine_intersection_eq_standard k n i hdim v hv hc y hy,
      generalSecantLine_apply_standard]
    exact Set.mem_singleton _
  · intro hz
    have hz' : z = centrePoint k n := Set.mem_singleton_iff.mp hz
    subst z
    exact ⟨⟨centrePoint k 0, generalSecantLine_apply_standard k n i hdim v hv hc⟩, hq⟩

end Hironaka.Geometry.ProjectiveSecant
