import Hironaka.Algebra.ProjectiveSecantLinePoint
import Hironaka.Geometry.ProjectiveSecantIntersection

/-!
# The actual original secant intersection has one specified endpoint as support
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

/-- The original native projective line's closed coordinate complement has exactly its original endpoint. -/
theorem linePoint_eq_standard_of_outside_chart (p : projectiveSpace k 1)
    (hp : p ∉ Proj.basicOpen (ProjectiveGrading k 1) (X (1 : Fin 2))) :
    p = centrePoint k 0 := by
  apply eq_centrePoint_of_remaining_mem k 0 p
  intro j
  have hj : j = 0 := Fin.ext (Nat.lt_one_iff.mp j.isLt)
  subst j
  exact not_not.mp hp

variable {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1))
  [IsClosedImmersion i] [IsIntegral X] (hdim : topologicalKrullDim X < n)

/-- Every actual original line/source intersection point on the native line is the original standard endpoint. -/
theorem secantLine_intersection_eq_standard (v : Fin (n + 2) → k) (hv : v ≠ 0)
    (hc : vectorPoint k n v hv ∈ secantCenterOpen k n i hdim)
    (y : projectiveSpace k 1) (hy : secantLine k n i hdim v hv hc y ∈ Set.range i) :
    y = centrePoint k 0 :=
  linePoint_eq_standard_of_outside_chart k y
    (secantLine_intersection_outside_chart k n i hdim v hv hc y hy)

/-- The actual original pullback's literal second projection is supported at the specified original line endpoint. -/
theorem secantLine_pullback_snd_eq_standard (v : Fin (n + 2) → k) (hv : v ≠ 0)
    (hc : vectorPoint k n v hv ∈ secantCenterOpen k n i hdim)
    (z : (Limits.pullback i (secantLine k n i hdim v hv hc) : Scheme)) :
    Limits.pullback.snd i (secantLine k n i hdim v hv hc) z = centrePoint k 0 :=
  linePoint_eq_standard_of_outside_chart k _ (secantLine_pullback_support k n i hdim v hv hc z)

/-- If the specified original point lies on the source, its actual original line intersects that source only at this point. -/
theorem secantLine_range_inter_range (v : Fin (n + 2) → k) (hv : v ≠ 0)
    (hc : vectorPoint k n v hv ∈ secantCenterOpen k n i hdim)
    (hq : centrePoint k n ∈ Set.range i) :
    Set.range (secantLine k n i hdim v hv hc) ∩ Set.range i = {centrePoint k n} := by
  ext z
  constructor
  · rintro ⟨⟨y, rfl⟩, hy⟩
    rw [secantLine_intersection_eq_standard k n i hdim v hv hc y hy,
      secantLine_apply_standard]
    exact Set.mem_singleton _
  · intro hz
    have hz' : z = centrePoint k n := Set.mem_singleton_iff.mp hz
    subst z
    exact ⟨⟨centrePoint k 0, secantLine_apply_standard k n i hdim v hv hc⟩, hq⟩

end Hironaka.Geometry.ProjectiveSecant
