import Hironaka.Geometry.ProjectiveSecantGeneralOpen
import Hironaka.Geometry.ProjectiveSecantPointOpen

/-!
# An original rational fixed point produces a whole-source nonempty secant open
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveProjectionCenter ProjectiveRationalPointCoordinates

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)
  (q : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
  (hq : q ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
  {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
  (hdim : topologicalKrullDim X < n)

/-- The actual parameter open in the original ambient scheme is an actual inverse image of the internally computed open. -/
def generalFixedPointCenterOpen : (projectiveSpace k (n + 1)).Opens :=
  (fixedPointAutomorphism k n q hq).hom ⁻¹ᵁ generalSecantCenterOpen k n (fixedPointInclusion k n q hq i) hdim

/-- Nonemptiness uses an actual native point and the two actual scheme inverse identities. -/
theorem generalFixedPointCenterOpen_nonempty :
    (generalFixedPointCenterOpen k n q hq i hdim : Set (projectiveSpace k (n + 1))).Nonempty := by
  exact iso_preimage_open_nonempty (fixedPointAutomorphism k n q hq)
    (generalSecantCenterOpen k n (fixedPointInclusion k n q hq i) hdim)
    (generalSecantCenterOpen_nonempty k n (fixedPointInclusion k n q hq i) hdim)

/-- The actual centre open avoids the exact original closed image, before any coordinate transport. -/
theorem generalFixedPointCenterOpen_avoids_image (c : projectiveSpace k (n + 1))
    (hc : c ∈ generalFixedPointCenterOpen k n q hq i hdim) : c ∉ Set.range i := by
  rintro ⟨x, rfl⟩
  exact generalSecantCenterOpen_avoids_image k n (fixedPointInclusion k n q hq i) hdim _ hc ⟨x, rfl⟩

/-- Every actual original rational centre in this produced original open gives a genuine finite projection on the same original source. -/
def projectionFromGeneralFixedPointOpen (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
    (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hc : pointImage k n p ∈ generalFixedPointCenterOpen k n q hq i hdim) : X ⟶ projectiveSpace k n :=
  ProjectiveProjectionPoint.projectionFromPoint k n p hp i
    (generalFixedPointCenterOpen_avoids_image k n q hq i hdim _ hc)

/-- Finiteness is a genuine property of the actual original projection, with no supplied certificate. -/
theorem projectionFromGeneralFixedPointOpen_isFinite (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
    (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hc : pointImage k n p ∈ generalFixedPointCenterOpen k n q hq i hdim) :
    IsFinite (projectionFromGeneralFixedPointOpen k n q hq i hdim p hp hc) :=
  ProjectiveProjectionPoint.projectionFromPoint_isFinite _ _ _ _ _ _

/-- The original coefficient triangle for the original finite projection is retained literally. -/
@[reassoc]
theorem projectionFromGeneralFixedPointOpen_structure (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
    (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hc : pointImage k n p ∈ generalFixedPointCenterOpen k n q hq i hdim) :
    projectionFromGeneralFixedPointOpen k n q hq i hdim p hp hc ≫ projectiveSpaceStructure k n =
      i ≫ projectiveSpaceStructure k (n + 1) :=
  ProjectiveProjectionPoint.projectionFromPoint_structure _ _ _ _ _ _

end Hironaka.Geometry.ProjectiveSecant
