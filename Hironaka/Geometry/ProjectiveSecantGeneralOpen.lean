import Hironaka.Geometry.ProjectiveSecantGeneralEquation
import Hironaka.Geometry.ProjectiveSecantOpen
import Hironaka.Geometry.ProjectiveProjectionPointFinite

/-!
# A nonempty secant-centre open for the whole original source without integrality
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveProjection
open Algebra.ProjectiveProjectionFinite

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)

variable {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
  (hdim : topologicalKrullDim X < n)

/-- The actual parameter open comes from the original geometric dimension, rather than a caller's general-position certificate. -/
def generalSecantCenterOpen : (projectiveSpace k (n + 1)).Opens :=
  Proj.basicOpen (ProjectiveGrading k (n + 1))
    (MvPolynomial.rename Fin.succ (generalSecantEquation k n i hdim).val.2)

/-- Genuine native scheme nonemptiness is witnessed by the original ambient generic point. -/
theorem generalSecantCenterOpen_nonempty : (generalSecantCenterOpen k n i hdim : Set (projectiveSpace k (n + 1))).Nonempty := by
  refine ⟨ambientGenericPoint k n, ?_⟩
  change MvPolynomial.rename Fin.succ (generalSecantEquation k n i hdim).val.2 ≠ 0
  exact (MvPolynomial.rename_eq_zero_iff_of_injective _ (Fin.succ_injective (n + 1))).not.mpr
    (generalSecantEquation k n i hdim).property.2.2.1

/-- Every actual centre in the internally constructed open is outside the original closed image. -/
theorem generalSecantCenterOpen_avoids_image (c : projectiveSpace k (n + 1))
    (hc : c ∈ generalSecantCenterOpen k n i hdim) : c ∉ Set.range i := by
  intro hi
  rw [← zeroLocus_representativeIdeal_eq_range k n i] at hi
  change MvPolynomial.rename Fin.succ (generalSecantEquation k n i hdim).val.2 ∉ c.asHomogeneousIdeal at hc
  exact hc (hi (generalSecantEquation k n i hdim).property.2.2.2)

/-- The original rational centre in this actual parameter open gives a finite map on the original source. -/
def projectionFromGeneralSecantOpen
    (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
    (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hc : ProjectiveRationalPointCoordinates.pointImage k n p ∈ generalSecantCenterOpen k n i hdim) :
    X ⟶ projectiveSpace k n :=
  ProjectiveProjectionPoint.projectionFromPoint k n p hp i
    (generalSecantCenterOpen_avoids_image k n i hdim _ hc)

/-- Finiteness for the literal original projection is retained on the actual internally produced parameter open. -/
theorem projectionFromGeneralSecantOpen_isFinite
    (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
    (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hc : ProjectiveRationalPointCoordinates.pointImage k n p ∈ generalSecantCenterOpen k n i hdim) :
    IsFinite (projectionFromGeneralSecantOpen k n i hdim p hp hc) :=
  ProjectiveProjectionPoint.projectionFromPoint_isFinite k n p hp i
    (generalSecantCenterOpen_avoids_image k n i hdim _ hc)

/-- The actual parameter-open projection preserves the original coefficient triangle. -/
@[reassoc]
theorem projectionFromGeneralSecantOpen_structure
    (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
    (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hc : ProjectiveRationalPointCoordinates.pointImage k n p ∈ generalSecantCenterOpen k n i hdim) :
    projectionFromGeneralSecantOpen k n i hdim p hp hc ≫ projectiveSpaceStructure k n =
      i ≫ projectiveSpaceStructure k (n + 1) :=
  ProjectiveProjectionPoint.projectionFromPoint_structure k n p hp i
    (generalSecantCenterOpen_avoids_image k n i hdim _ hc)

end Hironaka.Geometry.ProjectiveSecant
