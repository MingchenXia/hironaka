import Hironaka.Geometry.ProjectiveRationalPointCoordinatesEquations
import Hironaka.Geometry.ProjectiveProjectionCenterFinite

/-!
# Genuine finite projection from an original rational scheme morphism

The actual original morphism Spec(k) → projective space, its coefficient
triangle, the original closed immersion, and outside-ness are the inputs.
A homogeneous vector and the projective coordinate automorphism are produced
internally, and the finite projection retains the original source.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveProjectionPoint

open ProjectiveIdeal ProjectiveRationalPointCoordinates ProjectiveProjectionCenter
open Algebra.ProjectiveLinearCoordinates

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)
  (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
  (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
  {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]

omit [IsClosedImmersion i] in
/-- Original outside-ness is retained by the internally recovered vector, with no supplied representation. -/
theorem pointVector_outside (hout : pointImage k n p ∉ Set.range i) :
    vectorPoint k n (pointVector k n p hp) (pointVector_ne_zero k n p hp) ∉ Set.range i := by
  rwa [pointVector_image]

/-- The actual finite projection from the original source and original rational scheme centre. -/
def projectionFromPoint (hout : pointImage k n p ∉ Set.range i) : X ⟶ projectiveSpace k n :=
  projectionFromVector k n i (pointVector k n p hp) (pointVector_ne_zero k n p hp)
    (pointVector_outside k n p hp i hout)

/-- The original rational scheme point internally produces a genuine finite projection. -/
theorem projectionFromPoint_isFinite (hout : pointImage k n p ∉ Set.range i) :
    IsFinite (projectionFromPoint k n p hp i hout) :=
  projectionFromVector_isFinite k n i (pointVector k n p hp) (pointVector_ne_zero k n p hp)
    (pointVector_outside k n p hp i hout)

/-- The exact original coefficient structure triangle survives the actual rational-point construction. -/
@[reassoc]
theorem projectionFromPoint_structure (hout : pointImage k n p ∉ Set.range i) :
    projectionFromPoint k n p hp i hout ≫ projectiveSpaceStructure k n =
      i ≫ projectiveSpaceStructure k (n + 1) :=
  projectionFromVector_structure k n i (pointVector k n p hp) (pointVector_ne_zero k n p hp)
    (pointVector_outside k n p hp i hout)

/-- The original actual rational point determines literal original linear-coordinate preimages. -/
@[simp]
theorem projectionFromPoint_preimage_coordinate (hout : pointImage k n p ∉ Set.range i)
    (j : Fin (n + 1)) :
    projectionFromPoint k n p hp i hout ⁻¹ᵁ Proj.basicOpen (ProjectiveGrading k n) (MvPolynomial.X j) =
      i ⁻¹ᵁ Proj.basicOpen (ProjectiveGrading k (n + 1))
        (coordinatePolynomialEquiv k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)
          (MvPolynomial.X j.succ)) :=
  projectionFromVector_preimage_coordinate k n i (pointVector k n p hp) (pointVector_ne_zero k n p hp)
    (pointVector_outside k n p hp i hout) j

/-- Projectivity remains a property of the actual original source over its original field. -/
theorem projectionFromPoint_source_isProjectiveOver (hout : pointImage k n p ∉ Set.range i) :
    IsProjectiveOver (projectionFromPoint k n p hp i hout ≫ projectiveSpaceStructure k n) :=
  ⟨n + 1, i, inferInstance, (projectionFromPoint_structure k n p hp i hout).symm⟩

/-- Source 2.11 finite projection from the original rational scheme morphism, without any vector certificate. -/
theorem exists_finite_projection_from_point (hout : pointImage k n p ∉ Set.range i) :
    ∃ f : X ⟶ projectiveSpace k n, IsFinite f ∧
      f ≫ projectiveSpaceStructure k n = i ≫ projectiveSpaceStructure k (n + 1) ∧
      ∀ j : Fin (n + 1),
        f ⁻¹ᵁ Proj.basicOpen (ProjectiveGrading k n) (MvPolynomial.X j) =
          i ⁻¹ᵁ Proj.basicOpen (ProjectiveGrading k (n + 1))
            (coordinatePolynomialEquiv k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)
              (MvPolynomial.X j.succ)) :=
  ⟨projectionFromPoint k n p hp i hout, projectionFromPoint_isFinite k n p hp i hout,
    projectionFromPoint_structure k n p hp i hout, projectionFromPoint_preimage_coordinate k n p hp i hout⟩

end Hironaka.Geometry.ProjectiveProjectionPoint
