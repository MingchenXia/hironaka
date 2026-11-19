import Hironaka.Geometry.ProjectiveProjectionCenterAutomorphism
import Hironaka.Geometry.ProjectiveProjectionClosedSubscheme

/-!
# Genuine finite projection from an original arbitrary nonzero rational centre

The homogeneous coordinate automorphism is constructed internally from
the original vector. The finite projection has the literal original
closed subscheme as source and preserves its coefficient structure.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveProjectionCenter

open ProjectiveIdeal Algebra.ProjectiveLinearCoordinates
open Algebra.ProjectiveProjectionFinite

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)
  {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
  (v : Fin (n + 2) → k) (hv : v ≠ 0)

/-- The actual original closed immersion in the internally constructed new coordinates. -/
def transformedInclusion : X ⟶ projectiveSpace k (n + 1) :=
  i ≫ (coordinateAutomorphism k n v hv).hom

instance transformedInclusion_isClosedImmersion : IsClosedImmersion (transformedInclusion k n i v hv) := by
  dsimp only [transformedInclusion]
  infer_instance

omit [IsClosedImmersion i] in
/-- Original outside-ness implies actual standard-centre outside-ness in the constructed coordinates. -/
theorem transformedInclusion_centre_outside (hout : vectorPoint k n v hv ∉ Set.range i) :
    centrePoint k n ∉ Set.range (transformedInclusion k n i v hv) := by
  rintro ⟨x, hx⟩
  apply hout
  refine ⟨x, ?_⟩
  change (coordinateAutomorphism k n v hv).hom (i x) = centrePoint k n at hx
  have heq : (coordinateAutomorphism k n v hv).hom (i x) =
      (coordinateAutomorphism k n v hv).hom (vectorPoint k n v hv) :=
    hx.trans (coordinateAutomorphism_apply_vectorPoint k n v hv).symm
  have hinv := congrArg (fun z => (coordinateAutomorphism k n v hv).inv z) heq
  change ((coordinateAutomorphism k n v hv).hom ≫ (coordinateAutomorphism k n v hv).inv) (i x) =
    ((coordinateAutomorphism k n v hv).hom ≫ (coordinateAutomorphism k n v hv).inv) (vectorPoint k n v hv) at hinv
  rw [Iso.hom_inv_id] at hinv
  change i x = vectorPoint k n v hv at hinv
  exact hinv

/-- The genuine projection from the original source, with no supplied coordinate-change or finite-map certificate. -/
def projectionFromVector (hout : vectorPoint k n v hv ∉ Set.range i) : X ⟶ projectiveSpace k n :=
  ProjectiveProjection.closedProjection k n (transformedInclusion k n i v hv)
    (transformedInclusion_centre_outside k n i v hv hout)

/-- The actual projection from the arbitrary original rational vector centre is finite. -/
theorem projectionFromVector_isFinite (hout : vectorPoint k n v hv ∉ Set.range i) :
    IsFinite (projectionFromVector k n i v hv hout) :=
  ProjectiveProjection.closedProjection_isFinite k n (transformedInclusion k n i v hv)
    (transformedInclusion_centre_outside k n i v hv hout)

/-- The original coefficient triangle survives the internally chosen coordinate change. -/
@[reassoc]
theorem projectionFromVector_structure (hout : vectorPoint k n v hv ∉ Set.range i) :
    projectionFromVector k n i v hv hout ≫ projectiveSpaceStructure k n =
      i ≫ projectiveSpaceStructure k (n + 1) := by
  rw [projectionFromVector, ProjectiveProjection.closedProjection_structure,
    transformedInclusion, Category.assoc, coordinateAutomorphism_structure]

/-- Literal original linear coordinate forms give all actual coordinate-open preimages. -/
@[simp]
theorem projectionFromVector_preimage_coordinate (hout : vectorPoint k n v hv ∉ Set.range i)
    (j : Fin (n + 1)) :
    projectionFromVector k n i v hv hout ⁻¹ᵁ Proj.basicOpen (ProjectiveGrading k n) (MvPolynomial.X j) =
      i ⁻¹ᵁ Proj.basicOpen (ProjectiveGrading k (n + 1))
        (coordinatePolynomialEquiv k n v hv (MvPolynomial.X j.succ)) := by
  rw [projectionFromVector, ProjectiveProjection.closedProjection_preimage_coordinate,
    transformedInclusion, Scheme.Hom.comp_preimage, coordinateAutomorphism_preimage_basicOpen]

/-- The original source remains projective over its original coefficient field. -/
theorem projectionFromVector_source_isProjectiveOver (hout : vectorPoint k n v hv ∉ Set.range i) :
    IsProjectiveOver (projectionFromVector k n i v hv hout ≫ projectiveSpaceStructure k n) :=
  ⟨n + 1, i, inferInstance, (projectionFromVector_structure k n i v hv hout).symm⟩

/-- Source 2.11 finite projection from the actual original rational vector centre. -/
theorem exists_finite_projection_from_vector (hout : vectorPoint k n v hv ∉ Set.range i) :
    ∃ f : X ⟶ projectiveSpace k n, IsFinite f ∧
      f ≫ projectiveSpaceStructure k n = i ≫ projectiveSpaceStructure k (n + 1) ∧
      ∀ j : Fin (n + 1),
        f ⁻¹ᵁ Proj.basicOpen (ProjectiveGrading k n) (MvPolynomial.X j) =
          i ⁻¹ᵁ Proj.basicOpen (ProjectiveGrading k (n + 1))
            (coordinatePolynomialEquiv k n v hv (MvPolynomial.X j.succ)) :=
  ⟨projectionFromVector k n i v hv hout, projectionFromVector_isFinite k n i v hv hout,
    projectionFromVector_structure k n i v hv hout, projectionFromVector_preimage_coordinate k n i v hv hout⟩

end Hironaka.Geometry.ProjectiveProjectionCenter
