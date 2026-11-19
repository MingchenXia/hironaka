import Hironaka.Geometry.ProjectiveProjectionCenterCoordinates
import Hironaka.Geometry.ProjStructureMap
import Hironaka.Geometry.ProjectiveModification

/-!
# Actual projective coordinate automorphism at an original rational centre
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

/-- The actual native projective-space automorphism constructed from the original vector. -/
def coordinateAutomorphism (v : Fin (n + 2) → k) (hv : v ≠ 0) :
    projectiveSpace k (n + 1) ≅ projectiveSpace k (n + 1) where
  hom := Proj.map (coordinateGradedMap k n v hv) (coordinateGradedMap_irrelevant_le k n v hv)
  inv := Proj.map (inverseCoordinateGradedMap k n v hv) (inverseCoordinateGradedMap_irrelevant_le k n v hv)
  hom_inv_id := by
    rw [← Proj.map_comp]
    change Proj.map ((coordinateGradedMap k n v hv).comp (inverseCoordinateGradedMap k n v hv)) _ =
      𝟙 (Proj (ProjectiveGrading k (n + 1)))
    simpa only [coordinateGradedMap_comp_inverse] using
      (Proj.map_id (𝒜 := ProjectiveGrading k (n + 1)))
  inv_hom_id := by
    rw [← Proj.map_comp]
    change Proj.map ((inverseCoordinateGradedMap k n v hv).comp (coordinateGradedMap k n v hv)) _ =
      𝟙 (Proj (ProjectiveGrading k (n + 1)))
    simpa only [inverseCoordinateGradedMap_comp_coordinate] using
      (Proj.map_id (𝒜 := ProjectiveGrading k (n + 1)))

/-- The constructed native projective automorphism takes the original vector point to the actual standard centre. -/
theorem coordinateAutomorphism_apply_vectorPoint (v : Fin (n + 2) → k) (hv : v ≠ 0) :
    (coordinateAutomorphism k n v hv).hom (vectorPoint k n v hv) = centrePoint k n := by
  apply ProjectiveSpectrum.ext
  apply SetLike.ext
  intro F
  change vectorGradedMap k n v (coordinateGradedMap k n v hv F) = 0 ↔ centreGradedMap k n F = 0
  have h := DFunLike.congr_fun (vectorGradedMap_comp_coordinates k n v hv) F
  change vectorGradedMap k n v (coordinateGradedMap k n v hv F) = centreGradedMap k n F at h
  rw [h]

/-- The constructed scheme automorphism preserves the literal original coefficient structure. -/
@[reassoc]
theorem coordinateAutomorphism_structure (v : Fin (n + 2) → k) (hv : v ≠ 0) :
    (coordinateAutomorphism k n v hv).hom ≫ projectiveSpaceStructure k (n + 1) =
      projectiveSpaceStructure k (n + 1) := by
  apply ProjStructureMap.map_toSpec_base
  apply RingHom.ext
  intro a
  apply Subtype.ext
  change coordinatePolynomialEquiv k n v hv (C a) = C a
  exact (coordinatePolynomialEquiv k n v hv).commutes a

/-- Every original homogeneous basic-open pullback is the actual linear coordinate substitution. -/
@[simp]
theorem coordinateAutomorphism_preimage_basicOpen (v : Fin (n + 2) → k) (hv : v ≠ 0)
    (F : MvPolynomial (Fin (n + 2)) k) :
    (coordinateAutomorphism k n v hv).hom ⁻¹ᵁ Proj.basicOpen (ProjectiveGrading k (n + 1)) F =
      Proj.basicOpen (ProjectiveGrading k (n + 1)) (coordinatePolynomialEquiv k n v hv F) :=
  Proj.map_preimage_basicOpen _ _ F

end Hironaka.Geometry.ProjectiveProjectionCenter
