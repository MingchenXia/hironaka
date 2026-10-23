import DeJongAlterations.Algebra.ProjectiveLinearCoordinatesMatrixGraded
import DeJongAlterations.Geometry.ProjStructureMap
import DeJongAlterations.Projective

/-!
# Actual original linear algebra internally constructs whole native projective-space automorphisms
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace DeJongAlterations.Geometry.ProjectiveLinearCoordinates

open ProjectiveIdeal Algebra.ProjectiveLinearCoordinates

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)

/-- The whole actual native scheme automorphism is internally constructed from the original entire actual linear equivalence, in every original projective dimension. -/
def linearAutomorphism (e : (Fin (n + 1) → k) ≃ₗ[k] (Fin (n + 1) → k)) :
    projectiveSpace k n ≅ projectiveSpace k n where
  hom := Proj.map (linearGradedMap k n e) (linearGradedMap_irrelevant_le k n e)
  inv := Proj.map (linearGradedMap k n e.symm) (linearGradedMap_irrelevant_le k n e.symm)
  hom_inv_id := by
    rw [← Proj.map_comp]
    change Proj.map ((linearGradedMap k n e).comp (linearGradedMap k n e.symm)) _ =
      𝟙 (Proj (ProjectiveGrading k n))
    simpa only [linearGradedMap_comp_symm] using (Proj.map_id (𝒜 := ProjectiveGrading k n))
  inv_hom_id := by
    rw [← Proj.map_comp]
    change Proj.map ((linearGradedMap k n e.symm).comp (linearGradedMap k n e)) _ =
      𝟙 (Proj (ProjectiveGrading k n))
    simpa only [linearGradedMap_symm_comp] using (Proj.map_id (𝒜 := ProjectiveGrading k n))

/-- The actual original native linear automorphism preserves its literal entire original coefficient structure. -/
@[reassoc]
theorem linearAutomorphism_structure
    (e : (Fin (n + 1) → k) ≃ₗ[k] (Fin (n + 1) → k)) :
    (linearAutomorphism k n e).hom ≫ projectiveSpaceStructure k n =
      projectiveSpaceStructure k n := by
  apply ProjStructureMap.map_toSpec_base
  apply RingHom.ext
  intro a
  apply Subtype.ext
  exact (linearPolynomialEquiv k e).commutes a

/-- Every whole original homogeneous basic-open preimage is exactly the SAME actual original linear polynomial substitution. -/
@[simp]
theorem linearAutomorphism_preimage_basicOpen
    (e : (Fin (n + 1) → k) ≃ₗ[k] (Fin (n + 1) → k)) (F : MvPolynomial (Fin (n + 1)) k) :
    (linearAutomorphism k n e).hom ⁻¹ᵁ Proj.basicOpen (ProjectiveGrading k n) F =
      Proj.basicOpen (ProjectiveGrading k n) (linearPolynomialEquiv k e F) :=
  Proj.map_preimage_basicOpen _ _ F

end DeJongAlterations.Geometry.ProjectiveLinearCoordinates
