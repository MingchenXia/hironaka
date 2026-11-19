import Hironaka.Geometry.ProjectiveLinearCoordinatesScalarPointComparison
import Hironaka.Geometry.ProjectiveSecantProjectionOriginalGraded
import Hironaka.Geometry.ProjectiveProjectionMapSquare

/-!
# Original rational points internally give the entire graded projection coefficient square
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveRationalPointCoordinates ProjectiveSpaceBaseChange
open ProjectiveLinearCoordinates Algebra.ProjectiveLinearCoordinates BlowupProjectiveEmbedding

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)
  (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
  (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)

/-- The entire exact original rational-point projection forms as one actual original graded map. -/
def pointProjectionGradedMap : ProjectiveGrading k n →+*ᵍ ProjectiveGrading k (n + 1) :=
  (coordinateGradedMap k n (pointVector k n p hp) (pointVector_ne_zero k n p hp)).comp
    (remainingVariableGradedMap k n)

variable (L : Type u) [Field L] (φ : k →+* L)

/-- The actual inverse target-coordinate substitution followed by the SAME original coefficient map, produced internally from the SAME original rational scheme point. -/
def scalarProjectionTargetCoefficientGradedMap : ProjectiveGrading k n →+*ᵍ ProjectiveGrading L n :=
  (linearGradedMap L n (scalarPointTargetLinearEquiv k L φ n p hp).symm).comp (coefficientGradedMap φ)

/-- The internally constructed actual inverse target map and actual coefficient map supply genuine native irrelevant containment. -/
theorem scalarProjectionTargetCoefficientGradedMap_irrelevant_le :
    HomogeneousIdeal.irrelevant (ProjectiveGrading L n) ≤
      (HomogeneousIdeal.irrelevant (ProjectiveGrading k n)).map
        (scalarProjectionTargetCoefficientGradedMap k n p hp L φ) :=
  HomogeneousIdeal.irrelevant_le_map_comp (coefficientGradedMap_irrelevant_le φ)
    (linearGradedMap_irrelevant_le L n (scalarPointTargetLinearEquiv k L φ n p hp).symm)

/-- The SAME actual original rational point gives the literal ENTIRE original graded projection coefficient square, with both independent actual normalizations produced internally. -/
theorem pointProjectionGraded_coefficient_square :
    (coefficientGradedMap φ).comp (pointProjectionGradedMap k n p hp) =
      (pointProjectionGradedMap L n (scalarPoint k L φ n p hp) (scalarPoint_structure k L φ n p hp)).comp
        (scalarProjectionTargetCoefficientGradedMap k n p hp L φ) := by
  apply DFunLike.ext
  intro F
  exact (scalarPoint_originalPolynomial_coefficient_triangle k L φ n p hp F).symm

/-- The actual native scheme map of the entire original target graded composite is exactly the SAME internally constructed inverse target automorphism followed by the SAME original coefficient morphism. -/
theorem scalarProjectionTargetCoefficientGradedMap_native :
    Proj.map (scalarProjectionTargetCoefficientGradedMap k n p hp L φ)
      (scalarProjectionTargetCoefficientGradedMap_irrelevant_le k n p hp L φ) =
      (scalarPointTargetAutomorphism k L φ n p hp).inv ≫ projectiveCoefficientMap φ n := by
  change Proj.map ((linearGradedMap L n (scalarPointTargetLinearEquiv k L φ n p hp).symm).comp
    (coefficientGradedMap φ)) _ =
    Proj.map (linearGradedMap L n (scalarPointTargetLinearEquiv k L φ n p hp).symm) _ ≫
      Proj.map (coefficientGradedMap φ) _
  exact Proj.map_comp (coefficientGradedMap φ)
    (linearGradedMap L n (scalarPointTargetLinearEquiv k L φ n p hp).symm)
    (coefficientGradedMap_irrelevant_le φ)
    (linearGradedMap_irrelevant_le L n (scalarPointTargetLinearEquiv k L φ n p hp).symm)

end Hironaka.Geometry.ProjectiveSecant
