import Hironaka.Geometry.ProjectiveLinearCoordinatesVectorPoint
import Hironaka.Geometry.ProjectiveLinearCoordinatesMatrixAutomorphism
import Hironaka.Algebra.ProjectiveLinearCoordinatesComparisonPolynomial

/-!
# The SAME actual original projective centre internally produces its whole target-coordinate comparison
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveLinearCoordinates

open ProjectiveProjectionCenter Algebra.ProjectiveLinearCoordinates

universe u

variable (k : Type u) [Field k] (n : ℕ)
  (v : Fin (n + 2) → k) (hv : v ≠ 0) (w : Fin (n + 2) → k) (hw : w ≠ 0)
  (h : vectorPoint k n v hv = vectorPoint k n w hw)

/-- The actual original native projective centre internally supplies a nonzero coordinate-comparison scalar. -/
def originalPointComparisonScalar : k :=
  (exists_nonzero_smul_of_vectorPoint_eq k n v hv w hw h).choose

/-- The internally obtained actual original comparison scalar is nonzero and preserves the exact original vectors. -/
theorem originalPointComparisonScalar_spec :
    originalPointComparisonScalar k n v hv w hw h ≠ 0 ∧
      w = originalPointComparisonScalar k n v hv w hw h • v :=
  (exists_nonzero_smul_of_vectorPoint_eq k n v hv w hw h).choose_spec

/-- The actual entire remaining-coordinate comparison is internally constructed from the SAME actual native original projective point. -/
def originalPointTargetLinearEquiv : (Fin (n + 1) → k) ≃ₗ[k] (Fin (n + 1) → k) :=
  normalizationRemainingLinearEquiv k n v hv w hw (originalPointComparisonScalar k n v hv w hw h)
    (originalPointComparisonScalar_spec k n v hv w hw h).1
    (originalPointComparisonScalar_spec k n v hv w hw h).2

/-- The actual whole target scheme automorphism is internally produced from the SAME original native projective centre; none is supplied. -/
def originalPointTargetAutomorphism : projectiveSpace k n ≅ projectiveSpace k n :=
  linearAutomorphism k n (originalPointTargetLinearEquiv k n v hv w hw h)

/-- The internally produced actual entire target scheme automorphism retains the exact original coefficient triangle. -/
@[reassoc]
theorem originalPointTargetAutomorphism_structure :
    (originalPointTargetAutomorphism k n v hv w hw h).hom ≫ projectiveSpaceStructure k n =
      projectiveSpaceStructure k n :=
  linearAutomorphism_structure k n _

/-- The SAME actual native original point internally gives the literal ENTIRE original polynomial projection comparison for the independently chosen original normalizations. -/
theorem originalPoint_normalizationPolynomial_triangle (F : MvPolynomial (Fin (n + 1)) k) :
    coordinatePolynomialEquiv k n w hw (MvPolynomial.rename Fin.succ F) =
      coordinatePolynomialEquiv k n v hv (MvPolynomial.rename Fin.succ
        (linearPolynomialEquiv k (originalPointTargetLinearEquiv k n v hv w hw h) F)) :=
  normalizationRemainingPolynomial_triangle k n v hv w hw
    (originalPointComparisonScalar k n v hv w hw h)
    (originalPointComparisonScalar_spec k n v hv w hw h).1
    (originalPointComparisonScalar_spec k n v hv w hw h).2 F

end Hironaka.Geometry.ProjectiveLinearCoordinates
