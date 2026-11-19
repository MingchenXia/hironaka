import Hironaka.Geometry.ProjectiveLinearCoordinatesMatrixAutomorphism
import Hironaka.Algebra.ProjectiveLinearCoordinatesScalarPolynomial
import Hironaka.Geometry.ProjectiveSpaceBaseChange

/-!
# Actual original native projective linear automorphisms retain the literal entire scalar coefficient square
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveLinearCoordinates

open ProjectiveIdeal ProjectiveSpaceBaseChange BlowupProjectiveEmbedding
open Algebra.ProjectiveLinearCoordinates

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k L : Type u) [Field k] [Field L] (φ : k →+* L) (n : ℕ)
  (e : (Fin (n + 1) → k) ≃ₗ[k] (Fin (n + 1) → k))

/-- The actual entire original graded coefficient square commutes with the SAME internally constructed actual scalar linear equivalence. -/
theorem scalar_linearGradedMap_square :
    (coefficientGradedMap φ).comp (linearGradedMap k n e) =
      (linearGradedMap L n (scalarLinearEquiv k L φ e)).comp (coefficientGradedMap φ) := by
  apply DFunLike.ext
  intro F
  exact scalarLinearEquiv_polynomial_coefficient_triangle k L φ e F

/-- The actual whole scalar native projective linear automorphism retains the literal entire original native coefficient square. -/
theorem linearAutomorphism_scalar_coefficient :
    (linearAutomorphism L n (scalarLinearEquiv k L φ e)).hom ≫ projectiveCoefficientMap φ n =
      projectiveCoefficientMap φ n ≫ (linearAutomorphism k n e).hom := by
  change Proj.map (linearGradedMap L n (scalarLinearEquiv k L φ e)) _ ≫
      Proj.map (coefficientGradedMap φ) _ =
    Proj.map (coefficientGradedMap φ) _ ≫ Proj.map (linearGradedMap k n e) _
  rw [← Proj.map_comp, ← Proj.map_comp]
  congr 1
  exact (scalar_linearGradedMap_square k L φ n e).symm

end Hironaka.Geometry.ProjectiveLinearCoordinates
