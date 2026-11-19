import Hironaka.Analytic.Unibranch.HironakaG10SquareZeroMatrixQuotient

/-! The matrix-column quotient is the square-zero extension of the cokernel. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Hironaka.Analytic.Unibranch.HironakaG10SquareZeroMatrixQuotient
namespace Hironaka.Analytic.Unibranch.HironakaG10SquareZeroMatrixAlgebraEquiv
noncomputable section
variable {B : Type*} [CommRing B] {a b : ℕ}

/-- Quotienting the square-zero algebra by the original column ideal is
exactly the square-zero algebra of the original matrix cokernel. -/
def matrixColumnQuotientAlgEquiv (F : Matrix (Fin a) (Fin b) B) :
    (TrivSqZeroExt B (Fin a → B) ⧸ matrixColumnIdeal F) ≃ₐ[B]
      TrivSqZeroExt B ((Fin a → B) ⧸ LinearMap.range F.mulVecLin) :=
  (Ideal.quotientEquivAlgOfEq B (matrixQuotientMap_ker F).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (matrixQuotientMap_surjective F))
end
end Hironaka.Analytic.Unibranch.HironakaG10SquareZeroMatrixAlgebraEquiv
