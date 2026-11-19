import Hironaka.Analytic.Unibranch.HironakaG10SquareZeroMatrixAlgebraEquiv

/-! The actual holomorphic linear germs encoding the original matrix columns. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Hironaka Hironaka
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalJet
  Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalVector
  Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalAlgebraEquiv
namespace Hironaka.Analytic.Unibranch.HironakaG10ActualSquareZeroColumns
noncomputable section

/-- The literal original germ obtained by pairing a matrix column with the normal coordinates. -/
def actualMatrixColumn (d a : ℕ) {b : ℕ}
    (F : Matrix (Fin a) (Fin b) (HolGerm (ComplexModel d))) (j : Fin b) :
    HolGerm (ComplexModel (d+a)) :=
  ∑ i, tangentPullback d a (F i j) * normalCoordinate d a i

/-- The square-zero algebra equivalence sends each original column to the
class of its actual holomorphic normal-linear germ. -/
theorem firstOrderNormalAlgEquiv_matrixColumn (d a : ℕ) {b : ℕ}
    (F : Matrix (Fin a) (Fin b) (HolGerm (ComplexModel d))) (j : Fin b) :
    letI := tangentAlgebra d a
    firstOrderNormalAlgEquiv d a (TrivSqZeroExt.inr (F.col j)) =
      Ideal.Quotient.mk (normalIdeal d a ^ 2) (actualMatrixColumn d a F j) := by
  classical
  let _ := tangentAlgebra d a
  change firstOrderNormalLinearEquiv d a (0,F.col j) = _
  rw [firstOrderNormalLinearEquiv_vector]
  simp only [actualMatrixColumn, map_sum, map_mul, Matrix.col_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap]
  rfl
end
end Hironaka.Analytic.Unibranch.HironakaG10ActualSquareZeroColumns
