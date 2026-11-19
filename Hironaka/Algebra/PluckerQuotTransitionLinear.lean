import Hironaka.Algebra.PluckerQuotTransitionMatrix
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The same original normalized matrix is the original quotient linear map

The matrix representation retains every original free coordinate and is
compared on the entire original free module.
-/

noncomputable section

namespace Hironaka.Algebra.PluckerQuot

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {ι κ : Type u}
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The actual full original normalized matrix realizes exactly the originally frozen quotient map. -/
theorem normalizedMatrix_mulVecLin (a : Matrix ι κ R) :
    (normalizedMatrix a).mulVecLin = matrixQuotient a := by
  apply LinearMap.ext
  intro v
  funext i
  change (∑ k, normalizedMatrix a i k * v k) = matrixQuotient a v i
  rw [matrixQuotient_apply, Fintype.sum_sum_type]
  simp only [normalizedMatrix_inl, normalizedMatrix_inr, Matrix.one_apply,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end Hironaka.Algebra.PluckerQuot
