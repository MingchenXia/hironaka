import Hironaka.Algebra.PluckerQuotTransitionAlgebra

/-!
# Actual original coefficient evaluation preserves the entire original pivot matrix
-/

noncomputable section

open scoped Classical

namespace Hironaka.Algebra.PluckerQuotTransition

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] {A ι ν : Type u} [CommRing A] [Algebra R A]
  [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]

/-- Literal evaluation at SAME original matrix coefficients in the actual original polynomial ring. -/
def originalMatrixCoefficientEvaluation (C : Matrix ι ν A) : MvPolynomial (ι × ν) R →ₐ[R] A :=
  MvPolynomial.aeval fun ij => C ij.1 ij.2

omit [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν] in
/-- Every original coefficient variable has its SAME actual original matrix value. -/
theorem originalMatrixCoefficientEvaluation_X (C : Matrix ι ν A) (i : ι) (j : ν) :
    originalMatrixCoefficientEvaluation R C (MvPolynomial.X (i, j)) = C i j :=
  MvPolynomial.aeval_X _ _

omit [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν] in
/-- The WHOLE original coefficient-ring triangle of actual polynomial evaluation. -/
theorem originalMatrixCoefficientEvaluation_coeff (C : Matrix ι ν A) :
    (originalMatrixCoefficientEvaluation R C).toRingHom.comp
      (algebraMap R (MvPolynomial (ι × ν) R)) = algebraMap R A := by
  ext r
  exact (originalMatrixCoefficientEvaluation R C).commutes r

omit [Fintype ι] in
/-- The ENTIRE actual original universal pivot matrix evaluates to SAME original split normalized matrix. -/
theorem originalMatrixCoefficientEvaluation_pivotMatrix
    (p : (ι ⊕ ν) ≃ (ι ⊕ ν)) (C : Matrix ι ν A) :
    (PluckerQuot.pivotUniversalMatrix R p).map (originalMatrixCoefficientEvaluation R C) =
      PluckerQuot.splitNormalizedMatrix p C := by
  ext i j
  obtain ⟨k, rfl⟩ := p.surjective j
  cases k <;> simp [Matrix.map_apply, PluckerQuot.pivotUniversalMatrix,
    PluckerQuot.splitNormalizedMatrix, originalMatrixCoefficientEvaluation, Matrix.one_apply,
    PluckerQuot.normalizedMatrix_inl, PluckerQuot.normalizedMatrix_inr]

end Hironaka.Algebra.PluckerQuotTransition
