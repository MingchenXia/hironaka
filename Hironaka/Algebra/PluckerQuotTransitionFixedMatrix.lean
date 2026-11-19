import Hironaka.Algebra.PluckerQuotTransitionFixedIndices

/-!
# WHOLE original matrix quotient in fixed ORIGINAL row and ambient coordinates

Both source and target reindexing maps are actual equivalences constructed
from the SAME original selected columns and their prescribed rank cardinal.
-/

noncomputable section

open scoped Classical

namespace Hironaka.Algebra.PluckerQuotTransition

universe u

variable {B ι ν I : Type u} [CommRing B] [Fintype ι] [Fintype ν] [Fintype I]
  [DecidableEq ι] [DecidableEq ν] [DecidableEq I]
  (C : Matrix I (ι ⊕ ν) B) (a : I ↪ (ι ⊕ ν)) (hcard : Nat.card I = Fintype.card ι)

/-- EVERY original fixed-row matrix coefficient is the SAME actual original complementary column coefficient. -/
def originalFixedPivotCoefficientMatrix : Matrix ι ν B :=
  fun i j => C (originalFixedPivotRowEquiv hcard i) (originalFixedPivotPermutation a hcard (Sum.inr j))

/-- The ENTIRE actual original fixed-row/pivot reindexed matrix is the original normalized matrix. -/
theorem originalFixedPivotMatrix_normalized
    (h : ∀ i j, C i (a j) = if i = j then 1 else 0) :
    C.submatrix (originalFixedPivotRowEquiv hcard) (originalFixedPivotPermutation a hcard) =
      PluckerQuot.normalizedMatrix (originalFixedPivotCoefficientMatrix C a hcard) := by
  ext i j
  cases j with
  | inl j =>
    simp only [Matrix.submatrix_apply, originalFixedPivotPermutation_inl,
      PluckerQuot.normalizedMatrix_inl, Matrix.one_apply, h, Equiv.apply_eq_iff_eq]
  | inr j =>
    simp only [Matrix.submatrix_apply, PluckerQuot.normalizedMatrix_inr,
      originalFixedPivotCoefficientMatrix]

/-- WHOLE actual fixed-original-row target and original ambient pivot source reindexing identifies SAME original matrix map with its frozen original normalized quotient. -/
theorem originalFixedPivotMatrix_whole_quotient
    (h : ∀ i j, C i (a j) = if i = j then 1 else 0) :
    (LinearEquiv.funCongrLeft B B (originalFixedPivotRowEquiv hcard)).toLinearMap.comp
      (C.mulVecLin.comp
        (LinearEquiv.funCongrLeft B B (originalFixedPivotPermutation a hcard).symm).toLinearMap) =
      PluckerQuot.matrixQuotient (originalFixedPivotCoefficientMatrix C a hcard) := by
  have hm := Matrix.mulVecLin_submatrix (R := B) (originalFixedPivotRowEquiv hcard)
    (originalFixedPivotPermutation a hcard) C
  rw [originalFixedPivotMatrix_normalized C a hcard h, PluckerQuot.normalizedMatrix_mulVecLin] at hm
  exact hm.symm

end Hironaka.Algebra.PluckerQuotTransition
