import Hironaka.Algebra.PluckerQuotTransitionLinear
import Hironaka.Algebra.GrassmannQuotientKernel
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# WHOLE original split normalized quotient and its actual tensor source
-/

noncomputable section

open scoped Classical
open TensorProduct

namespace Hironaka.Algebra.PluckerQuotTransition

universe u

variable {A ι ν : Type u} [CommRing A] [Fintype ι] [Fintype ν]
  [DecidableEq ι] [DecidableEq ν]
  (p : (ι ⊕ ν) ≃ (ι ⊕ ν)) (C : Matrix ι ν A)

/-- The WHOLE split original matrix becomes the frozen original quotient through its actual original ambient pivot isomorphism. -/
theorem originalSplitNormalizedMatrix_whole_quotient :
    (PluckerQuot.splitNormalizedMatrix p C).mulVecLin.comp
      (LinearEquiv.funCongrLeft A A p.symm).toLinearMap = PluckerQuot.matrixQuotient C := by
  have hm : (PluckerQuot.splitNormalizedMatrix p C).submatrix id p =
      PluckerQuot.normalizedMatrix C := by
    ext i j
    simp only [Matrix.submatrix_apply, id_eq, PluckerQuot.splitNormalizedMatrix_apply]
  have h := Matrix.mulVecLin_submatrix (R := A) id p (PluckerQuot.splitNormalizedMatrix p C)
  rw [hm, PluckerQuot.normalizedMatrix_mulVecLin] at h
  exact h.symm

/-- SAME actual original split normalized matrix is surjective, derived from its actual whole original source triangle. -/
theorem originalSplitNormalizedMatrix_surjective :
    Function.Surjective (PluckerQuot.splitNormalizedMatrix p C).mulVecLin := by
  intro y
  obtain ⟨v, hv⟩ := PluckerQuot.matrixQuotient_surjective C y
  refine ⟨LinearEquiv.funCongrLeft A A p.symm v, ?_⟩
  exact (LinearMap.congr_fun (originalSplitNormalizedMatrix_whole_quotient p C) v).trans hv

/-- The actual original normalized matrix quotient on its unchanged original tensor source is surjective. -/
theorem originalSplitNormalizedMatrix_tensor_surjective
    (R : Type u) [CommRing R] [Algebra R A] :
    Function.Surjective ((PluckerQuot.splitNormalizedMatrix p C).mulVecLin.comp
      (TensorProduct.piScalarRight R A A (ι ⊕ ν)).toLinearMap) :=
  (originalSplitNormalizedMatrix_surjective p C).comp (TensorProduct.piScalarRight R A A (ι ⊕ ν)).surjective

end Hironaka.Algebra.PluckerQuotTransition
