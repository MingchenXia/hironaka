import Hironaka.Algebra.PluckerQuotTransitionCommonQuotient
import Hironaka.Algebra.PluckerQuotTransitionSplitTensor
import Hironaka.Algebra.PluckerQuotTransitionOverlap
import Mathlib.LinearAlgebra.Determinant

/-!
# SAME original normalized kernel internally produces its actual unit cross-pivot
-/

noncomputable section

open scoped Classical

namespace Hironaka.Algebra.PluckerQuotTransition

open PluckerQuot ModuleFlatteningMinors

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A ι ν : Type u} [CommRing A] [Fintype ι] [Fintype ν]
  [DecidableEq ι] [DecidableEq ν]

/-- EVERY original pivot coordinate column of the actual split normalized quotient has its SAME original unit value. -/
theorem originalSplitNormalizedMatrix_pivot_column
    (p : (ι ⊕ ν) ≃ (ι ⊕ ν)) (C : Matrix ι ν A) (j : ι) :
    (splitNormalizedMatrix p C).mulVecLin (Pi.single (p (Sum.inl j)) 1) = Pi.single j 1 := by
  ext i
  simp [splitNormalizedMatrix_apply,
    normalizedMatrix_inl, Matrix.one_apply, Pi.single_apply, eq_comm]

/-- SAME entire original quotient kernel derives the actual selected cross-pivot matrix as the native matrix of the inverse ACTUAL produced target change. -/
theorem originalCommonKernel_selectedMatrix_eq_inverseTarget
    (p t : (ι ⊕ ν) ≃ (ι ⊕ ν)) (C D : Matrix ι ν A)
    (h : (splitNormalizedMatrix p C).mulVecLin.ker = (splitNormalizedMatrix t D).mulVecLin.ker) :
    let e := originalCommonQuotientTargetEquiv
      (splitNormalizedMatrix p C).mulVecLin (splitNormalizedMatrix t D).mulVecLin
      (originalSplitNormalizedMatrix_surjective p C) (originalSplitNormalizedMatrix_surjective t D) h
    selectedMatrix (splitNormalizedMatrix p C) (t ∘ Sum.inl) = LinearMap.toMatrix' e.symm.toLinearMap := by
  let e := originalCommonQuotientTargetEquiv
    (splitNormalizedMatrix p C).mulVecLin (splitNormalizedMatrix t D).mulVecLin
    (originalSplitNormalizedMatrix_surjective p C) (originalSplitNormalizedMatrix_surjective t D) h
  have he := originalCommonQuotientTargetEquiv_whole_triangle
    (splitNormalizedMatrix p C).mulVecLin (splitNormalizedMatrix t D).mulVecLin
    (originalSplitNormalizedMatrix_surjective p C) (originalSplitNormalizedMatrix_surjective t D) h
  ext i j
  have hc : (splitNormalizedMatrix p C).mulVecLin (Pi.single (t (Sum.inl j)) 1) = e.symm (Pi.single j 1) := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (LinearMap.congr_fun he (Pi.single (t (Sum.inl j)) 1)).trans
      (originalSplitNormalizedMatrix_pivot_column t D j)
  change splitNormalizedMatrix p C i (t (Sum.inl j)) = e.symm (Pi.single j 1) i
  simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply] using congrFun hc i

/-- The SAME original normalized quotient kernel INTERNALLY produces a unit original cross-pivot determinant, without a supplied unit-minor condition. -/
theorem originalCommonKernel_pivotMinor_isUnit
    (p t : (ι ⊕ ν) ≃ (ι ⊕ ν)) (C D : Matrix ι ν A)
    (h : (splitNormalizedMatrix p C).mulVecLin.ker = (splitNormalizedMatrix t D).mulVecLin.ker) :
    IsUnit (columnMinor (splitNormalizedMatrix p C) (t ∘ Sum.inl)) := by
  let e := originalCommonQuotientTargetEquiv
    (splitNormalizedMatrix p C).mulVecLin (splitNormalizedMatrix t D).mulVecLin
    (originalSplitNormalizedMatrix_surjective p C) (originalSplitNormalizedMatrix_surjective t D) h
  rw [columnMinor, originalCommonKernel_selectedMatrix_eq_inverseTarget p t C D h]
  simpa only [LinearMap.toMatrix_eq_toMatrix'] using
    e.symm.isUnit_det (Pi.basisFun A ι) (Pi.basisFun A ι)

end Hironaka.Algebra.PluckerQuotTransition
