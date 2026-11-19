import Hironaka.Geometry.QuotGrassmannPivotOverlapEvaluation
import Hironaka.Geometry.QuotGrassmannPivotOverlapChange
import Hironaka.Algebra.PluckerQuotTransitionCommonNormalize

/-!
# Every ORIGINAL right overlap variable is forced by actual original Cramer products

The SAME actual derived overlap homomorphism evaluates the entire left
matrix. Exact Cramer products and the produced original unit minor then
identify each original right variable without mapping a chosen inverse.
-/

noncomputable section

open scoped Classical

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuot Algebra.PluckerQuotTransition Algebra.ModuleFlatteningMinors

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] {A ι ν : Type u} [CommRing A] [Algebra R A]
  [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
  (p t : (ι ⊕ ν) ≃ (ι ⊕ ν)) (C D : Matrix ι ν A)
  (h : (splitNormalizedMatrix p C).mulVecLin.ker = (splitNormalizedMatrix t D).mulVecLin.ker)

/-- The ENTIRE actual original left overlap matrix evaluates to SAME original split normalized matrix. -/
theorem originalCommonKernelOverlapEvaluation_left_matrix :
    (pivotOverlapMatrix R p (pivotIndex (coordinateSelector ι ν) t)).map
      (originalCommonKernelOverlapEvaluation R p t C D h) = splitNormalizedMatrix p C := by
  ext i j
  change ((originalCommonKernelOverlapEvaluation R p t C D h).comp
    (pivotOverlapPolynomialMap R p (pivotIndex (coordinateSelector ι ν) t)))
      (pivotUniversalMatrix R p i j) = _
  rw [originalCommonKernelOverlapEvaluation_left_polynomial]
  exact congrFun (congrFun (originalMatrixCoefficientEvaluation_pivotMatrix R p C) i) j

/-- EVERY original selected minor of SAME actual original left overlap matrix has its SAME evaluated original minor value. -/
theorem originalCommonKernelOverlapEvaluation_left_minor (s : ι → ι ⊕ ν) :
    originalCommonKernelOverlapEvaluation R p t C D h
      (columnMinor (pivotOverlapMatrix R p (pivotIndex (coordinateSelector ι ν) t)) s) =
        columnMinor (splitNormalizedMatrix p C) s := by
  let ψ := originalCommonKernelOverlapEvaluation R p t C D h
  have hm : ψ.mapMatrix (selectedMatrix
      (pivotOverlapMatrix R p (pivotIndex (coordinateSelector ι ν) t)) s) =
      selectedMatrix (splitNormalizedMatrix p C) s := by
    ext i j
    exact congrFun (congrFun (originalCommonKernelOverlapEvaluation_left_matrix R p t C D h) i) (s j)
  exact (ψ.map_det (selectedMatrix
    (pivotOverlapMatrix R p (pivotIndex (coordinateSelector ι ν) t)) s)).trans (congrArg Matrix.det hm)

/-- Every ORIGINAL right polynomial variable has its SAME second original matrix value, derived from actual Cramer products and the produced original unit cross-pivot minor. -/
theorem originalCommonKernelOverlapEvaluation_right_variable (i : ι) (j : ν) :
    originalCommonKernelOverlapEvaluation R p t C D h
      (pivotOverlapRightPolynomialMap R p t (MvPolynomial.X (i, j))) = D i j := by
  let k := pivotIndex (coordinateSelector ι ν) t
  let L := pivotOverlapMatrix R p k
  let ψ := originalCommonKernelOverlapEvaluation R p t C D h
  have hsel : coordinateSelector ι ν k = t ∘ Sum.inl :=
    (coordinateSelector ι ν).apply_symm_apply _
  have huL : IsUnit (columnMinor L (t ∘ Sum.inl)) := by
    have hunit := pivotOverlapMatrix_pivot_isUnit R p k
    rw [hsel] at hunit
    exact hunit
  have hs := pivotNormalize_entry_mul_det L (t ∘ Sum.inl) huL i (t (Sum.inr j))
  rw [pivotOverlap_normalize_eq_right R p t] at hs
  have hh := congrArg ψ hs
  simp only [map_mul] at hh
  rw [originalCommonKernelOverlapEvaluation_left_minor R p t C D h,
    originalCommonKernelOverlapEvaluation_left_minor R p t C D h] at hh
  have hentry : pivotOverlapRightMatrix R p t i (t (Sum.inr j)) =
      pivotOverlapRightPolynomialMap R p t (MvPolynomial.X (i, j)) := by
    change pivotOverlapRightPolynomialMap R p t (pivotUniversalMatrix R t i (t (Sum.inr j))) = _
    simp only [pivotUniversalMatrix, splitNormalizedMatrix_apply, normalizedMatrix_inr]
  rw [hentry] at hh
  have hu := originalCommonKernel_pivotMinor_isUnit p t C D h
  have hc := pivotNormalize_entry_mul_det (splitNormalizedMatrix p C) (t ∘ Sum.inl) hu i (t (Sum.inr j))
  rw [originalCommonKernel_pivotNormalize_eq p t C D h, splitNormalizedMatrix_apply, normalizedMatrix_inr] at hc
  exact hu.mul_left_cancel (hh.trans hc.symm)

end Hironaka.Geometry.QuotGrassmann
