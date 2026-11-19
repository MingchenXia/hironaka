import Hironaka.Geometry.QuotGrassmannPivotOverlapCoefficients
import Hironaka.Geometry.QuotGrassmannPivotOverlapRightValues

/-!
# SAME actual derived overlap evaluation retains the WHOLE original right polynomial map
-/

noncomputable section

open scoped Classical

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuot Algebra.PluckerQuotTransition

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] {A ι ν : Type u} [CommRing A] [Algebra R A]
  [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
  (p t : (ι ⊕ ν) ≃ (ι ⊕ ν)) (C D : Matrix ι ν A)
  (h : (splitNormalizedMatrix p C).mulVecLin.ker = (splitNormalizedMatrix t D).mulVecLin.ker)

/-- The ENTIRE original right polynomial coefficient map of SAME native overlap evaluates at SAME second original matrix, with ALL original scalar and variable values internally derived. -/
theorem originalCommonKernelOverlapEvaluation_right_polynomial :
    (originalCommonKernelOverlapEvaluation R p t C D h).comp (pivotOverlapRightPolynomialMap R p t) =
      (originalMatrixCoefficientEvaluation R D).toRingHom := by
  apply MvPolynomial.ringHom_ext'
  · change ((originalCommonKernelOverlapEvaluation R p t C D h).comp
      (pivotOverlapRightPolynomialMap R p t)).comp (algebraMap R (ChartRing R ι ν)) =
      (originalMatrixCoefficientEvaluation R D).toRingHom.comp (algebraMap R (ChartRing R ι ν))
    rw [RingHom.comp_assoc, ← originalOverlapPolynomialMaps_coeff_eq,
      ← RingHom.comp_assoc, originalCommonKernelOverlapEvaluation_left_polynomial,
      originalMatrixCoefficientEvaluation_coeff, originalMatrixCoefficientEvaluation_coeff]
  · rintro ⟨i, j⟩
    exact (originalCommonKernelOverlapEvaluation_right_variable R p t C D h i j).trans
      (originalMatrixCoefficientEvaluation_X R D i j).symm

end Hironaka.Geometry.QuotGrassmann
