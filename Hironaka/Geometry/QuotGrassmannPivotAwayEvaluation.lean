import Hironaka.Geometry.QuotGrassmannPivotOverlapRatio
import Hironaka.Algebra.PluckerQuotTransitionEvaluatedMinors
import Hironaka.Algebra.PluckerQuotTransitionCommonPivot

/-!
# Actual original native away-ring evaluation retains every original cross-pivot ratio
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

/-- The actual original polynomial coefficient evaluation composed with the inverse SAME native whole pivot-ring equivalence. -/
def originalPivotAwayEvaluation (p : (ι ⊕ ν) ≃ (ι ⊕ ν)) (C : Matrix ι ν A) :
    PivotAwayRing R ι ν (pivotIndex (coordinateSelector ι ν) p) →+* A :=
  (originalMatrixCoefficientEvaluation R C).toRingHom.comp (pivotPolynomialAwayEquiv R p).symm.toRingHom

/-- EVERY original native other-pivot ratio evaluates to SAME actual original selected minor. -/
theorem originalPivotAwayEvaluation_nativeRatio
    (p t : (ι ⊕ ν) ≃ (ι ⊕ ν)) (C : Matrix ι ν A) :
    originalPivotAwayEvaluation R p C
      (nativePivotRatio R ι ν (pivotIndex (coordinateSelector ι ν) p)
        (pivotIndex (coordinateSelector ι ν) t)) =
      columnMinor (splitNormalizedMatrix p C) (t ∘ Sum.inl) := by
  have hr : pivotPolynomialAwayEquiv R p (columnMinor (pivotUniversalMatrix R p) (t ∘ Sum.inl)) =
      nativePivotRatio R ι ν (pivotIndex (coordinateSelector ι ν) p)
        (pivotIndex (coordinateSelector ι ν) t) := by
    rw [pivotPolynomialAwayEquiv_minor, pivotRatioHom_coordinate]
    rfl
  rw [← hr]
  change originalMatrixCoefficientEvaluation R C
    ((pivotPolynomialAwayEquiv R p).symm (pivotPolynomialAwayEquiv R p
      (columnMinor (pivotUniversalMatrix R p) (t ∘ Sum.inl)))) = _
  rw [RingEquiv.symm_apply_apply]
  exact originalMatrixCoefficientEvaluation_minor R p C (t ∘ Sum.inl)

/-- SAME entire original quotient kernel INTERNALLY makes actual native other-pivot ratio image a unit, with no supplied invertibility condition. -/
theorem originalPivotAwayEvaluation_nativeRatio_isUnit
    (p t : (ι ⊕ ν) ≃ (ι ⊕ ν)) (C D : Matrix ι ν A)
    (h : (splitNormalizedMatrix p C).mulVecLin.ker = (splitNormalizedMatrix t D).mulVecLin.ker) :
    IsUnit (originalPivotAwayEvaluation R p C
      (nativePivotRatio R ι ν (pivotIndex (coordinateSelector ι ν) p)
        (pivotIndex (coordinateSelector ι ν) t))) := by
  rw [originalPivotAwayEvaluation_nativeRatio]
  exact originalCommonKernel_pivotMinor_isUnit p t C D h

end Hironaka.Geometry.QuotGrassmann
