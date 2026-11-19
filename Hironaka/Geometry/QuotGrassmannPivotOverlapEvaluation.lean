import Hironaka.Geometry.QuotGrassmannPivotAwayEvaluation
import Hironaka.Geometry.QuotGrassmannPivotOverlapMatrix

/-!
# SAME original common quotient kernel constructs actual native overlap evaluation

The native product-open localization and unit ratio image are internally
proved on SAME original rings. The left coefficient triangle is a WHOLE
original polynomial ring-map equality, not just pointwise chart data.
-/

noncomputable section

open scoped Classical
open HomogeneousLocalization

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuot Algebra.PluckerQuotTransition Algebra.ModuleFlatteningMinors

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] (ι ν : Type u)
  [Fintype ι] [Fintype ν] [DecidableEq ι]

/-- The SAME native product-open ring is the genuine localization of SAME original away ring at its literal other-pivot ratio, under ORIGINAL restriction. -/
theorem originalNativeOverlapRestriction_isLocalizationAway
    (j k : Fin (pluckerDimension ι ν + 1)) :
    letI : Algebra (PivotAwayRing R ι ν j) (PivotOverlapRing R ι ν j k) :=
      (pivotOverlapRestriction R ι ν j k).toAlgebra
    IsLocalization.Away (nativePivotRatio R ι ν j k) (PivotOverlapRing R ι ν j k) := by
  let : Algebra (PivotAwayRing R ι ν j) (PivotOverlapRing R ι ν j k) :=
    (pivotOverlapRestriction R ι ν j k).toAlgebra
  simpa only [Away.isLocalizationElem, pow_one, nativePivotRatio] using
    Away.isLocalization_mul (coordinateClass_homogeneous R ι ν j)
      (coordinateClass_homogeneous R ι ν k) rfl (by decide : (1 : ℕ) ≠ 0)

variable {ι ν} [DecidableEq ν] {A : Type u} [CommRing A] [Algebra R A]
  (p t : (ι ⊕ ν) ≃ (ι ⊕ ν)) (C D : Matrix ι ν A)
  (h : (splitNormalizedMatrix p C).mulVecLin.ker = (splitNormalizedMatrix t D).mulVecLin.ker)

/-- The ACTUAL original common kernel derives the entire native overlap evaluation, with no supplied unit-minor or localization extension certificate. -/
def originalCommonKernelOverlapEvaluation :
    PivotOverlapRing R ι ν (pivotIndex (coordinateSelector ι ν) p)
      (pivotIndex (coordinateSelector ι ν) t) →+* A :=
  let j := pivotIndex (coordinateSelector ι ν) p
  let k := pivotIndex (coordinateSelector ι ν) t
  let : Algebra (PivotAwayRing R ι ν j) (PivotOverlapRing R ι ν j k) :=
    (pivotOverlapRestriction R ι ν j k).toAlgebra
  let := originalNativeOverlapRestriction_isLocalizationAway R ι ν j k
  IsLocalization.Away.lift (S := PivotOverlapRing R ι ν j k)
    (nativePivotRatio R ι ν j k) (g := originalPivotAwayEvaluation R p C)
    (originalPivotAwayEvaluation_nativeRatio_isUnit R p t C D h)

/-- The WHOLE actual original native localization restriction triangle for SAME produced overlap evaluation. -/
theorem originalCommonKernelOverlapEvaluation_restriction :
    (originalCommonKernelOverlapEvaluation R p t C D h).comp
      (pivotOverlapRestriction R ι ν (pivotIndex (coordinateSelector ι ν) p)
        (pivotIndex (coordinateSelector ι ν) t)) = originalPivotAwayEvaluation R p C := by
  let j := pivotIndex (coordinateSelector ι ν) p
  let k := pivotIndex (coordinateSelector ι ν) t
  let : Algebra (PivotAwayRing R ι ν j) (PivotOverlapRing R ι ν j k) :=
    (pivotOverlapRestriction R ι ν j k).toAlgebra
  let := originalNativeOverlapRestriction_isLocalizationAway R ι ν j k
  exact IsLocalization.Away.lift_comp (S := PivotOverlapRing R ι ν j k)
    (nativePivotRatio R ι ν j k) (g := originalPivotAwayEvaluation R p C)
    (originalPivotAwayEvaluation_nativeRatio_isUnit R p t C D h)

/-- The ENTIRE original left polynomial coefficient map of SAME actual native overlap evaluates at SAME original matrix coefficients. -/
theorem originalCommonKernelOverlapEvaluation_left_polynomial :
    (originalCommonKernelOverlapEvaluation R p t C D h).comp
      (pivotOverlapPolynomialMap R p (pivotIndex (coordinateSelector ι ν) t)) =
      (originalMatrixCoefficientEvaluation R C).toRingHom := by
  rw [pivotOverlapPolynomialMap, ← RingHom.comp_assoc,
    originalCommonKernelOverlapEvaluation_restriction]
  apply RingHom.ext
  intro F
  change originalMatrixCoefficientEvaluation R C
    ((pivotPolynomialAwayEquiv R p).symm (pivotPolynomialAwayEquiv R p F)) =
      originalMatrixCoefficientEvaluation R C F
  rw [RingEquiv.symm_apply_apply]

end Hironaka.Geometry.QuotGrassmann
