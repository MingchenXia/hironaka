import Hironaka.Algebra.PluckerQuotTransitionLocalization
import Hironaka.Geometry.QuotGrassmannPivotScheme

/-!
# Actual other-pivot ratios on literal native projective intersections

All rings and restrictions are the native homogeneous localizations of the
same originally constructed Plücker model. The other pivot ratio becomes
a unit by the native localization theorem, without an assumed invertibility
or overlap-chart certificate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuot ProjectiveIdeal

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] (ι ν : Type u)
  [Fintype ι] [Fintype ν] [DecidableEq ι]

private local instance ratioChartAlgebra (j : Fin (pluckerDimension ι ν + 1)) :
    Algebra R (HomogeneousChartRing R j) := homogeneousChartAlgebra j

/-- The original homogeneous coordinate class in the same whole projective quotient. -/
def coordinateClass (j : Fin (pluckerDimension ι ν + 1)) :=
  GradedQuotient.gradedMk (projectiveSpaceGrading R (pluckerDimension ι ν))
    (pluckerIdeal R ι ν).toIdeal (X j)

/-- Its actual degree-one homogeneity in the native original quotient grading. -/
theorem coordinateClass_homogeneous (j : Fin (pluckerDimension ι ν + 1)) :
    coordinateClass R ι ν j ∈
      GradedQuotient.grading (projectiveSpaceGrading R (pluckerDimension ι ν))
        (pluckerIdeal R ι ν).toIdeal 1 :=
  (GradedQuotient.gradedMk (projectiveSpaceGrading R (pluckerDimension ι ν))
    (pluckerIdeal R ι ν).toIdeal).map_mem (MvPolynomial.isHomogeneous_X R j)

/-- The literal native homogeneous product-open ring of two original projective coordinates. -/
abbrev PivotOverlapRing (j k : Fin (pluckerDimension ι ν + 1)) :=
  Away (GradedQuotient.grading (projectiveSpaceGrading R (pluckerDimension ι ν))
    (pluckerIdeal R ι ν).toIdeal) (coordinateClass R ι ν j * coordinateClass R ι ν k)

/-- The actual other-coordinate ratio in the original pivot's native away ring. -/
def nativePivotRatio (j k : Fin (pluckerDimension ι ν + 1)) : PivotAwayRing R ι ν j :=
  Away.mk _ (coordinateClass_homogeneous R ι ν j) 1 (coordinateClass R ι ν k)
    (by simpa using coordinateClass_homogeneous R ι ν k)

/-- The actual native restriction to the literal product open. -/
def pivotOverlapRestriction (j k : Fin (pluckerDimension ι ν + 1)) :
    PivotAwayRing R ι ν j →+* PivotOverlapRing R ι ν j k :=
  awayMap _ (coordinateClass_homogeneous R ι ν k) rfl

/-- The actual other-pivot ratio is a unit on the actual intersection, produced internally. -/
theorem nativePivotRatio_overlap_isUnit (j k : Fin (pluckerDimension ι ν + 1)) :
    IsUnit (pivotOverlapRestriction R ι ν j k (nativePivotRatio R ι ν j k)) :=
  Algebra.PluckerQuot.overlapRatio_isUnit _
    (coordinateClass_homogeneous R ι ν j) (coordinateClass_homogeneous R ι ν k)

/-- The product open is exactly the intersection of the same original projective opens. -/
theorem coordinateOpen_inf_eq_product (j k : Fin (pluckerDimension ι ν + 1)) :
    coordinateOpen R ι ν j ⊓ coordinateOpen R ι ν k =
      Proj.basicOpen
        (GradedQuotient.grading (projectiveSpaceGrading R (pluckerDimension ι ν))
          (pluckerIdeal R ι ν).toIdeal)
        (coordinateClass R ι ν j * coordinateClass R ι ν k) := by
  exact (Proj.basicOpen_mul _ _ _).symm

/-- Native polynomial ratios agree with the literal original quotient homogeneous fractions. -/
theorem pivotRatioHom_coordinate (j k : Fin (pluckerDimension ι ν + 1)) :
    pivotRatioHom R ι ν j (coordinateDehom j (X k)) = nativePivotRatio R ι ν j k := by
  have hr : homogeneousChartRatioHom j (coordinateDehom j (X k :
      MvPolynomial (Fin (pluckerDimension ι ν + 1)) R)) =
      Away.mk (projectiveSpaceGrading R (pluckerDimension ι ν))
        (MvPolynomial.isHomogeneous_X R j) 1 (X k)
        (by simpa using MvPolynomial.isHomogeneous_X R k) := by
    rw [← homogeneousChartDehom_mk j 1 (X k), ← AlgHom.comp_apply,
      homogeneousChartRatioHom_comp_dehom, AlgHom.id_apply]
  change Away.map _ (X j) (homogeneousChartRatioHom j (coordinateDehom j (X k))) = _
  rw [hr, Away.map_mk]
  rfl

end Hironaka.Geometry.QuotGrassmann
