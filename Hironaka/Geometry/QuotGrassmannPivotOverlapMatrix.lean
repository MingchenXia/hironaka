import Hironaka.Geometry.QuotGrassmannPivotOverlapRatio
import Hironaka.Algebra.PluckerQuotTransitionOverlap

/-!
# Actual pivot matrices and produced unit determinants on actual intersections

The unit determinant is derived from the native restriction map of the same
original projective model. It is not supplied as an overlap-chart hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuot Algebra.ModuleFlatteningMinors ProjectiveIdeal

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] {ι κ ν : Type u}
  [Fintype ι] [Fintype κ] [Fintype ν] [DecidableEq ι] [DecidableEq κ]
  (e : (ι ⊕ κ) ≃ (ι ⊕ ν))

/-- Actual restriction of the original normalized matrix polynomial coordinates to the overlap. -/
def pivotOverlapPolynomialMap (k : Fin (pluckerDimension ι ν + 1)) :
    MvPolynomial (ι × κ) R →+*
      PivotOverlapRing R ι ν (pivotIndex (coordinateSelector ι ν) e) k :=
  (pivotOverlapRestriction R ι ν _ k).comp (pivotPolynomialAwayEquiv R e).toRingHom

/-- The same original normalized universal matrix, restricted to the actual projective overlap. -/
def pivotOverlapMatrix (k : Fin (pluckerDimension ι ν + 1)) :=
  (pivotUniversalMatrix R e).map (pivotOverlapPolynomialMap R e k)

/-- Every selected determinant commutes with the original whole coefficient restriction map. -/
theorem pivotOverlapMatrix_minor (k : Fin (pluckerDimension ι ν + 1)) (t : ι → ι ⊕ ν) :
    columnMinor (pivotOverlapMatrix R e k) t =
      pivotOverlapRestriction R ι ν _ k
        (nativePivotRatio R ι ν _ ((coordinateSelector ι ν).symm t)) := by
  let φ := pivotOverlapPolynomialMap R e k
  have hm : φ.mapMatrix (selectedMatrix (pivotUniversalMatrix R e) t) =
      selectedMatrix (pivotOverlapMatrix R e k) t := by
    ext i j
    rfl
  have hd := (φ.map_det (selectedMatrix (pivotUniversalMatrix R e) t)).trans
    (congrArg Matrix.det hm)
  rw [columnMinor, ← hd]
  change pivotOverlapRestriction R ι ν _ k
    (pivotPolynomialAwayEquiv R e (columnMinor (pivotUniversalMatrix R e) t)) = _
  rw [pivotPolynomialAwayEquiv_minor, pivotRatioHom_coordinate]

/-- On the actual intersection the actual selected second-pivot determinant is a produced unit. -/
theorem pivotOverlapMatrix_pivot_isUnit (k : Fin (pluckerDimension ι ν + 1)) :
    IsUnit (columnMinor (pivotOverlapMatrix R e k) (coordinateSelector ι ν k)) := by
  rw [pivotOverlapMatrix_minor, Equiv.symm_apply_apply]
  exact nativePivotRatio_overlap_isUnit R ι ν _ k

/-- The actual matrix can be normalized on the other original pivot without a unit hypothesis. -/
theorem pivotOverlapMatrix_normalize_selected (k : Fin (pluckerDimension ι ν + 1)) :
    selectedMatrix (pivotNormalize (pivotOverlapMatrix R e k) (coordinateSelector ι ν k))
      (coordinateSelector ι ν k) = 1 :=
  selectedMatrix_pivotNormalize _ _ (pivotOverlapMatrix_pivot_isUnit R e k)

end Hironaka.Geometry.QuotGrassmann
