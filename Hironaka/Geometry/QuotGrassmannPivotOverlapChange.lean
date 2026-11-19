import Hironaka.Geometry.QuotGrassmannPivotOverlapMatrix
import Hironaka.Algebra.PluckerQuotTransitionCramer

/-!
# Both original normalized quotient matrices on the same actual intersection

The two actual native restriction maps land in the same original product-open
ring. Native original fractions and exact Cramer entries identify the two
original normalized universal matrices by their actual inverse basis change.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuot Algebra.ModuleFlatteningMinors ProjectiveIdeal

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] (ι ν : Type u)
  [Fintype ι] [Fintype ν] [DecidableEq ι]

/-- The actual second-pivot restriction lands in the same literal product-open ring. -/
def pivotOverlapRightRestriction (j k : Fin (pluckerDimension ι ν + 1)) :
    PivotAwayRing R ι ν k →+* PivotOverlapRing R ι ν j k :=
  awayMap _ (coordinateClass_homogeneous R ι ν j) (mul_comm _ _)

/-- The exact original coordinate fractions commute with changing the original pivot denominator. -/
theorem nativePivotRatio_change_denominator (j k l : Fin (pluckerDimension ι ν + 1)) :
    pivotOverlapRestriction R ι ν j k (nativePivotRatio R ι ν j k) *
      pivotOverlapRightRestriction R ι ν j k (nativePivotRatio R ι ν k l) =
    pivotOverlapRestriction R ι ν j k (nativePivotRatio R ι ν j l) :=
  overlapRatio_change_denominator _ (coordinateClass_homogeneous R ι ν j)
    (coordinateClass_homogeneous R ι ν k) (coordinateClass_homogeneous R ι ν l)

variable {ι ν} {κ τ : Type u} [Fintype κ] [Fintype τ] [DecidableEq κ] [DecidableEq τ]
  (e : (ι ⊕ κ) ≃ (ι ⊕ ν)) (f : (ι ⊕ τ) ≃ (ι ⊕ ν))

/-- The second original coefficient map restricted to the same actual intersection. -/
def pivotOverlapRightPolynomialMap : MvPolynomial (ι × τ) R →+*
    PivotOverlapRing R ι ν (pivotIndex (coordinateSelector ι ν) e)
      (pivotIndex (coordinateSelector ι ν) f) :=
  (pivotOverlapRightRestriction R ι ν _ _).comp (pivotPolynomialAwayEquiv R f).toRingHom

/-- The second original normalized universal matrix, restricted along its actual coefficient map. -/
def pivotOverlapRightMatrix :=
  (pivotUniversalMatrix R f).map (pivotOverlapRightPolynomialMap R e f)

omit [Fintype κ] [DecidableEq κ] in
/-- Every original free column entry of the second quotient is its exact original replacement ratio. -/
theorem pivotOverlapRightMatrix_entry (i : ι) (a : ι ⊕ ν) :
    pivotOverlapRightMatrix R e f i a =
      pivotOverlapRightRestriction R ι ν _ _ (nativePivotRatio R ι ν _
        ((coordinateSelector ι ν).symm (Function.update (f ∘ Sum.inl) i a))) := by
  change pivotOverlapRightPolynomialMap R e f (pivotUniversalMatrix R f i a) = _
  calc
    _ = pivotOverlapRightPolynomialMap R e f (columnMinor (pivotUniversalMatrix R f)
        (Function.update (f ∘ Sum.inl) i a)) :=
      congrArg (pivotOverlapRightPolynomialMap R e f)
        (columnMinor_splitNormalized_replacement_any f
          (fun i j ↦ (X (i, j) : MvPolynomial (ι × τ) R)) i a).symm
    _ = _ := by
      change pivotOverlapRightRestriction R ι ν _ _
        (pivotPolynomialAwayEquiv R f (columnMinor (pivotUniversalMatrix R f)
          (Function.update (f ∘ Sum.inl) i a))) = _
      rw [pivotPolynomialAwayEquiv_minor, pivotRatioHom_coordinate]

/-- Both original normalized matrices on the same actual native intersection agree by the
actual inverse pivot basis change, with its unit determinant produced internally. -/
theorem pivotOverlap_normalize_eq_right :
    pivotNormalize (pivotOverlapMatrix R e (pivotIndex (coordinateSelector ι ν) f))
      (f ∘ Sum.inl) = pivotOverlapRightMatrix R e f := by
  let β := coordinateSelector ι ν
  let L := pivotOverlapMatrix R e (pivotIndex β f)
  have hu : IsUnit (columnMinor L (f ∘ Sum.inl)) := by
    have hs : coordinateSelector ι ν (pivotIndex β f) = f ∘ Sum.inl := β.apply_symm_apply _
    rw [← hs]
    exact pivotOverlapMatrix_pivot_isUnit R e (pivotIndex β f)
  apply Matrix.ext
  intro i a
  have hleft := pivotNormalize_entry_mul_det L (f ∘ Sum.inl) hu i a
  have hright : columnMinor L (f ∘ Sum.inl) * pivotOverlapRightMatrix R e f i a =
      columnMinor L (Function.update (f ∘ Sum.inl) i a) := by
    rw [show columnMinor L (f ∘ Sum.inl) =
      pivotOverlapRestriction R ι ν _ _ (nativePivotRatio R ι ν _ (pivotIndex β f)) from
        pivotOverlapMatrix_minor R e (pivotIndex β f) (f ∘ Sum.inl)]
    rw [pivotOverlapRightMatrix_entry, nativePivotRatio_change_denominator]
    exact (pivotOverlapMatrix_minor R e (pivotIndex β f) _).symm
  exact hu.mul_left_cancel (hleft.trans hright.symm)

end Hironaka.Geometry.QuotGrassmann
