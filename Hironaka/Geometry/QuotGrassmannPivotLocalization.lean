import Hironaka.Algebra.PluckerQuotTransitionCoordinates
import Hironaka.Geometry.QuotGrassmannProjective

/-!
# The whole original pivot algebra is the native degree-zero quotient localization

The source is exactly the originally constructed closed projective Plücker model.
The kernel computation retains the whole homogeneous ideal, including nilpotents.
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

/-- The native degree-zero away ring of the same originally constructed projective model. -/
abbrev PivotAwayRing (j : Fin (pluckerDimension ι ν + 1)) :=
  Away (GradedQuotient.grading (projectiveSpaceGrading R (pluckerDimension ι ν))
    (pluckerIdeal R ι ν).toIdeal)
    (GradedQuotient.gradedMk (projectiveSpaceGrading R (pluckerDimension ι ν))
      (pluckerIdeal R ι ν).toIdeal (X j))

private local instance chartAlgebra (j : Fin (pluckerDimension ι ν + 1)) :
    Algebra R (HomogeneousChartRing R j) := homogeneousChartAlgebra j

/-- The actual original coordinate ratios followed by the actual graded quotient away map. -/
def pivotRatioHom (j : Fin (pluckerDimension ι ν + 1)) :
    CoordinateRing R j →+* PivotAwayRing R ι ν j :=
  (Away.map (GradedQuotient.gradedMk (projectiveSpaceGrading R (pluckerDimension ι ν))
    (pluckerIdeal R ι ν).toIdeal) (X j)).comp (homogeneousChartRatioHom j).toRingHom

/-- The actual map from the whole original polynomial chart is surjective. -/
theorem pivotRatioHom_surjective (j : Fin (pluckerDimension ι ν + 1)) :
    Function.Surjective (pivotRatioHom R ι ν j) := by
  exact (GradedQuotient.awayMap_surjective
    (projectiveSpaceGrading R (pluckerDimension ι ν)) (pluckerIdeal R ι ν)
    (MvPolynomial.isHomogeneous_X R j)).comp (homogeneousChartEquiv (R := R) j).symm.surjective

variable {ι ν} {κ : Type u} [Fintype κ] [DecidableEq κ]
  (e : (ι ⊕ κ) ≃ (ι ⊕ ν))

omit [Fintype κ] [DecidableEq κ] in
/-- The exact kernel is the whole original dehomogenized minor-relation ideal. -/
theorem pivotRatioHom_ker :
    RingHom.ker (pivotRatioHom R ι ν (pivotIndex (coordinateSelector ι ν) e)) =
      pivotDehomIdeal R (coordinateSelector ι ν) e :=
  homogeneousQuotient_coordinateKernel (pluckerIdeal R ι ν) _

/-- An actual isomorphism of the whole original pivot quotient with the native away ring. -/
def pivotCoordinateAwayEquiv : PivotCoordinateRing R (coordinateSelector ι ν) e ≃+*
    PivotAwayRing R ι ν (pivotIndex (coordinateSelector ι ν) e) :=
  (Ideal.quotEquivOfEq (pivotRatioHom_ker R e).symm).trans
    ((pivotRatioHom R ι ν _).quotientKerEquivOfSurjective (pivotRatioHom_surjective R ι ν _))

omit [Fintype κ] [DecidableEq κ] in
/-- The isomorphism is the actual quotient lift of the original whole coordinate map. -/
theorem pivotCoordinateAwayEquiv_mk (F : CoordinateRing R
    (pivotIndex (coordinateSelector ι ν) e)) :
    pivotCoordinateAwayEquiv R e (Ideal.Quotient.mk _ F) = pivotRatioHom R ι ν _ F := by
  simp [pivotCoordinateAwayEquiv, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- The same actual coordinate open has its native basic-open spectrum isomorphism. -/
def pivotOpenAwayIso :
    (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e)).toScheme ≅
      Spec (.of (PivotAwayRing R ι ν (pivotIndex (coordinateSelector ι ν) e))) :=
  Proj.basicOpenIsoSpec
    (GradedQuotient.grading (projectiveSpaceGrading R (pluckerDimension ι ν))
      (pluckerIdeal R ι ν).toIdeal)
    (GradedQuotient.gradedMk (projectiveSpaceGrading R (pluckerDimension ι ν))
      (pluckerIdeal R ι ν).toIdeal (X (pivotIndex (coordinateSelector ι ν) e)))
    ((GradedQuotient.gradedMk (projectiveSpaceGrading R (pluckerDimension ι ν))
      (pluckerIdeal R ι ν).toIdeal).map_mem
      (MvPolynomial.isHomogeneous_X R _)) (by decide : 0 < (1 : ℕ))

omit [Fintype κ] [DecidableEq κ] in
set_option maxHeartbeats 2000000 in
/-- The native original coefficient morphism commutes with the actual original pivot chart. -/
theorem pivotOpenAwayIso_inv_structure :
    (pivotOpenAwayIso R e).inv ≫
      (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e)).ι ≫
      projectiveStructure R ι ν =
    Spec.map (CommRingCat.ofHom ((pivotRatioHom R ι ν _).comp
      (algebraMap R (CoordinateRing R (pivotIndex (coordinateSelector ι ν) e))))) := by
  let j := pivotIndex (coordinateSelector ι ν) e
  let G := projectiveSpaceGrading R (pluckerDimension ι ν)
  let q := GradedQuotient.gradedMk G (pluckerIdeal R ι ν).toIdeal
  rw [← Category.assoc]
  change Proj.awayι (GradedQuotient.grading G (pluckerIdeal R ι ν).toIdeal)
      (q (X j)) (q.map_mem (MvPolynomial.isHomogeneous_X R j)) (by decide : 0 < (1 : ℕ)) ≫
      (Proj.map q (GradedQuotient.irrelevant_le_map G (pluckerIdeal R ι ν)) ≫
        (Proj.toSpecZero G ≫ Spec.map (projectiveSpaceDegreeZeroEquiv R _).toCommRingCatIso.hom)) = _
  rw [← Category.assoc,
    Proj.awayι_comp_map q (GradedQuotient.irrelevant_le_map G (pluckerIdeal R ι ν))
      (by decide : 0 < (1 : ℕ)) (X j) (MvPolynomial.isHomogeneous_X R j)]
  simp only [Category.assoc]
  rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext r : 1
  change Away.map q (X j)
    (HomogeneousLocalization.fromZeroRingHom G _ (projectiveSpaceConstants R _ r)) =
      Away.map q (X j) (homogeneousChartRatioHom j (algebraMap R (CoordinateRing R j) r))
  rw [AlgHom.commutes]
  rfl

end Hironaka.Geometry.QuotGrassmann
