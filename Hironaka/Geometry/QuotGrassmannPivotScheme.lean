import Hironaka.Algebra.PluckerQuotTransitionAlgebra
import Hironaka.Geometry.QuotGrassmannPivotLocalization

/-!
# Actual native scheme isomorphisms for every original injective pivot

The scheme is exactly the previously constructed projective Plücker model.
Every coordinate splitting and both whole-ring inverse maps are constructed
internally. No affine-chart or scheme-isomorphism certificate is supplied.
-/

noncomputable section

open scoped Classical
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

/-- The actual original polynomial algebra and native degree-zero quotient ring are isomorphic. -/
def pivotPolynomialAwayEquiv : MvPolynomial (ι × κ) R ≃+*
    PivotAwayRing R ι ν (pivotIndex (coordinateSelector ι ν) e) :=
  (pivotCoordinateAlgEquiv R (coordinateSelector ι ν) e).toRingEquiv.trans
    (pivotCoordinateAwayEquiv R e)

/-- The whole original coefficient map is preserved by this actual coordinate-ring isomorphism. -/
theorem pivotPolynomialAwayEquiv_C (r : R) :
    pivotPolynomialAwayEquiv R e (C r) = pivotRatioHom R ι ν _ (C r) := by
  change pivotCoordinateAwayEquiv R e
    ((pivotCoordinateAlgEquiv R (coordinateSelector ι ν) e) (C r)) = _
  rw [show (C r : MvPolynomial (ι × κ) R) = algebraMap R _ r from rfl,
    AlgEquiv.commutes]
  exact pivotCoordinateAwayEquiv_mk R e (C r)

/-- The actual original ratio of every selector is the image of its same normalized matrix minor. -/
theorem pivotPolynomialAwayEquiv_minor (t : ι → ι ⊕ ν) :
    pivotPolynomialAwayEquiv R e (columnMinor (pivotUniversalMatrix R e) t) =
      pivotRatioHom R ι ν _ (coordinateDehom (pivotIndex (coordinateSelector ι ν) e)
        (X ((coordinateSelector ι ν).symm t))) := by
  change pivotCoordinateAwayEquiv R e
    (polynomialToPivot R (coordinateSelector ι ν) e (columnMinor (pivotUniversalMatrix R e) t)) = _
  rw [polynomialToPivot_minor, ← pivotCoordinate_eq_minor]
  exact pivotCoordinateAwayEquiv_mk R e _

/-- The entire original affine coordinate map intertwines, including every coefficient. -/
theorem pivotPolynomialAwayEquiv_minorBack
    (F : CoordinateRing R (pivotIndex (coordinateSelector ι ν) e)) :
    pivotPolynomialAwayEquiv R e (minorBack R (coordinateSelector ι ν) e F) =
      pivotRatioHom R ι ν _ F := by
  let β := coordinateSelector ι ν
  have hl := AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp (pivotDehomIdeal R β e)
    (minorBack R β e) (fun _ hF ↦ pivotDehomIdeal_le_ker_minorBack R β e hF)) F
  have hi := AlgHom.congr_fun (polynomialToPivot_comp_pivotToPolynomial R β e)
    (Ideal.Quotient.mkₐ R (pivotDehomIdeal R β e) F)
  change pivotCoordinateAwayEquiv R e
    (polynomialToPivot R β e (minorBack R β e F)) = _
  change pivotToPolynomial R β e (Ideal.Quotient.mkₐ R (pivotDehomIdeal R β e) F) =
    minorBack R β e F at hl
  change polynomialToPivot R β e
    (pivotToPolynomial R β e (Ideal.Quotient.mkₐ R (pivotDehomIdeal R β e) F)) =
      Ideal.Quotient.mkₐ R (pivotDehomIdeal R β e) F at hi
  rw [← hl, hi]
  exact pivotCoordinateAwayEquiv_mk R e F

/-- The whole original coefficient ring triangle for the actual native coordinate isomorphism. -/
theorem pivotPolynomialAwayEquiv_coeffHom :
    (pivotPolynomialAwayEquiv R e).toRingHom.comp
      (algebraMap R (MvPolynomial (ι × κ) R)) =
    (pivotRatioHom R ι ν _).comp
      (algebraMap R (CoordinateRing R (pivotIndex (coordinateSelector ι ν) e))) := by
  ext r : 1
  exact pivotPolynomialAwayEquiv_C R e r

/-- The literal original projective open is the spectrum of the original normalized matrix ring. -/
def pivotMatrixSchemeIso :
    (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e)).toScheme ≅
      Spec (.of (MvPolynomial (ι × κ) R)) :=
  (pivotOpenAwayIso R e).trans
    (Scheme.Spec.mapIso (pivotPolynomialAwayEquiv R e).toCommRingCatIso.op)

/-- The native scheme isomorphism preserves the original coefficient structure morphism. -/
theorem pivotMatrixSchemeIso_structure :
    (pivotMatrixSchemeIso R e).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (ι × κ) R))) =
    (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e)).ι ≫
      projectiveStructure R ι ν := by
  apply (cancel_epi (pivotOpenAwayIso R e).inv).mp
  rw [pivotMatrixSchemeIso, Iso.trans_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [pivotOpenAwayIso_inv_structure]
  change Spec.map (CommRingCat.ofHom (pivotPolynomialAwayEquiv R e).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (ι × κ) R))) = _
  rw [← Spec.map_comp]
  exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) (pivotPolynomialAwayEquiv_coeffHom R e)

variable (ι ν)

/-- The actual unused original columns of an original pivot. -/
abbrev ActualPivotComplement (j : Fin (pluckerDimension ι ν + 1)) :=
  {k : ι ⊕ ν // k ∉ Set.range (coordinateSelector ι ν j)}

/-- An original injective pivot internally supplies its actual original coordinate splitting. -/
def actualPivotSplitting (j : Fin (pluckerDimension ι ν + 1))
    (hj : Function.Injective (coordinateSelector ι ν j)) :
    (ι ⊕ ActualPivotComplement ι ν j) ≃ (ι ⊕ ν) :=
  ((Equiv.ofInjective (coordinateSelector ι ν j) hj).sumCongr (Equiv.refl _)).trans
    (Equiv.sumCompl (fun k ↦ k ∈ Set.range (coordinateSelector ι ν j)))

@[simp]
theorem actualPivotSplitting_inl (j : Fin (pluckerDimension ι ν + 1))
    (hj : Function.Injective (coordinateSelector ι ν j)) (i : ι) :
    actualPivotSplitting ι ν j hj (Sum.inl i) = coordinateSelector ι ν j i := by
  simp [actualPivotSplitting]

@[simp]
theorem actualPivotSplitting_pivotIndex (j : Fin (pluckerDimension ι ν + 1))
    (hj : Function.Injective (coordinateSelector ι ν j)) :
    pivotIndex (coordinateSelector ι ν) (actualPivotSplitting ι ν j hj) = j := by
  apply (coordinateSelector ι ν).injective
  simp only [pivotIndex, Equiv.apply_symm_apply]
  funext i
  exact actualPivotSplitting_inl ι ν j hj i

/-- Every actual injective-pivot open of the same projective model is the original matrix chart. -/
def actualPivotMatrixSchemeIso (j : Fin (pluckerDimension ι ν + 1))
    (hj : Function.Injective (coordinateSelector ι ν j)) :
    (coordinateOpen R ι ν j).toScheme ≅
      Spec (.of (MvPolynomial (ι × ActualPivotComplement ι ν j) R)) := by
  simpa using pivotMatrixSchemeIso R (actualPivotSplitting ι ν j hj)

end Hironaka.Geometry.QuotGrassmann
