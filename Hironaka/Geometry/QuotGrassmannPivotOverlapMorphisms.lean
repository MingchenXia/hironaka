import Hironaka.Geometry.QuotGrassmannPivotOverlapChange

/-!
# Actual native overlap coefficient maps are open immersions

Both maps use the original whole-ring chart equivalences and the native
localization maps to the same actual homogeneous product-open ring.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuot ProjectiveIdeal

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] {ι κ τ ν : Type u}
  [Fintype ι] [Fintype κ] [Fintype τ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq τ]
  (e : (ι ⊕ κ) ≃ (ι ⊕ ν)) (f : (ι ⊕ τ) ≃ (ι ⊕ ν))

/-- The first original coefficient map on the same actual native overlap. -/
def originalOverlapLeftMorphism :
    Spec (.of (PivotOverlapRing R ι ν (pivotIndex (coordinateSelector ι ν) e)
      (pivotIndex (coordinateSelector ι ν) f))) ⟶ Spec (.of (MvPolynomial (ι × κ) R)) :=
  Spec.map (CommRingCat.ofHom (pivotOverlapPolynomialMap R e (pivotIndex (coordinateSelector ι ν) f)))

/-- The second original coefficient map on that very same actual native overlap. -/
def originalOverlapRightMorphism :
    Spec (.of (PivotOverlapRing R ι ν (pivotIndex (coordinateSelector ι ν) e)
      (pivotIndex (coordinateSelector ι ν) f))) ⟶ Spec (.of (MvPolynomial (ι × τ) R)) :=
  Spec.map (CommRingCat.ofHom (pivotOverlapRightPolynomialMap R e f))

/-- The actual first native overlap coefficient morphism is an open immersion, constructed internally. -/
instance originalOverlapLeftMorphism_isOpenImmersion :
    IsOpenImmersion (originalOverlapLeftMorphism R e f) := by
  let j := pivotIndex (coordinateSelector ι ν) e
  let k := pivotIndex (coordinateSelector ι ν) f
  let φ := pivotOverlapRestriction R ι ν j k
  let := φ.toAlgebra
  let : IsLocalization.Away (nativePivotRatio R ι ν j k) (PivotOverlapRing R ι ν j k) := by
    simpa only [Away.isLocalizationElem, pow_one, nativePivotRatio] using
      Away.isLocalization_mul (coordinateClass_homogeneous R ι ν j)
        (coordinateClass_homogeneous R ι ν k) rfl (by decide : (1 : ℕ) ≠ 0)
  have hφ : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) :=
    IsOpenImmersion.of_isLocalization (nativePivotRatio R ι ν j k)
  change IsOpenImmersion (Spec.map ((pivotPolynomialAwayEquiv R e).toCommRingCatIso.hom ≫
    CommRingCat.ofHom φ))
  rw [Spec.map_comp]
  infer_instance

/-- The actual second native overlap coefficient morphism is an open immersion, constructed internally. -/
instance originalOverlapRightMorphism_isOpenImmersion :
    IsOpenImmersion (originalOverlapRightMorphism R e f) := by
  let j := pivotIndex (coordinateSelector ι ν) e
  let k := pivotIndex (coordinateSelector ι ν) f
  let φ := pivotOverlapRightRestriction R ι ν j k
  let := φ.toAlgebra
  let : IsLocalization.Away (nativePivotRatio R ι ν k j) (PivotOverlapRing R ι ν j k) := by
    simpa only [Away.isLocalizationElem, pow_one, nativePivotRatio] using
      Away.isLocalization_mul (coordinateClass_homogeneous R ι ν k)
        (coordinateClass_homogeneous R ι ν j) (mul_comm _ _) (by decide : (1 : ℕ) ≠ 0)
  have hφ : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) :=
    IsOpenImmersion.of_isLocalization (nativePivotRatio R ι ν k j)
  change IsOpenImmersion (Spec.map ((pivotPolynomialAwayEquiv R f).toCommRingCatIso.hom ≫
    CommRingCat.ofHom φ))
  rw [Spec.map_comp]
  infer_instance

/-- The same actual original homogeneous product-open map into the same projective model. -/
def originalOverlapModelMorphism :
    Spec (.of (PivotOverlapRing R ι ν (pivotIndex (coordinateSelector ι ν) e)
      (pivotIndex (coordinateSelector ι ν) f))) ⟶ projectiveModel R ι ν :=
  Proj.awayι
    (GradedQuotient.grading (projectiveSpaceGrading R (pluckerDimension ι ν))
      (pluckerIdeal R ι ν).toIdeal)
    (coordinateClass R ι ν (pivotIndex (coordinateSelector ι ν) e) *
      coordinateClass R ι ν (pivotIndex (coordinateSelector ι ν) f))
    (SetLike.mul_mem_graded (coordinateClass_homogeneous R ι ν _)
      (coordinateClass_homogeneous R ι ν _)) (by decide : 0 < (2 : ℕ))

omit [Fintype τ] [DecidableEq τ] in
set_option maxHeartbeats 1500000 in
/-- The original first coefficient map and original matrix chart commute with the same native overlap. -/
theorem originalOverlapLeftMorphism_triangle :
    originalOverlapLeftMorphism R e f ≫ (pivotMatrixSchemeIso R e).inv ≫
      (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e)).ι =
    originalOverlapModelMorphism R e f := by
  let j := pivotIndex (coordinateSelector ι ν) e
  let k := pivotIndex (coordinateSelector ι ν) f
  let c := (Scheme.Spec.mapIso (pivotPolynomialAwayEquiv R e).toCommRingCatIso.op)
  have hmap : originalOverlapLeftMorphism R e f =
      Spec.map (CommRingCat.ofHom (pivotOverlapRestriction R ι ν j k)) ≫ c.hom := by
    change Spec.map ((pivotPolynomialAwayEquiv R e).toCommRingCatIso.hom ≫
      CommRingCat.ofHom (pivotOverlapRestriction R ι ν j k)) =
        Spec.map (CommRingCat.ofHom (pivotOverlapRestriction R ι ν j k)) ≫
          Spec.map (pivotPolynomialAwayEquiv R e).toCommRingCatIso.hom
    exact Spec.map_comp _ _
  rw [hmap]
  change (Spec.map (CommRingCat.ofHom (pivotOverlapRestriction R ι ν j k)) ≫ c.hom) ≫
    (c.inv ≫ (pivotOpenAwayIso R e).inv) ≫ (coordinateOpen R ι ν j).ι = _
  simp only [Category.assoc, c.hom_inv_id_assoc]
  change Spec.map (CommRingCat.ofHom (pivotOverlapRestriction R ι ν j k)) ≫
    Proj.awayι _ (coordinateClass R ι ν j) (coordinateClass_homogeneous R ι ν j)
      (by decide : 0 < (1 : ℕ)) = _
  exact Proj.SpecMap_awayMap_awayι _ (coordinateClass_homogeneous R ι ν j)
    (by decide : 0 < (1 : ℕ)) (coordinateClass_homogeneous R ι ν k) rfl

omit [Fintype κ] [DecidableEq κ] in
set_option maxHeartbeats 1500000 in
/-- The original second coefficient map and original matrix chart commute with that same native overlap. -/
theorem originalOverlapRightMorphism_triangle :
    originalOverlapRightMorphism R e f ≫ (pivotMatrixSchemeIso R f).inv ≫
      (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) f)).ι =
    originalOverlapModelMorphism R e f := by
  let j := pivotIndex (coordinateSelector ι ν) e
  let k := pivotIndex (coordinateSelector ι ν) f
  let c := (Scheme.Spec.mapIso (pivotPolynomialAwayEquiv R f).toCommRingCatIso.op)
  have hmap : originalOverlapRightMorphism R e f =
      Spec.map (CommRingCat.ofHom (pivotOverlapRightRestriction R ι ν j k)) ≫ c.hom := by
    change Spec.map ((pivotPolynomialAwayEquiv R f).toCommRingCatIso.hom ≫
      CommRingCat.ofHom (pivotOverlapRightRestriction R ι ν j k)) =
        Spec.map (CommRingCat.ofHom (pivotOverlapRightRestriction R ι ν j k)) ≫
          Spec.map (pivotPolynomialAwayEquiv R f).toCommRingCatIso.hom
    exact Spec.map_comp _ _
  rw [hmap]
  change (Spec.map (CommRingCat.ofHom (pivotOverlapRightRestriction R ι ν j k)) ≫ c.hom) ≫
    (c.inv ≫ (pivotOpenAwayIso R f).inv) ≫ (coordinateOpen R ι ν k).ι = _
  simp only [Category.assoc, c.hom_inv_id_assoc]
  change Spec.map (CommRingCat.ofHom (pivotOverlapRightRestriction R ι ν j k)) ≫
    Proj.awayι _ (coordinateClass R ι ν k) (coordinateClass_homogeneous R ι ν k)
      (by decide : 0 < (1 : ℕ)) = _
  exact Proj.SpecMap_awayMap_awayι _ (coordinateClass_homogeneous R ι ν k)
    (by decide : 0 < (1 : ℕ)) (coordinateClass_homogeneous R ι ν j) (mul_comm _ _)

end Hironaka.Geometry.QuotGrassmann
