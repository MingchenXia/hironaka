import Hironaka.Geometry.QuotGrassmannPivotOverScalars

/-!
# The ORIGINAL polynomial pivot and its entire native section-ring triangle

The morphism and all coefficient maps are precisely the originally constructed
whole-ring pivot isomorphism and the original open inclusion into the SAME G.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuot ProjectiveIdeal

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem originalSectionRingInverseTriangle {C : Type*} [Category C]
    {A B D E : C} (i : A ≅ B) (t : D ≅ E) (s : A ⟶ D) (r : D ⟶ A)
    (p : B ⟶ E) (h : s ≫ t.hom = i.hom ≫ p) (hs : s ≫ r = 𝟙 A) :
    p ≫ t.inv ≫ r = i.inv := by
  apply (cancel_epi i.hom).mp
  calc
    i.hom ≫ (p ≫ t.inv ≫ r) = (i.hom ≫ p) ≫ t.inv ≫ r := by
      simp only [Category.assoc]
    _ = (s ≫ t.hom) ≫ t.inv ≫ r :=
      congrArg (fun z => z ≫ t.inv ≫ r) h.symm
    _ = s ≫ r := by simp only [Category.assoc, t.hom_inv_id_assoc]
    _ = 𝟙 A := hs
    _ = i.hom ≫ i.inv := i.hom_inv_id.symm

variable (R : Type u) [CommRing R] {ι κ ν : Type u}
  [Fintype ι] [Fintype κ] [Fintype ν] [DecidableEq ι] [DecidableEq κ]
  (e : (ι ⊕ κ) ≃ (ι ⊕ ν))

/-- The ORIGINAL polynomial-pivot map, with its ORIGINAL source and SAME target G. -/
def originalPivotModelMorphism : affineChart R ι κ ⟶ projectiveModel R ι ν :=
  (pivotMatrixSchemeIso R e).inv ≫
    (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e)).ι

/-- This actual original morphism is an open immersion internally. -/
instance originalPivotModelMorphism_isOpenImmersion :
    IsOpenImmersion (originalPivotModelMorphism R e) := by
  unfold originalPivotModelMorphism
  infer_instance

/-- The SAME actual original pivot morphism retains its original coefficient structure triangle. -/
theorem originalPivotModelMorphism_structure :
    originalPivotModelMorphism R e ≫ projectiveStructure R ι ν =
      Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing R ι κ))) := by
  let a := pivotMatrixSchemeIso R e
  let v := (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e)).ι
  let f := Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing R ι κ)))
  exact (Category.assoc a.inv v (projectiveStructure R ι ν)).trans
    ((congrArg (fun z => a.inv ≫ z) (pivotMatrixSchemeIso_structure R e).symm).trans
      (a.inv_hom_id_assoc f))

/-- The ORIGINAL scheme isomorphism has exactly the SAME entire original polynomial section map. -/
theorem originalPivotMatrixSchemeIso_appTop :
    (pivotMatrixSchemeIso R e).hom.appTop ≫
      (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e)).topIso.hom =
    (Scheme.ΓSpecIso (.of (ChartRing R ι κ))).hom ≫
      CommRingCat.ofHom (originalOverPivotScalarMap R e) := by
  let U := coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e)
  let A := PivotAwayRing R ι ν (pivotIndex (coordinateSelector ι ν) e)
  let a := pivotOpenAwayIso R e
  let c := Scheme.Spec.mapIso (pivotPolynomialAwayEquiv R e).toCommRingCatIso.op
  have ha : a.hom.appTop ≫ U.topIso.hom =
      (Scheme.ΓSpecIso (.of A)).hom ≫
        Proj.awayToSection
          (GradedQuotient.grading (projectiveSpaceGrading R (pluckerDimension ι ν))
            (pluckerIdeal R ι ν).toIdeal)
          (coordinateClass R ι ν (pivotIndex (coordinateSelector ι ν) e)) := by
    rw [show a.hom.appTop = (Proj.basicOpenToSpec
      (GradedQuotient.grading (projectiveSpaceGrading R (pluckerDimension ι ν))
        (pluckerIdeal R ι ν).toIdeal)
      (coordinateClass R ι ν (pivotIndex (coordinateSelector ι ν) e))).app ⊤ from rfl]
    rw [Proj.basicOpenToSpec_app_top]
    let V := Proj.basicOpen
      (GradedQuotient.grading (projectiveSpaceGrading R (pluckerDimension ι ν))
        (pluckerIdeal R ι ν).toIdeal)
      (coordinateClass R ι ν (pivotIndex (coordinateSelector ι ν) e))
    have hcancel : V.topIso.inv ≫ U.topIso.hom = 𝟙 _ := V.topIso.inv_hom_id
    let t := Proj.awayToSection
      (GradedQuotient.grading (projectiveSpaceGrading R (pluckerDimension ι ν))
        (pluckerIdeal R ι ν).toIdeal)
      (coordinateClass R ι ν (pivotIndex (coordinateSelector ι ν) e))
    simp only [Category.assoc]
    exact (congrArg (fun z => (Scheme.ΓSpecIso (.of A)).hom ≫ t ≫ z) hcancel).trans
      (congrArg (fun z => (Scheme.ΓSpecIso (.of A)).hom ≫ z) (Category.comp_id t))
  have hc : c.hom.appTop ≫ (Scheme.ΓSpecIso (.of A)).hom =
      (Scheme.ΓSpecIso (.of (ChartRing R ι κ))).hom ≫
        CommRingCat.ofHom (pivotPolynomialAwayEquiv R e).toRingHom :=
    Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (pivotPolynomialAwayEquiv R e).toRingHom)
  change (a.hom ≫ c.hom).appTop ≫ U.topIso.hom = _
  rw [Scheme.Hom.comp_appTop, Category.assoc, ha, ← Category.assoc, hc]
  rfl

/-- The SAME entire original polynomial section map has the exact original inverse transport triangle. -/
theorem originalPivotMatrixSchemeIso_sectionTriangle :
    CommRingCat.ofHom (originalOverPivotScalarMap R e) ≫
      (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e)).topIso.inv ≫
        (pivotMatrixSchemeIso R e).inv.appTop =
      (Scheme.ΓSpecIso (.of (ChartRing R ι κ))).inv := by
  let a := pivotMatrixSchemeIso R e
  have ha : a.hom.appTop ≫ a.inv.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, a.inv_hom_id]
    simp only [Scheme.Hom.id_appTop]
  exact originalSectionRingInverseTriangle
    (Scheme.ΓSpecIso (.of (ChartRing R ι κ)))
    (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e)).topIso
    a.hom.appTop a.inv.appTop (CommRingCat.ofHom (originalOverPivotScalarMap R e))
    (originalPivotMatrixSchemeIso_appTop R e) ha

end Hironaka.Geometry.QuotGrassmann
