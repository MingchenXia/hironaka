import Hironaka.Geometry.QuotGrassmannPivotGlobalPullbackFrame
import Hironaka.Geometry.QuotGrassmannPivotOverSchemeMatrices

/-!
# The SAME original global quotient under its ACTUAL native polynomial-pivot pullback

The exact native naturality triangle identifies the pulled-back original global
map with the native transport of its internally produced original over-site map.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem originalFrameConjugationNaturality {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D) (c : F ≅ G) {S T : C} (q : S ⟶ T)
    {A B : D} (a : F.obj S ≅ A) (b : F.obj T ≅ B) :
    ((c.app S).symm ≪≫ a).inv ≫ G.map q ≫ ((c.app T).symm ≪≫ b).hom =
      a.inv ≫ F.map q ≫ b.hom := by
  have hc : (c.app S).hom ≫ G.map q ≫ (c.app T).inv = F.map q := by
    exact (Category.assoc (c.app S).hom (G.map q) (c.app T).inv).symm.trans
      ((congrArg (fun z => z ≫ (c.app T).inv) (c.hom.naturality q).symm).trans
        ((Category.assoc (F.map q) (c.app T).hom (c.app T).inv).trans
          ((congrArg (fun z => F.map q ≫ z) (c.app T).hom_inv_id).trans
            (Category.comp_id (F.map q)))))
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom]
  calc
    _ = a.inv ≫ ((c.app S).hom ≫ G.map q ≫ (c.app T).inv) ≫ b.hom := by
      simp only [Category.assoc]
    _ = _ := congrArg (fun z => a.inv ≫ z ≫ b.hom) hc

open Algebra.PluckerQuot

variable (R : Type u) [CommRing R] {ι κ ν : Type u}
  [Fintype ι] [Fintype κ] [Fintype ν] [DecidableEq ι] [DecidableEq κ]
  (e : (ι ⊕ κ) ≃ (ι ⊕ ν))

/-- The SAME actual global quotient's true native pullback is the actual transported original over-site quotient. -/
theorem originalGlobalImagePivotFramedQuotient_eq_transport :
    originalGlobalImagePivotFramedQuotient R e =
      originalPullbackFreeHom (pivotMatrixSchemeIso R e).inv
        (originalOverEquivFreeHom (projectiveModel R ι ν)
          (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e))
          ((originalOverFreeIso (projectiveModel R ι ν)
            (coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e)) (ι ⊕ ν)).hom ≫
            originalOverPivotQuotient R ι ν (pivotIndex (coordinateSelector ι ν) e))) := by
  let X := projectiveModel R ι ν
  let U := coordinateOpen R ι ν (pivotIndex (coordinateSelector ι ν) e)
  let H := originalPivotOverPullbackFunctor R e
  let F := SheafOfModules.overFunctor.{u} X.ringCatSheaf U ⋙ H
  let G := Scheme.Modules.pullback (originalPivotModelMorphism R e)
  let c := originalOverCompositePullbackIso U (pivotMatrixSchemeIso R e).inv
  let s := originalOverFreeIso X U (ι ⊕ ν)
  let t := originalGlobalImagePivotFrame R e
  let a := H.mapIso s.symm ≪≫ originalPivotOverPullbackFreeIso R e (ι ⊕ ν)
  let b := H.mapIso t ≪≫ originalPivotOverPullbackFreeIso R e ι
  have hn := originalFrameConjugationNaturality F G c (originalGlobalQuotient R ι ν) a b
  have ho : s.hom ≫
      (SheafOfModules.overFunctor.{u} X.ringCatSheaf U).map (originalGlobalQuotient R ι ν) ≫
        t.hom = s.hom ≫ originalOverPivotQuotient R ι ν (pivotIndex (coordinateSelector ι ν) e) :=
    congrArg (fun z => s.hom ≫ z) (originalGlobalImagePivotFrame_quotient R e)
  have ht := congrArg (fun z => (originalPivotOverPullbackFreeIso R e (ι ⊕ ν)).inv ≫
    H.map z ≫ (originalPivotOverPullbackFreeIso R e ι).hom) ho
  simp only [H.map_comp, Category.assoc] at ht
  calc
    _ = a.inv ≫ F.map (originalGlobalQuotient R ι ν) ≫ b.hom := hn
    _ = (originalPivotOverPullbackFreeIso R e (ι ⊕ ν)).inv ≫
        H.map (s.hom ≫ originalOverPivotQuotient R ι ν (pivotIndex (coordinateSelector ι ν) e)) ≫
          (originalPivotOverPullbackFreeIso R e ι).hom := by
      simp only [a, b, Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
        Iso.symm_inv, H.map_comp, Category.assoc]
      exact ht
    _ = _ := by
      simp only [originalPullbackFreeHom, originalOverEquivFreeHom,
        originalPivotOverPullbackFreeIso, Iso.trans_inv, Iso.trans_hom,
        Functor.mapIso_inv, Functor.mapIso_hom, Iso.symm_inv, Iso.symm_hom,
        Functor.map_comp, Category.assoc]
      rfl

end Hironaka.Geometry.QuotGrassmann
