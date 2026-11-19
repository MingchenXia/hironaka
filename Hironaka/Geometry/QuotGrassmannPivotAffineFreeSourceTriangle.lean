import Hironaka.Geometry.QuotGrassmannPivotAffineFreeScalarTriangle
import Hironaka.Geometry.QuotGrassmannPivotPullbackFreeComposition
import Hironaka.Geometry.QuotGrassmannPivotAffineCompositeSections

/-!
# ORIGINAL native finite source coordinates under actual affine composition

The whole finite-coordinate triangle follows from the actual scalar coordinate
formula, naturality on the ORIGINAL inverse free frame, and the internally
proved native free-frame composition. No frame compatibility is an input.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem originalScalarSourceDiagram {C : Type*} [Category C]
    {X Y Z V W T U K : C}
    (a : X ⟶ Y) (b : Y ⟶ Z) (d : Z ⟶ V) (e : V ⟶ U)
    (n : Y ⟶ W) (p : W ⟶ V) (v : W ≅ T)
    (s : X ⟶ K) (c : K ⟶ T) (k : T ⟶ U)
    (hn : b ≫ d = n ≫ p) (hs : a ≫ n ≫ v.hom = s ≫ c)
    (hk : v.inv ≫ p ≫ e = k) :
    a ≫ b ≫ d ≫ e = s ≫ c ≫ k := by
  calc
    _ = a ≫ (b ≫ d) ≫ e := by simp only [Category.assoc]
    _ = a ≫ (n ≫ p) ≫ e := congrArg (fun q => a ≫ q ≫ e) hn
    _ = (a ≫ n ≫ v.hom) ≫ (v.inv ≫ p ≫ e) := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = (s ≫ c) ≫ k := by rw [hs, hk]
    _ = _ := by simp only [Category.assoc]

/-- The ORIGINAL inverse free frames satisfy WHOLE actual native composition, on the same sheaves and scheme morphisms. -/
theorem originalPullbackFreeIso_comp_inverse {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (I : Type u) :
    (originalPullbackFreeIso f I).inv ≫
      (pullback f).map (originalPullbackFreeIso g I).inv ≫
        ((pullbackComp f g).app (SheafOfModules.free (R := Z.ringCatSheaf) I)).hom =
      (originalPullbackFreeIso (f ≫ g) I).inv := by
  have h : ((pullbackComp f g).app
      (SheafOfModules.free (R := Z.ringCatSheaf) I)).symm ≪≫
        (pullback f).mapIso (originalPullbackFreeIso g I) ≪≫
          originalPullbackFreeIso f I = originalPullbackFreeIso (f ≫ g) I := by
    apply Iso.ext
    exact originalPullbackFreeIso_comp_inv f g I
  exact congrArg Iso.inv h

/-- ALL original affine source coordinates commute with actual native scalar extension and SAME native pullback composition, as WHOLE maps. -/
theorem originalCompositeSpecFreeSourceScalarTriangle
    {A B : CommRingCat.{u}} (φ : A ⟶ B) {X : Scheme.{u}}
    (f : Spec A ⟶ X) (I : Type u) [Finite I] :
    (ModuleCat.extendScalars φ.hom).map
        ((originalAffineFreeSectionsCoordinateIso A I).hom ≫
          moduleSpecΓFunctor.map (originalPullbackFreeIso f I).inv) ≫
      (originalCompositeSpecPullbackSectionsNatTrans φ f).app
        (SheafOfModules.free (R := X.ringCatSheaf) I) =
    (originalAffineFreeScalarCoordinateIso φ I).hom ≫
      (originalAffineFreeSectionsCoordinateIso B I).hom ≫
        moduleSpecΓFunctor.map (originalPullbackFreeIso (Spec.map φ ≫ f) I).inv := by
  let S := SheafOfModules.free (R := X.ringCatSheaf) I
  let : ((pullback f).obj S).IsLocallyFree := originalSchemePullback_isLocallyFree f S
  let F := pullback (Spec.map φ)
  let E := ModuleCat.extendScalars φ.hom
  let v := moduleSpecΓFunctor.mapIso (originalPullbackFreeIso (Spec.map φ) I)
  have hn := originalSpecPullbackSectionsIso_naturality φ
    (originalPullbackFreeIso f I).inv
  have hs := originalAffineFreeSectionScalarMap_eq_coordinate φ I
  have hk : v.inv ≫ moduleSpecΓFunctor.map (F.map (originalPullbackFreeIso f I).inv) ≫
      moduleSpecΓFunctor.map ((pullbackComp (Spec.map φ) f).app S).hom =
      moduleSpecΓFunctor.map (originalPullbackFreeIso (Spec.map φ ≫ f) I).inv := by
    have h := congrArg moduleSpecΓFunctor.map
      (originalPullbackFreeIso_comp_inverse (Spec.map φ) f I)
    simp only [Functor.map_comp] at h
    exact h
  have h := originalScalarSourceDiagram
    (E.map (originalAffineFreeSectionsCoordinateIso A I).hom)
    (E.map (moduleSpecΓFunctor.map (originalPullbackFreeIso f I).inv))
    (originalSpecPullbackSectionsIso φ ((pullback f).obj S)).hom
    (moduleSpecΓFunctor.map ((pullbackComp (Spec.map φ) f).app S).hom)
    (originalSpecPullbackSectionsIso φ
      (SheafOfModules.free (R := (Spec A).ringCatSheaf) I)).hom
    (moduleSpecΓFunctor.map (F.map (originalPullbackFreeIso f I).inv)) v
    (originalAffineFreeScalarCoordinateIso φ I).hom
    (originalAffineFreeSectionsCoordinateIso B I).hom
    (moduleSpecΓFunctor.map (originalPullbackFreeIso (Spec.map φ ≫ f) I).inv)
    hn hs hk
  have h' : E.map ((originalAffineFreeSectionsCoordinateIso A I).hom ≫
        moduleSpecΓFunctor.map (originalPullbackFreeIso f I).inv) ≫
      (originalCompositeSpecPullbackSectionsIso φ f S).hom =
        (originalAffineFreeScalarCoordinateIso φ I).hom ≫
          (originalAffineFreeSectionsCoordinateIso B I).hom ≫
            moduleSpecΓFunctor.map (originalPullbackFreeIso (Spec.map φ ≫ f) I).inv := by
    change E.map ((originalAffineFreeSectionsCoordinateIso A I).hom ≫
        moduleSpecΓFunctor.map (originalPullbackFreeIso f I).inv) ≫
      ((originalSpecPullbackSectionsIso φ ((pullback f).obj S)).hom ≫
        moduleSpecΓFunctor.map ((pullbackComp (Spec.map φ) f).app S).hom) = _
    simpa only [Functor.map_comp, Category.assoc] using h
  simpa only [originalCompositeSpecPullbackSectionsIso_hom] using h'

end Hironaka.Geometry.QuotGrassmann
