import Hironaka.Geometry.QuotGrassmannPivotCompositeUnitCoherence
import Hironaka.Geometry.QuotGrassmannPivotOverSchemeMatrices

/-!
# The reusable native over-site source frame is the canonical ORIGINAL free-pullback frame

The whole source comparison is determined by its original native basis maps,
and its original unit frame has already been identified canonically.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual native over-site/open-scheme/pullback transport of the original free sheaf. -/
def originalOverOpenPullbackFreeIso {X Y : Scheme.{u}} (U : X.Opens) (h : Y ⟶ U.toScheme)
    (J : Type u) :
    ((Scheme.Modules.overEquiv U).functor ⋙ Scheme.Modules.pullback h).obj
      (SheafOfModules.free (R := X.ringCatSheaf.over U) J) ≅
      SheafOfModules.free (R := Y.ringCatSheaf) J :=
  (Scheme.Modules.pullback h).mapIso (originalOverEquivFreeIso X U J).symm ≪≫
    originalPullbackFreeIso h J

/-- This SAME actual native composite free frame retains every ORIGINAL basis inclusion. -/
theorem originalOverOpenPullbackFreeIso_inclusion {X Y : Scheme.{u}} (U : X.Opens)
    (h : Y ⟶ U.toScheme) (J : Type u) (j : J) :
    ((Scheme.Modules.overEquiv U).functor ⋙ Scheme.Modules.pullback h).map
      (SheafOfModules.ιFree j) ≫ (originalOverOpenPullbackFreeIso U h J).hom =
      (originalPullbackUnitIso h).hom ≫ SheafOfModules.ιFree j := by
  let E := (Scheme.Modules.overEquiv U).functor
  let P := Scheme.Modules.pullback h
  let a := originalOverEquivFreeIso X U J
  let b := originalPullbackFreeIso h J
  have he : E.map (SheafOfModules.ιFree j) ≫ a.inv = SheafOfModules.ιFree j :=
    (originalOverEquivFreeIso_map_inclusion X U J j).trans (Category.id_comp _)
  calc
    _ = (P.map (E.map (SheafOfModules.ιFree j)) ≫ P.map a.inv) ≫ b.hom :=
      (Category.assoc _ _ _).symm
    _ = P.map (E.map (SheafOfModules.ιFree j) ≫ a.inv) ≫ b.hom :=
      congrArg (fun z => z ≫ b.hom) (P.map_comp _ _).symm
    _ = P.map (SheafOfModules.ιFree j) ≫ b.hom :=
      congrArg (fun z => P.map z ≫ b.hom) he
    _ = _ := originalPullbackFreeIso_inclusion h j

/-- The actual native composite-pullback source comparison, with no frame supplied as data. -/
def originalOverCompositeFreeIso {X Y : Scheme.{u}} (U : X.Opens) (h : Y ⟶ U.toScheme)
    (J : Type u) :
    (Scheme.Modules.pullback (h ≫ U.ι)).obj (SheafOfModules.free (R := X.ringCatSheaf) J) ≅
      SheafOfModules.free (R := Y.ringCatSheaf) J :=
  ((originalOverCompositePullbackIso U h).app (SheafOfModules.free (R := X.ringCatSheaf) J)).symm ≪≫
    ((Scheme.Modules.overEquiv U).functor ⋙ Scheme.Modules.pullback h).mapIso
      (originalOverFreeIso X U J).symm ≪≫ originalOverOpenPullbackFreeIso U h J

/-- The entire actual original composite source comparison preserves the SAME canonical original basis. -/
theorem originalOverCompositeFreeIso_inclusion {X Y : Scheme.{u}} (U : X.Opens)
    (h : Y ⟶ U.toScheme) (J : Type u) (j : J) :
    (Scheme.Modules.pullback (h ≫ U.ι)).map (SheafOfModules.ιFree j) ≫
      (originalOverCompositeFreeIso U h J).hom =
      (originalPullbackUnitIso (h ≫ U.ι)).hom ≫ SheafOfModules.ιFree j := by
  let F := SheafOfModules.overFunctor.{u} X.ringCatSheaf U
  let H := (Scheme.Modules.overEquiv U).functor ⋙ Scheme.Modules.pullback h
  let G := Scheme.Modules.pullback (h ≫ U.ι)
  let c := originalOverCompositePullbackIso U h
  let s := originalOverFreeIso X U J
  let t := originalOverOpenPullbackFreeIso U h J
  let a := (c.app (SheafOfModules.unit X.ringCatSheaf))
  have hs₁ : H.map (SheafOfModules.ιFree j) ≫ (H.mapIso s).hom =
      H.map (F.map (SheafOfModules.ιFree j)) :=
    (H.map_comp _ _).symm.trans (congrArg H.map (originalOverFreeIso_inclusion X U J j))
  have hs : H.map (F.map (SheafOfModules.ιFree j)) ≫ (H.mapIso s).inv =
      H.map (SheafOfModules.ιFree j) := (H.mapIso s).comp_inv_eq.mpr hs₁.symm
  have hu : a.inv ≫ (originalPullbackUnitIso h).hom =
      (originalPullbackUnitIso (h ≫ U.ι)).hom :=
    a.inv_comp_eq.mpr (originalOverCompositePullbackIso_unit U h).symm
  calc
    _ = (G.map (SheafOfModules.ιFree j) ≫
        (c.app (SheafOfModules.free (R := X.ringCatSheaf) J)).inv) ≫
          (H.mapIso s).inv ≫ t.hom := by
      simp only [originalOverCompositeFreeIso, Iso.trans_hom, Iso.symm_hom,
        Functor.mapIso_hom, Category.assoc]
      rfl
    _ = (a.inv ≫ H.map (F.map (SheafOfModules.ιFree j))) ≫ (H.mapIso s).inv ≫ t.hom :=
      congrArg (fun z => z ≫ (H.mapIso s).inv ≫ t.hom)
        (c.inv.naturality (SheafOfModules.ιFree j))
    _ = a.inv ≫ H.map (SheafOfModules.ιFree j) ≫ t.hom := by
      simp only [Category.assoc]
      exact congrArg (fun z => a.inv ≫ z ≫ t.hom) hs
    _ = a.inv ≫ (originalPullbackUnitIso h).hom ≫ SheafOfModules.ιFree j :=
      congrArg (fun z => a.inv ≫ z) (originalOverOpenPullbackFreeIso_inclusion U h J j)
    _ = _ := by
      exact (Category.assoc a.inv (originalPullbackUnitIso h).hom
        (SheafOfModules.ιFree j)).symm.trans
          (congrArg (fun z => z ≫ SheafOfModules.ιFree j) hu)

/-- The entire actual original composite source frame is EXACTLY the canonical ORIGINAL native free-pullback frame. -/
theorem originalOverCompositeFreeIso_eq_originalPullbackFreeIso {X Y : Scheme.{u}}
    (U : X.Opens) (h : Y ⟶ U.toScheme) (J : Type u) :
    originalOverCompositeFreeIso U h J = originalPullbackFreeIso (h ≫ U.ι) J := by
  apply Iso.ext
  apply (isColimitOfPreserves (Scheme.Modules.pullback (h ≫ U.ι))
    (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) J)).hom_ext
  intro j
  exact (originalOverCompositeFreeIso_inclusion U h J j.as).trans
    (originalPullbackFreeIso_inclusion (h ≫ U.ι) j.as).symm

end Hironaka.Geometry.QuotGrassmann
