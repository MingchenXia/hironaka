import Hironaka.Geometry.QuotGrassmannPivotOverImage
import Hironaka.Geometry.QuotGrassmannPivotPullbackFree

/-!
# Reusable actual over-site, open-scheme and composite native pullback comparisons

This uses only the native over-site/open-scheme equivalence, native restriction
adjunction, and native pullback composition. Every original map is retained by
the naturality triangle. No frame, factorization or local-freeness input occurs.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual native open-site equivalence carries the original unit to the actual open-scheme unit. -/
def originalOverEquivUnitIso (X : Scheme.{u}) (U : X.Opens) :
    (Scheme.Modules.overEquiv U).functor.obj
      (SheafOfModules.unit (X.ringCatSheaf.over U)) ≅
        SheafOfModules.unit U.toScheme.ringCatSheaf :=
  U.sheafOfModulesEquivOverUnit X.ringCatSheaf

/-- The actual native free comparison retains the same original indices. -/
def originalOverEquivFreeIso (X : Scheme.{u}) (U : X.Opens) (I : Type u) :
    SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ≅
      (Scheme.Modules.overEquiv U).functor.obj
        (SheafOfModules.free (R := X.ringCatSheaf.over U) I) :=
  SheafOfModules.mapFreeIso (Scheme.Modules.overEquiv U).functor I
    (originalOverEquivUnitIso X U).symm

/-- The produced actual native free comparison preserves every actual original basis inclusion. -/
theorem originalOverEquivFreeIso_inclusion (X : Scheme.{u}) (U : X.Opens)
    (I : Type u) (i : I) :
    SheafOfModules.ιFree i ≫ (originalOverEquivFreeIso X U I).hom =
      (originalOverEquivUnitIso X U).inv ≫
        (Scheme.Modules.overEquiv U).functor.map (SheafOfModules.ιFree i) :=
  SheafOfModules.ιFree_mapFreeIso_hom (Scheme.Modules.overEquiv U).functor I
    (originalOverEquivUnitIso X U).symm i

/-- Actual original over-site restriction and open-scheme pullback compose to the true native pullback. -/
def originalOverCompositePullbackIso {X Y : Scheme.{u}} (U : X.Opens)
    (h : Y ⟶ U.toScheme) :
    SheafOfModules.overFunctor.{u} X.ringCatSheaf U ⋙
      (Scheme.Modules.overEquiv U).functor ⋙ Scheme.Modules.pullback h ≅
        Scheme.Modules.pullback (h ≫ U.ι) :=
  Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv U)
    (Scheme.Modules.pullback h) ≪≫
  Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι)
    (Scheme.Modules.pullback h) ≪≫
  Scheme.Modules.pullbackComp h U.ι

/-- Every SAME original native module-sheaf map satisfies the exact original comparison triangle. -/
theorem originalOverCompositePullbackIso_naturality {X Y : Scheme.{u}} (U : X.Opens)
    (h : Y ⟶ U.toScheme) {M N : X.Modules} (q : M ⟶ N) :
    (Scheme.Modules.pullback h).map ((Scheme.Modules.overEquiv U).functor.map
      ((SheafOfModules.overFunctor.{u} X.ringCatSheaf U).map q)) ≫
        (originalOverCompositePullbackIso U h).hom.app N =
      (originalOverCompositePullbackIso U h).hom.app M ≫
        (Scheme.Modules.pullback (h ≫ U.ι)).map q :=
  (originalOverCompositePullbackIso U h).hom.naturality q

end Hironaka.Geometry.QuotGrassmann
