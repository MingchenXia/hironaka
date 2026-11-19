import Hironaka.Geometry.QuotGrassmannPivotOverImage

/-!
# Actual original native over-map finite-free comparisons

The native over-map adjunction and native actual unit comparison construct
the finite-free comparison internally. No restricted frame is an input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual original native over-map preserves colimits by its actual native adjunction. -/
theorem originalOverMap_preservesColimits (X : Scheme.{u}) {U W : X.Opens} (f : W ⟶ U) :
    PreservesColimits (SheafOfModules.overMap.{u} X.ringCatSheaf f) := by
  let F := SheafOfModules.overMap.{u} X.ringCatSheaf f
  let : F.IsLeftAdjoint := (SheafOfModules.overMapPushforwardAdj X.ringCatSheaf f).isLeftAdjoint
  infer_instance

/-- The SAME original native over-map has its internally produced original free-sheaf comparison. -/
def originalOverMapFreeIso (X : Scheme.{u}) {U W : X.Opens} (f : W ⟶ U) (I : Type u) :
    SheafOfModules.free (R := X.ringCatSheaf.over W) I ≅
      (SheafOfModules.overMap.{u} X.ringCatSheaf f).obj
        (SheafOfModules.free (R := X.ringCatSheaf.over U) I) := by
  let := originalOverMap_preservesColimits X f
  exact SheafOfModules.mapFreeIso (SheafOfModules.overMap.{u} X.ringCatSheaf f) I
    (SheafOfModules.overMapUnitIso (R := X.ringCatSheaf) f).symm

/-- The actual original native over-map comparison preserves every SAME original basis inclusion. -/
theorem originalOverMapFreeIso_inclusion (X : Scheme.{u}) {U W : X.Opens}
    (f : W ⟶ U) (I : Type u) (i : I) :
    SheafOfModules.ιFree i ≫ (originalOverMapFreeIso X f I).hom =
      (SheafOfModules.overMapUnitIso (R := X.ringCatSheaf) f).inv ≫
        (SheafOfModules.overMap.{u} X.ringCatSheaf f).map (SheafOfModules.ιFree i) := by
  let := originalOverMap_preservesColimits X f
  exact SheafOfModules.ιFree_mapFreeIso_hom
    (SheafOfModules.overMap.{u} X.ringCatSheaf f) I
    (SheafOfModules.overMapUnitIso (R := X.ringCatSheaf) f).symm i

end Hironaka.Geometry.QuotGrassmann
