import Hironaka.Geometry.QuotGrassmannPivotOverSchemeCoefficients
import Hironaka.Geometry.QuotGrassmannPivotPullbackMatrix

/-!
# Reusable whole native finite-free maps through the actual open-site equivalence

Both inclusions and projections are compared by their original native
coproduct universal properties. The resulting coefficient equality retains
entire native unit endomorphisms and actual native pullbacks.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every original basis inclusion is preserved in the actual native open-scheme free frame. -/
theorem originalOverEquivFreeIso_map_inclusion (X : Scheme.{u}) (U : X.Opens)
    (I : Type u) (i : I) :
    (Scheme.Modules.overEquiv U).functor.map (SheafOfModules.ιFree i) ≫
      (originalOverEquivFreeIso X U I).inv =
      (originalOverEquivUnitIso X U).hom ≫ SheafOfModules.ιFree i :=
  SheafOfModules.map_ιFree_mapFreeIso_inv (Scheme.Modules.overEquiv U).functor I
    (originalOverEquivUnitIso X U).symm i

/-- Every original native row projection is preserved in the SAME actual open-scheme free frame. -/
theorem originalOverEquivFreeProjection (X : Scheme.{u}) (U : X.Opens)
    {I : Type u} [DecidableEq I] (i : I) :
    (Scheme.Modules.overEquiv U).functor.map (originalOverFreeProjection X U i) ≫
      (originalOverEquivUnitIso X U).hom =
    (originalOverEquivFreeIso X U I).inv ≫ originalFreeProjection U.toScheme i := by
  let F := (Scheme.Modules.overEquiv U).functor
  apply (isColimitOfPreserves F
    (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf.over U) I)).hom_ext
  intro j
  change F.map (SheafOfModules.ιFree j.as) ≫
      (F.map (originalOverFreeProjection X U i) ≫ (originalOverEquivUnitIso X U).hom) =
    F.map (SheafOfModules.ιFree j.as) ≫
      ((originalOverEquivFreeIso X U I).inv ≫ originalFreeProjection U.toScheme i)
  rw [← Category.assoc, ← F.map_comp (SheafOfModules.ιFree j.as) (originalOverFreeProjection X U i),
    originalOverFreeProjection_inclusion]
  rw [← Category.assoc, originalOverEquivFreeIso_map_inclusion, Category.assoc,
    originalFreeProjection_inclusion]
  split_ifs <;> simp

/-- The SAME whole original free-sheaf map in its actual native open-scheme free frames. -/
def originalOverEquivFreeHom (X : Scheme.{u}) (U : X.Opens) {I J : Type u}
    (q : SheafOfModules.free (R := X.ringCatSheaf.over U) I ⟶
      SheafOfModules.free (R := X.ringCatSheaf.over U) J) :
    SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ⟶
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) J :=
  (originalOverEquivFreeIso X U I).hom ≫ (Scheme.Modules.overEquiv U).functor.map q ≫
    (originalOverEquivFreeIso X U J).inv

/-- Actual whole original matrix coefficients are transported as entire native unit endomorphisms. -/
theorem originalOverEquivFreeHom_coefficient (X : Scheme.{u}) (U : X.Opens)
    {I J : Type u} [DecidableEq J]
    (q : SheafOfModules.free (R := X.ringCatSheaf.over U) I ⟶
      SheafOfModules.free (R := X.ringCatSheaf.over U) J) (i : I) (j : J) :
    originalFreeHomCoefficient (originalOverEquivFreeHom X U q) i j =
      originalOverEquivUnitEnd X U
        (SheafOfModules.ιFree i ≫ q ≫ originalOverFreeProjection X U j) :=
  originalConjugatedCoefficient (Scheme.Modules.overEquiv U).functor
    (originalOverEquivUnitIso X U) (originalOverEquivFreeIso X U I).symm
    (originalOverEquivFreeIso X U J).symm
    (SheafOfModules.ιFree i) (originalOverFreeProjection X U j) q
    (SheafOfModules.ιFree i) (originalFreeProjection U.toScheme j)
    (originalOverEquivFreeIso_map_inclusion X U I i) (originalOverEquivFreeProjection X U j)

/-- Genuine native pullback preserves the SAME entire original over-site coefficient. -/
theorem originalOverSchemePullbackFreeHom_coefficient {X Y : Scheme.{u}}
    (U : X.Opens) (h : Y ⟶ U.toScheme) {I J : Type u} [DecidableEq J]
    (q : SheafOfModules.free (R := X.ringCatSheaf.over U) I ⟶
      SheafOfModules.free (R := X.ringCatSheaf.over U) J) (i : I) (j : J) :
    originalFreeHomCoefficient (originalPullbackFreeHom h (originalOverEquivFreeHom X U q)) i j =
      originalPullbackUnitEnd h (originalOverEquivUnitEnd X U
        (SheafOfModules.ιFree i ≫ q ≫ originalOverFreeProjection X U j)) :=
  (originalPullbackFreeHom_coefficient h (originalOverEquivFreeHom X U q) i j).trans
    (congrArg (originalPullbackUnitEnd h) (originalOverEquivFreeHom_coefficient X U q i j))

end Hironaka.Geometry.QuotGrassmann
