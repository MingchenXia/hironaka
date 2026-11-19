import Hironaka.Geometry.QuotGrassmannPivotOpenUnitCoherence

/-!
# Exact ORIGINAL unit-frame coherence for the native over-site composite-pullback comparison

This removes any freedom in the source-unit frame: the comparison uses the
same canonical native original pullback unit and its actual original mate.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The reusable actual over-site composite-pullback comparison preserves the SAME canonical ORIGINAL unit. -/
theorem originalOverCompositePullbackIso_unit {X Y : Scheme.{u}} (U : X.Opens)
    (h : Y ⟶ U.toScheme) :
    (originalOverCompositePullbackIso U h).hom.app (SheafOfModules.unit X.ringCatSheaf) ≫
      (originalPullbackUnitIso (h ≫ U.ι)).hom = (originalPullbackUnitIso h).hom := by
  let P := Scheme.Modules.pullback h
  let a := (Scheme.Modules.overFunctorEquiv U).app (SheafOfModules.unit X.ringCatSheaf)
  let b := (Scheme.Modules.restrictFunctorIsoPullback U.ι).app (SheafOfModules.unit X.ringCatSheaf)
  let d := (Scheme.Modules.pullbackComp h U.ι).app (SheafOfModules.unit X.ringCatSheaf)
  have hd : d.hom ≫ (originalPullbackUnitIso (h ≫ U.ι)).hom =
      P.map (originalPullbackUnitIso U.ι).hom ≫ (originalPullbackUnitIso h).hom :=
    (d.inv_comp_eq.mp (originalPullbackUnitIso_comp_inv h U.ι)).symm
  have ha : a.hom = (Scheme.Modules.restrictUnitIso U.ι).inv :=
    congrArg Iso.hom (originalOverFunctorEquiv_unit X U)
  have hb := originalRestrictPullbackUnitIso U.ι
  have hbase : a.hom ≫ b.hom ≫ (originalPullbackUnitIso U.ι).hom = 𝟙 _ :=
    (congrArg (fun z => a.hom ≫ z) hb).trans
      ((congrArg (fun z => z ≫ (Scheme.Modules.restrictUnitIso U.ι).hom) ha).trans
        (Scheme.Modules.restrictUnitIso U.ι).inv_hom_id)
  have hm := congrArg P.map hbase
  simp only [P.map_comp, P.map_id] at hm
  have heq : (originalOverCompositePullbackIso U h).hom.app
      (SheafOfModules.unit X.ringCatSheaf) = P.map a.hom ≫ P.map b.hom ≫ d.hom := by
    dsimp only [originalOverCompositePullbackIso, Iso.trans_hom, NatTrans.comp_app]
    rfl
  calc
    _ = (P.map a.hom ≫ P.map b.hom ≫ d.hom) ≫
        (originalPullbackUnitIso (h ≫ U.ι)).hom :=
      congrArg (fun z => z ≫ (originalPullbackUnitIso (h ≫ U.ι)).hom) heq
    _ = P.map a.hom ≫ P.map b.hom ≫
        (d.hom ≫ (originalPullbackUnitIso (h ≫ U.ι)).hom) := by simp only [Category.assoc]
    _ = P.map a.hom ≫ P.map b.hom ≫
        (P.map (originalPullbackUnitIso U.ι).hom ≫ (originalPullbackUnitIso h).hom) :=
      congrArg (fun z => P.map a.hom ≫ P.map b.hom ≫ z) hd
    _ = (P.map a.hom ≫ P.map b.hom ≫ P.map (originalPullbackUnitIso U.ι).hom) ≫
        (originalPullbackUnitIso h).hom := by simp only [Category.assoc]
    _ = 𝟙 _ ≫ (originalPullbackUnitIso h).hom :=
      congrArg (fun z => z ≫ (originalPullbackUnitIso h).hom) hm
    _ = _ := Category.id_comp _

end Hironaka.Geometry.QuotGrassmann
