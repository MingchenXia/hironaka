import Hironaka.Geometry.QuotGrassmannPivotPullbackUnitCoherence
import Hironaka.Geometry.QuotGrassmannPivotOverSchemePullback

/-!
# Actual native open-restriction and pullback comparisons preserve ORIGINAL unit frames

These are the native adjunction/component proofs from the repository's
Picard/DualPullback/UnitComp and Picard/DualRestrict routes, retaining the
already frozen original native unit frame and using only Mathlib imports.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem originalSheafCompApply
    {D : Type u} [Category.{u} D] {J : GrothendieckTopology D}
    {S : Sheaf J RingCat.{u}} {A B C : SheafOfModules S}
    (p : A ⟶ B) (q : B ⟶ C) (W : Dᵒᵖ) (x : A.val.obj W) :
    (p ≫ q).val.app W x = q.val.app W (p.val.app W x) := rfl

private theorem originalOverFunctorEquiv_apply (X : Scheme.{u}) (U : X.Opens) (M : X.Modules)
    (W : U.toScheme.Opensᵒᵖ)
    (x : ((Scheme.Modules.overEquiv U).functor.obj (M.over U)).val.obj W) :
    ((Scheme.Modules.overFunctorEquiv U).hom.app M).val.app W x = x := by
  dsimp only [Scheme.Modules.overFunctorEquiv, Iso.trans_hom, NatTrans.comp_app]
  erw [originalSheafCompApply]
  rfl

/-- The native open-restriction unit frame has precisely the original structure-ring adjunction mate. -/
theorem originalRestrictUnitIso_mate {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictAdjunction f).homEquiv _ _ (Scheme.Modules.restrictUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  change (Scheme.Modules.restrictAdjunction f).unit.app (SheafOfModules.unit Y.ringCatSheaf) ≫
    (Scheme.Modules.pushforward f).map (Scheme.Modules.restrictUnitIso f).hom = _
  apply SheafOfModules.hom_ext
  ext U
  change (((Scheme.Modules.restrictAdjunction f).unit.app
      (SheafOfModules.unit Y.ringCatSheaf)).val.app U ≫
        (((Scheme.Modules.pushforward f).map (Scheme.Modules.restrictUnitIso f).hom).val.app U))
      (show Γ(Y, U.unop) from 1) = _
  rw [ConcreteCategory.comp_apply]
  dsimp only [Scheme.Modules.restrictAdjunction]
  erw [SheafOfModules.pushforwardPushforwardAdj_unit_app_val_app]
  change (f.appIso (f ⁻¹ᵁ U.unop)).hom (Y.presheaf.map _ (1 : Γ(Y, U.unop))) =
    (f.app U.unop).hom 1
  simp

/-- The actual native restriction/pullback comparison preserves the canonical ORIGINAL unit frame. -/
theorem originalRestrictPullbackUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctorIsoPullback f).hom.app (SheafOfModules.unit Y.ringCatSheaf) ≫
      (originalPullbackUnitIso f).hom = (Scheme.Modules.restrictUnitIso f).hom := by
  let adjr := Scheme.Modules.restrictAdjunction f
  let adjp := Scheme.Modules.pullbackPushforwardAdjunction f
  let e := (Scheme.Modules.restrictFunctorIsoPullback f).app (SheafOfModules.unit Y.ringCatSheaf)
  apply (adjr.homEquiv _ _).injective
  have he := Adjunction.homEquiv_leftAdjointUniq_hom_app adjr adjp
    (SheafOfModules.unit Y.ringCatSheaf)
  change (adjr.homEquiv _ _) e.hom = adjp.unit.app (SheafOfModules.unit Y.ringCatSheaf) at he
  have hp : adjp.unit.app (SheafOfModules.unit Y.ringCatSheaf) ≫
      (Scheme.Modules.pushforward f).map (originalPullbackUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    originalPullbackUnitIso_mate f
  exact (adjr.homEquiv_naturality_right e.hom (originalPullbackUnitIso f).hom).trans
    ((congrArg (fun z => z ≫ (Scheme.Modules.pushforward f).map
      (originalPullbackUnitIso f).hom) he).trans
      (hp.trans (originalRestrictUnitIso_mate f).symm))

/-- The actual native over/open-scheme comparison is the SAME original inverse restriction unit frame. -/
theorem originalOverFunctorEquiv_unit (X : Scheme.{u}) (U : X.Opens) :
    (Scheme.Modules.overFunctorEquiv U).app (SheafOfModules.unit X.ringCatSheaf) =
      (Scheme.Modules.restrictUnitIso U.ι).symm := by
  apply Iso.ext
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((Scheme.Modules.overFunctorEquiv U).hom.app
      (SheafOfModules.unit X.ringCatSheaf)).val.app W x =
    ((Scheme.Modules.restrictUnitIso U.ι).inv.val.app W).hom' x
  rw [originalOverFunctorEquiv_apply]
  have hr : ((Scheme.Modules.restrictUnitIso U.ι).inv.val.app W).hom' x =
      (U.ι.appIso W.unop).inv x := rfl
  rw [hr, Scheme.Opens.ι_appIso]
  rfl

end Hironaka.Geometry.QuotGrassmann
