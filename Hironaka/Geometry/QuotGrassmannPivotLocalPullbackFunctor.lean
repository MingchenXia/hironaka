import Hironaka.Geometry.QuotGrassmannPivotOverSchemePullback

/-!
# Reusable ACTUAL native local pullback functor on original over-sites

This is the genuine open-site equivalence, actual scheme pullback on the
original inverse-image open, and inverse open-site equivalence. Its actual
unit and module comparisons are constructed from the original native maps.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The genuine native local module-pullback functor on the SAME original inverse-image over-site. -/
def originalLocalModulePullbackFunctor {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) :
    SheafOfModules.{u} (X.ringCatSheaf.over U) ⥤
      SheafOfModules.{u} (Y.ringCatSheaf.over (f ⁻¹ᵁ U)) :=
  (Scheme.Modules.overEquiv U).functor ⋙ Scheme.Modules.pullback (f ∣_ U) ⋙
    (Scheme.Modules.overEquiv (f ⁻¹ᵁ U)).inverse

/-- Actual native local pullback preserves colimits internally. -/
instance originalLocalModulePullbackFunctor_preservesColimits {X Y : Scheme.{u}}
    (f : Y ⟶ X) (U : X.Opens) : PreservesColimits (originalLocalModulePullbackFunctor f U) := by
  dsimp only [originalLocalModulePullbackFunctor]
  infer_instance

/-- The actual native original local pullback unit isomorphism, without a unit-frame input. -/
def originalLocalModulePullbackUnitIso {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) :
    (originalLocalModulePullbackFunctor f U).obj (SheafOfModules.unit (X.ringCatSheaf.over U)) ≅
      SheafOfModules.unit (Y.ringCatSheaf.over (f ⁻¹ᵁ U)) :=
  (Scheme.Modules.overEquiv (f ⁻¹ᵁ U)).inverse.mapIso
    ((Scheme.Modules.pullback (f ∣_ U)).mapIso (originalOverEquivUnitIso X U) ≪≫
      originalPullbackUnitIso (f ∣_ U)) ≪≫
    (f ⁻¹ᵁ U).sheafOfModulesEquivOverInverseUnit Y.ringCatSheaf

/-- The actual native original local scheme-pullback square, natural in EVERY original module sheaf. -/
def originalLocalSchemePullbackNatIso {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) :
    (SheafOfModules.overFunctor.{u} X.ringCatSheaf U ⋙ (Scheme.Modules.overEquiv U).functor) ⋙
        Scheme.Modules.pullback (f ∣_ U) ≅
      Scheme.Modules.pullback f ⋙
        (SheafOfModules.overFunctor.{u} Y.ringCatSheaf (f ⁻¹ᵁ U) ⋙
          (Scheme.Modules.overEquiv (f ⁻¹ᵁ U)).functor) :=
  Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv U) (Scheme.Modules.pullback (f ∣_ U)) ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι)
      (Scheme.Modules.pullback (f ∣_ U)) ≪≫
    Scheme.Modules.pullbackComp (f ∣_ U) U.ι ≪≫
    Scheme.Modules.pullbackCongr (morphismRestrict_ι f U) ≪≫
    (Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).symm ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
      (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).symm ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
      (Scheme.Modules.overFunctorEquiv (f ⁻¹ᵁ U)).symm

/-- The SAME actual original local-module functor compares naturally with genuine native pullback then restriction. -/
def originalLocalModulePullbackNatIso {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) :
    SheafOfModules.overFunctor.{u} X.ringCatSheaf U ⋙ originalLocalModulePullbackFunctor f U ≅
      Scheme.Modules.pullback f ⋙ SheafOfModules.overFunctor.{u} Y.ringCatSheaf (f ⁻¹ᵁ U) :=
  Functor.isoWhiskerRight (originalLocalSchemePullbackNatIso f U)
    (Scheme.Modules.overEquiv (f ⁻¹ᵁ U)).inverse ≪≫
    Functor.isoWhiskerLeft
      (Scheme.Modules.pullback f ⋙ SheafOfModules.overFunctor.{u} Y.ringCatSheaf (f ⁻¹ᵁ U))
      (Scheme.Modules.overEquiv (f ⁻¹ᵁ U)).unitIso.symm

/-- Every ORIGINAL map satisfies the actual native local-pullback/restriction triangle. -/
theorem originalLocalModulePullbackNatIso_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    (U : X.Opens) {M N : X.Modules} (q : M ⟶ N) :
    (originalLocalModulePullbackFunctor f U).map
      ((SheafOfModules.overFunctor.{u} X.ringCatSheaf U).map q) ≫
        (originalLocalModulePullbackNatIso f U).hom.app N =
      (originalLocalModulePullbackNatIso f U).hom.app M ≫
        (SheafOfModules.overFunctor.{u} Y.ringCatSheaf (f ⁻¹ᵁ U)).map
          ((Scheme.Modules.pullback f).map q) :=
  (originalLocalModulePullbackNatIso f U).hom.naturality q

/-- The ACTUAL original local pullback carries the SAME original free generator family to the native free family. -/
def originalLocalModulePullbackFreeIso {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens)
    (I : Type u) :
    SheafOfModules.free (R := Y.ringCatSheaf.over (f ⁻¹ᵁ U)) I ≅
      (originalLocalModulePullbackFunctor f U).obj (SheafOfModules.free (R := X.ringCatSheaf.over U) I) :=
  SheafOfModules.mapFreeIso (originalLocalModulePullbackFunctor f U) I
    (originalLocalModulePullbackUnitIso f U).symm

end Hironaka.Geometry.QuotGrassmann
