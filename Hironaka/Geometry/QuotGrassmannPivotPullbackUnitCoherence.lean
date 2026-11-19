import Hironaka.Geometry.QuotGrassmannPivotPullbackFree

/-!
# Actual native pullback unit frames commute with composition

Adapted from the native adjunction proofs in the repository's
EnvelopeProperty/deps/aintlib-ep33/ModularCurves/Picard/DualPullback/UnitComp.lean.
Only native Mathlib functors and the already frozen original unit frame occur.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem originalHomEquivCompConjugate
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    {X : C} {Y : D} (p : L₁.obj X ⟶ Y) :
    (adj₂.homEquiv X Y) (α.app X ≫ p) =
      (adj₁.homEquiv X Y) p ≫ (conjugateEquiv adj₁ adj₂ α).app Y := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp]
  calc
    adj₂.unit.app X ≫ R₂.map (α.app X) ≫ R₂.map p =
        (adj₂.unit.app X ≫ R₂.map (α.app X)) ≫ R₂.map p :=
      (Category.assoc _ _ _).symm
    _ = (adj₁.unit.app X ≫ (conjugateEquiv adj₁ adj₂ α).app (L₁.obj X)) ≫ R₂.map p :=
      congrArg (fun k => k ≫ R₂.map p)
        (unit_conjugateEquiv adj₁ adj₂ α X).symm
    _ = adj₁.unit.app X ≫ ((conjugateEquiv adj₁ adj₂ α).app (L₁.obj X) ≫ R₂.map p) :=
      Category.assoc _ _ _
    _ = adj₁.unit.app X ≫ (R₁.map p ≫ (conjugateEquiv adj₁ adj₂ α).app Y) :=
      congrArg (fun k => adj₁.unit.app X ≫ k)
        ((conjugateEquiv adj₁ adj₂ α).naturality p).symm
    _ = (adj₁.unit.app X ≫ R₁.map p) ≫ (conjugateEquiv adj₁ adj₂ α).app Y :=
      (Category.assoc _ _ _).symm

/-- The actual original structure-unit adjunction mates compose by the native pushforward comparison. -/
theorem originalUnitToPushforward_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    SheafOfModules.unitToPushforwardObjUnit (f ≫ g).toRingCatSheafHom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward g).map
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app (SheafOfModules.unit X.ringCatSheaf) := by
  apply SheafOfModules.hom_ext
  ext U
  rfl

/-- The actual canonical native original unit frame satisfies exact inverse-composition coherence. -/
theorem originalPullbackUnitIso_comp_inv {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((Scheme.Modules.pullbackComp f g).app (SheafOfModules.unit Z.ringCatSheaf)).inv ≫
      (Scheme.Modules.pullback f).map (originalPullbackUnitIso g).hom ≫
        (originalPullbackUnitIso f).hom = (originalPullbackUnitIso (f ≫ g)).hom := by
  let adjf := Scheme.Modules.pullbackPushforwardAdjunction f
  let adjg := Scheme.Modules.pullbackPushforwardAdjunction g
  let adjc := adjg.comp adjf
  let adjd := Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)
  let τ := Scheme.Modules.pushforwardComp f g
  let p := (Scheme.Modules.pullback f).map (originalPullbackUnitIso g).hom ≫
    (originalPullbackUnitIso f).hom
  let q := SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
    (Scheme.Modules.pushforward g).map
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
  have hr : (adjc.homEquiv _ _) p = q := by
    change (adjg.homEquiv _ _) ((adjf.homEquiv _ _)
      ((Scheme.Modules.pullback f).map (originalPullbackUnitIso g).hom ≫
        (originalPullbackUnitIso f).hom)) = _
    rw [Adjunction.homEquiv_naturality_left, originalPullbackUnitIso_mate]
    exact ((adjg.homEquiv_naturality_right (originalPullbackUnitIso g).hom
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))).trans
        (congrArg (fun z => z ≫ (Scheme.Modules.pushforward g).map
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))
          (originalPullbackUnitIso_mate g))
  have hc := originalHomEquivCompConjugate adjc adjd (Scheme.Modules.pullbackComp f g).inv p
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at hc
  apply (adjd.homEquiv _ _).injective
  exact hc.trans ((congrArg (fun z => z ≫ τ.hom.app (SheafOfModules.unit X.ringCatSheaf)) hr).trans
    ((originalUnitToPushforward_comp f g).symm.trans
      (originalPullbackUnitIso_mate (f ≫ g)).symm))

end Hironaka.Geometry.QuotGrassmann
