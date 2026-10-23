import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Actual native affine pushforward and SAME original section scalar action

Native-only port from EnvelopeProperty/deps/aintlib-ep33/ModularCurves/ForMathlib/
AffineModuleBaseChange.lean, SHA256
37e928fdc0399a2c2d67e4fbbd3c4579755f20483a0886f7f1b10dbda47e7a3d.
The actual original ring map, native pushforward, and literal original top-open
section comparison are retained, with EVERY original module-map naturality.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace DeJongAlterations.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def originalSpecPushforwardSectionsIso₁
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor ≅
      (modulesSpecToSheaf ⋙
          TopCat.Sheaf.pushforward (ModuleCat S) (Spec.map φ).base ⋙
            sheafCompose (Opens.grothendieckTopology (Spec R))
              (ModuleCat.restrictScalars φ.hom)) ⋙
        TopCat.Sheaf.forget (ModuleCat R) (Spec R) ⋙
          (CategoryTheory.evaluation
            (Opens (Spec R))ᵒᵖ (ModuleCat R)).obj
            (op (⊤ : (Spec R).Opens)) := by
  let H := TopCat.Sheaf.forget (ModuleCat R) (Spec R) ⋙
    (CategoryTheory.evaluation
      (Opens (Spec R))ᵒᵖ (ModuleCat R)).obj
      (op (⊤ : (Spec R).Opens))
  exact (Functor.associator
      (pushforward (Spec.map φ)) modulesSpecToSheaf H).symm ≪≫
    Functor.isoWhiskerRight (pushforwardCompModulesSpecToSheafIso φ) H

def originalSpecPushforwardSectionsIsoApp₂
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (N : (Spec S).Modules) :
    (((modulesSpecToSheaf ⋙
          TopCat.Sheaf.pushforward (ModuleCat S) (Spec.map φ).base ⋙
            sheafCompose (Opens.grothendieckTopology (Spec R))
              (ModuleCat.restrictScalars φ.hom)) ⋙
        TopCat.Sheaf.forget (ModuleCat R) (Spec R) ⋙
          (CategoryTheory.evaluation
            (Opens (Spec R))ᵒᵖ (ModuleCat R)).obj
            (op (⊤ : (Spec R).Opens))).obj N) ≅
      (moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom).obj N := by
  have htop :
      (Opens.map (Spec.map φ).base).op.obj (op (⊤ : (Spec R).Opens)) =
        op (⊤ : (Spec S).Opens) := by
    simp
  exact (ModuleCat.restrictScalars φ.hom).mapIso
    ((modulesSpecToSheaf.obj N).presheaf.mapIso (eqToIso htop))

def originalSpecPushforwardSectionsIso₂
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    (modulesSpecToSheaf ⋙
          TopCat.Sheaf.pushforward (ModuleCat S) (Spec.map φ).base ⋙
            sheafCompose (Opens.grothendieckTopology (Spec R))
              (ModuleCat.restrictScalars φ.hom)) ⋙
        TopCat.Sheaf.forget (ModuleCat R) (Spec R) ⋙
          (CategoryTheory.evaluation
            (Opens (Spec R))ᵒᵖ (ModuleCat R)).obj
            (op (⊤ : (Spec R).Opens)) ≅
      moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom :=
  NatIso.ofComponents (originalSpecPushforwardSectionsIsoApp₂ φ) (by
    intro M N f
    have htop :
        (Opens.map (Spec.map φ).base).op.obj (op (⊤ : (Spec R).Opens)) =
          op (⊤ : (Spec S).Opens) := by
      simp
    change
      (ModuleCat.restrictScalars φ.hom).map
            ((modulesSpecToSheaf.map f).1.app
              ((Opens.map (Spec.map φ).base).op.obj
                (op (⊤ : (Spec R).Opens)))) ≫
          (ModuleCat.restrictScalars φ.hom).map
            ((modulesSpecToSheaf.obj N).presheaf.map (eqToHom htop)) =
        (ModuleCat.restrictScalars φ.hom).map
              ((modulesSpecToSheaf.obj M).presheaf.map (eqToHom htop)) ≫
          (ModuleCat.restrictScalars φ.hom).map
            ((modulesSpecToSheaf.map f).1.app
              (op (⊤ : (Spec S).Opens)))
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (ModuleCat.restrictScalars φ.hom).map
      ((modulesSpecToSheaf.map f).1.naturality (eqToHom htop)).symm)

def originalSpecPushforwardSectionsIso
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor ≅
      moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom :=
  originalSpecPushforwardSectionsIso₁ φ ≪≫ originalSpecPushforwardSectionsIso₂ φ


end DeJongAlterations.Geometry.QuotGrassmann
