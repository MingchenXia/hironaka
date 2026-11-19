import Hironaka.Geometry.QuotGrassmannPivotAffineSectionUnitValues
import Hironaka.Geometry.QuotGrassmannPivotPullbackFree

/-!
# SAME original native unit-pullback frame sends original pullback one to one

The original native unit adjunction mate is the SAME actual structural-ring map.
Naturality of the actual affine pushforward-section comparison proves the whole
readback diagram. Every resulting coefficient is computed using original one.
-/

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual ORIGINAL unit structural map and actual pushforward section comparison preserve the original unit section. -/
theorem originalSpecStructureUnit_one {A B : CommRingCat.{u}} (φ : A ⟶ B) :
    (originalSpecPushforwardSectionsIso φ).hom.app
      (SheafOfModules.unit (Spec B).ringCatSheaf)
        (moduleSpecΓFunctor.map
          (SheafOfModules.unitToPushforwardObjUnit (Spec.map φ).toRingCatSheafHom)
            (1 : Γ(Spec A, ⊤))) = (1 : Γ(Spec B, ⊤)) := by
  rw [originalSpecPushforwardSectionsIso_apply]
  change (Spec B).presheaf.map (eqToHom (show (⊤ : (Spec B).Opens) =
      (Spec.map φ) ⁻¹ᵁ (⊤ : (Spec A).Opens) by simp)).op
      ((Spec.map φ).app ⊤ (1 : Γ(Spec A, ⊤))) = (1 : Γ(Spec B, ⊤))
  rw [map_one, map_one]

/-- SAME original canonical native unit-pullback frame sends the actual original pullback-unit section of one to one. -/
theorem originalSpecPullbackUnitTop_frame_one {A B : CommRingCat.{u}} (φ : A ⟶ B) :
    moduleSpecΓFunctor.map (originalPullbackUnitIso (Spec.map φ)).hom
      (originalSpecPullbackUnitTop φ (SheafOfModules.unit (Spec A).ringCatSheaf)
        (1 : Γ(Spec A, ⊤))) = (1 : Γ(Spec B, ⊤)) := by
  let S := SheafOfModules.unit (Spec A).ringCatSheaf
  let T := SheafOfModules.unit (Spec B).ringCatSheaf
  let P := pullback (Spec.map φ)
  let U := pushforward (Spec.map φ)
  let e := originalPullbackUnitIso (Spec.map φ)
  let β := originalSpecPushforwardSectionsIso φ
  have hm : (pullbackPushforwardAdjunction (Spec.map φ)).unit.app S ≫ U.map e.hom =
      SheafOfModules.unitToPushforwardObjUnit (Spec.map φ).toRingCatSheafHom :=
    originalPullbackUnitIso_mate (Spec.map φ)
  have hg := congrArg moduleSpecΓFunctor.map hm
  simp only [Functor.map_comp] at hg
  have hn := β.hom.naturality e.hom
  simp only [Functor.comp_map] at hn
  have h := congrArg (fun q => q ≫ β.hom.app T) hg
  rw [Category.assoc, hn] at h
  have hv := ConcreteCategory.congr_hom h (1 : Γ(Spec A, ⊤))
  change moduleSpecΓFunctor.map e.hom
      (originalSpecPullbackUnitTop φ S (1 : Γ(Spec A, ⊤))) =
    β.hom.app T (moduleSpecΓFunctor.map
      (SheafOfModules.unitToPushforwardObjUnit (Spec.map φ).toRingCatSheafHom)
        (1 : Γ(Spec A, ⊤))) at hv
  exact hv.trans (originalSpecStructureUnit_one φ)

end Hironaka.Geometry.QuotGrassmann
