import Hironaka.Resolution.HironakaNativePulledIdealStalk

/-! Composition of ENTIRE native pulled image ideals on arbitrary ORIGINAL
locally ringed spaces. The actual old inclusion-stalk image theorem and
original stalkMap_comp derive the equality; native unit-submodule equality
then supplies the full sheaf iso with both literal inclusion triangles.
Blueprint FIRST: hironaka-native-pulled-ideal-composition.tex. -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Hironaka.HironakaNativePulledIdealComposition

open HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf HironakaNativePulledIdealStalk

noncomputable section
universe u
variable {X Y Z : LocallyRingedSpace.{u}} (F : Y ⟶ X) (q : Z ⟶ Y)
  (B : SheafOfModules.{u} (forgetRing X.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.toSheafedSpace.sheaf))

/-- Both ENTIRE native image ideals coincide for the SAME original composite. -/
theorem stalkIdeal_comp (z : Z) :
    nativePulledIdealStalkIdeal q (nativePulledIdealModule F B b)
      (nativePulledIdealInclusion F B b) z =
      nativePulledIdealStalkIdeal (q ≫ F) B b z := by
  let A := LinearMap.range (stalkInclusionLinearMap X.toSheafedSpace.sheaf B b (F.base (q.base z)))
  have hMap := Ideal.map_map (I := A) (F.stalkMap (q.base z)).hom (q.stalkMap z).hom
  have hComp : ((q ≫ F).stalkMap z).hom =
      (q.stalkMap z).hom.comp (F.stalkMap (q.base z)).hom :=
    congrArg CommRingCat.Hom.hom (LocallyRingedSpace.stalkMap_comp (f := q) (g := F) z)
  calc
    _ = Ideal.map (q.stalkMap z).hom (nativePulledIdealStalkIdeal F B b (q.base z)) :=
      congrArg (Ideal.map (q.stalkMap z).hom)
        (nativePulledIdealStalkInclusion_range F B b (q.base z))
    _ = Ideal.map ((q.stalkMap z).hom.comp (F.stalkMap (q.base z)).hom) A := hMap
    _ = _ := congrArg (fun f => Ideal.map f A) hComp.symm

/-- EVERY original section ideal is the SAME entire original composite image. -/
theorem sectionIdeal_comp (U : Opens Z.toTopCat) :
    nativePulledIdealSectionIdeal q (nativePulledIdealModule F B b)
      (nativePulledIdealInclusion F B b) U =
      nativePulledIdealSectionIdeal (q ≫ F) B b U := by
  ext s
  constructor
  · intro hs z hz
    exact (stalkIdeal_comp F q B b z) ▸ hs z hz
  · intro hs z hz
    exact (stalkIdeal_comp F q B b z).symm ▸ hs z hz

/-- The existing native original unit submodules coincide with ALL their actions. -/
theorem submodule_comp :
    nativePulledIdealSubmodule q (nativePulledIdealModule F B b)
      (nativePulledIdealInclusion F B b) =
      nativePulledIdealSubmodule (q ≫ F) B b := by
  apply PresheafOfModules.Submodule.ext
  intro U
  exact sectionIdeal_comp F q B b (unop U)

/-- FULL native sheaf isomorphism from the internally proved entire equality. -/
def compositionIso :
    nativePulledIdealModule q (nativePulledIdealModule F B b)
      (nativePulledIdealInclusion F B b) ≅ nativePulledIdealModule (q ≫ F) B b where
  hom := ⟨PresheafOfModules.Submodule.homOfLE (submodule_comp F q B b).le⟩
  inv := ⟨PresheafOfModules.Submodule.homOfLE (submodule_comp F q B b).ge⟩
  hom_inv_id := by ext U s; rfl
  inv_hom_id := by ext U s; rfl

@[simp] theorem compositionIso_hom_app_val (U : Opens Z.toTopCat)
    (s : nativePulledIdealSectionIdeal q (nativePulledIdealModule F B b)
      (nativePulledIdealInclusion F B b) U) :
    ((compositionIso F q B b).hom.val.app (op U) s).val = s.val := rfl

@[simp] theorem compositionIso_inv_app_val (U : Opens Z.toTopCat)
    (s : nativePulledIdealSectionIdeal (q ≫ F) B b U) :
    ((compositionIso F q B b).inv.val.app (op U) s).val = s.val := rfl

/-- The FULL original structure-unit inclusion triangle commutes. -/
theorem compositionIso_hom_comp_inclusion :
    (compositionIso F q B b).hom ≫ nativePulledIdealInclusion (q ≫ F) B b =
      nativePulledIdealInclusion q (nativePulledIdealModule F B b)
        (nativePulledIdealInclusion F B b) := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι (submodule_comp F q B b).le

/-- The inverse FULL original structure-unit inclusion triangle also commutes. -/
theorem compositionIso_inv_comp_inclusion :
    (compositionIso F q B b).inv ≫
        nativePulledIdealInclusion q (nativePulledIdealModule F B b)
          (nativePulledIdealInclusion F B b) =
      nativePulledIdealInclusion (q ≫ F) B b := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι (submodule_comp F q B b).ge

end
end Hironaka.HironakaNativePulledIdealComposition
