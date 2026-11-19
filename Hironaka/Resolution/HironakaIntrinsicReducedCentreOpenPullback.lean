import Hironaka.Resolution.HironakaIntrinsicReducedCentreOpenSections
import Hironaka.Resolution.HironakaIntrinsicReducedCentreIdealModel
import Hironaka.Resolution.HironakaNativePulledIdealStalk

/-!
# ENTIRE native intrinsic ideal transport and full sheaf comparison on original opens

For an actual ORIGINAL open immersion, all original stalk ideals, actual
component sections, native unit submodules and FULL module-sheaf inclusions
are internally identified. Actual section lifts come from native OI invApp;
no image equality/local iso/dictionary is assumed. Only isomorphic-open
REDUCED target transport is compared; arbitrary pulled images stay entire.

Blueprint: `hironaka-intrinsic-reduced-centre-open-pullback.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Hironaka.HironakaIntrinsicReducedCentreOpenPullback

open HironakaSingularModuleSheafStalk HironakaIntrinsicReducedCentreIdealSheaf
  HironakaIntrinsicReducedCentreIdealModel HironakaIntrinsicReducedCentreOpenSections
  HironakaNativePulledIdealSheaf
  HironakaNativePulledIdealStalk

noncomputable section
universe u
variable {X Y : LocallyRingedSpace.{u}}

/-- EXACT actual native inclusion-stalk image of the SAME intrinsic centre module. -/
abbrev intrinsicCentreStalkRange (Z : LocallyRingedSpace.{u}) (C : Set Z) (z : Z) :
    Ideal (Z.presheaf.stalk z).carrier :=
  LinearMap.range (intrinsicReducedCentreStalkInclusion Z C z)

/-- At an actual original centre point the ENTIRE actual image lies in its native maximal ideal. -/
theorem intrinsicCentreStalkRange_le_maximalIdeal (Z : LocallyRingedSpace.{u}) (C : Set Z)
    (z : Z) (hzC : z ∈ C) :
    intrinsicCentreStalkRange Z C z ≤ IsLocalRing.maximalIdeal (Z.presheaf.stalk z).carrier := by
  rintro r ⟨m, rfl⟩
  obtain ⟨V, hzV, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (intrinsicReducedCentreIdealModule Z C).val.presheaf m
  exact (stalkInclusionLinearMap_germ Z.toSheafedSpace.sheaf
    (intrinsicReducedCentreIdealModule Z C) (intrinsicReducedCentreIdealInclusion Z C)
      z V hzV s).symm ▸ s.property z hzV hzC

/-- BOTH ENTIRE ideal directions are derived using actual native OI section lifts. -/
theorem openImmersion_pulled_stalkIdeal_eq (j : X ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion j] (C : Set Y) (x : X) :
    nativePulledIdealStalkIdeal j (intrinsicReducedCentreIdealModule Y C)
      (intrinsicReducedCentreIdealInclusion Y C) x = intrinsicCentreStalkRange X (j.base ⁻¹' C) x := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    rintro a ⟨m, hm⟩
    obtain ⟨V, hxV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq
      (intrinsicReducedCentreIdealModule Y C).val.presheaf m
    let s := pullbackIntrinsicSection j C V t
    refine ⟨TopCat.Presheaf.germ
      (intrinsicReducedCentreIdealModule X (j.base ⁻¹' C)).val.presheaf
        ((Opens.map j.base).obj V) x hxV s, ?_⟩
    exact (stalkInclusionLinearMap_germ X.toSheafedSpace.sheaf
      (intrinsicReducedCentreIdealModule X (j.base ⁻¹' C))
      (intrinsicReducedCentreIdealInclusion X (j.base ⁻¹' C)) x _ hxV s).trans
      ((pullbackIntrinsicSection_germ j C V t x hxV).trans
        (congrArg (j.stalkMap x).hom
          ((stalkInclusionLinearMap_germ Y.toSheafedSpace.sheaf
            (intrinsicReducedCentreIdealModule Y C) (intrinsicReducedCentreIdealInclusion Y C)
              (j.base x) V hxV t).symm.trans hm)))
  · rintro r ⟨m, rfl⟩
    obtain ⟨V, hxV, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq
      (intrinsicReducedCentreIdealModule X (j.base ⁻¹' C)).val.presheaf m
    let t := openImmersionIntrinsicSectionLift j C V s
    have hxT : j.base x ∈ (LocallyRingedSpace.IsOpenImmersion.opensFunctor j).obj V := ⟨x, hxV, rfl⟩
    have ht : Y.presheaf.germ _ (j.base x) hxT t.val ∈ intrinsicCentreStalkRange Y C (j.base x) :=
      ⟨TopCat.Presheaf.germ (intrinsicReducedCentreIdealModule Y C).val.presheaf _ (j.base x) hxT t,
        stalkInclusionLinearMap_germ Y.toSheafedSpace.sheaf
          (intrinsicReducedCentreIdealModule Y C) (intrinsicReducedCentreIdealInclusion Y C)
            (j.base x) _ hxT t⟩
    have hmap := Ideal.mem_map_of_mem (j.stalkMap x).hom ht
    have hg := openImmersionIntrinsicSectionLift_germ j C V s x hxV
    exact (stalkInclusionLinearMap_germ X.toSheafedSpace.sheaf
      (intrinsicReducedCentreIdealModule X (j.base ⁻¹' C))
      (intrinsicReducedCentreIdealInclusion X (j.base ⁻¹' C)) x V hxV s).symm ▸ (hg ▸ hmap)

/-- The ACTUAL native pulled-ideal inclusion has exactly the SAME original intrinsic image. -/
theorem openImmersion_pulled_stalkInclusion_range (j : X ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion j] (C : Set Y) (x : X) :
    LinearMap.range (nativePulledIdealStalkInclusion j (intrinsicReducedCentreIdealModule Y C)
      (intrinsicReducedCentreIdealInclusion Y C) x) = intrinsicCentreStalkRange X (j.base ⁻¹' C) x :=
  (nativePulledIdealStalkInclusion_range j (intrinsicReducedCentreIdealModule Y C)
    (intrinsicReducedCentreIdealInclusion Y C) x).trans (openImmersion_pulled_stalkIdeal_eq j C x)

/-- Literal original section ideal equality, at EVERY unchanged original source open. -/
theorem openImmersion_pulled_sectionIdeal_eq (j : X ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion j] (C : Set Y) (U : Opens X.toTopCat) :
    nativePulledIdealSectionIdeal j (intrinsicReducedCentreIdealModule Y C)
      (intrinsicReducedCentreIdealInclusion Y C) U = intrinsicReducedCentreSectionIdeal X (j.base ⁻¹' C) U := by
  ext s
  constructor
  · intro hs x hx hxC
    have hr := hs x hx
    rw [openImmersion_pulled_stalkIdeal_eq] at hr
    exact intrinsicCentreStalkRange_le_maximalIdeal X (j.base ⁻¹' C) x hxC hr
  · intro hs x hx
    rw [openImmersion_pulled_stalkIdeal_eq]
    exact ⟨TopCat.Presheaf.germ (intrinsicReducedCentreIdealModule X (j.base ⁻¹' C)).val.presheaf
      U x hx ⟨s, hs⟩, stalkInclusionLinearMap_germ X.toSheafedSpace.sheaf
        (intrinsicReducedCentreIdealModule X (j.base ⁻¹' C))
        (intrinsicReducedCentreIdealInclusion X (j.base ⁻¹' C)) x U hx ⟨s, hs⟩⟩

/-- The actual native original unit submodules agree, without an incoming comparison. -/
theorem openImmersion_pulled_submodule_eq (j : X ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion j] (C : Set Y) :
    nativePulledIdealSubmodule j (intrinsicReducedCentreIdealModule Y C)
      (intrinsicReducedCentreIdealInclusion Y C) = intrinsicReducedCentreSubmodule X (j.base ⁻¹' C) := by
  apply PresheafOfModules.Submodule.ext
  intro U
  exact openImmersion_pulled_sectionIdeal_eq j C (unop U)

/-- FULL native module-sheaf isomorphism from genuine pullback to SAME intrinsic centre trace. -/
def openImmersion_pulled_idealIso (j : X ⟶ Y) [LocallyRingedSpace.IsOpenImmersion j] (C : Set Y) :
    nativePulledIdealModule j (intrinsicReducedCentreIdealModule Y C)
      (intrinsicReducedCentreIdealInclusion Y C) ≅ intrinsicReducedCentreIdealModule X (j.base ⁻¹' C) where
  hom := ⟨PresheafOfModules.Submodule.homOfLE (openImmersion_pulled_submodule_eq j C).le⟩
  inv := ⟨PresheafOfModules.Submodule.homOfLE (openImmersion_pulled_submodule_eq j C).ge⟩
  hom_inv_id := by ext U s; rfl
  inv_hom_id := by ext U s; rfl

@[simp] theorem openImmersion_pulled_idealIso_hom_app_val (j : X ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion j] (C : Set Y) (U : Opens X.toTopCat)
    (s : nativePulledIdealSectionIdeal j (intrinsicReducedCentreIdealModule Y C)
      (intrinsicReducedCentreIdealInclusion Y C) U) :
    ((openImmersion_pulled_idealIso j C).hom.val.app (op U) s).val = s.val := rfl

@[simp] theorem openImmersion_pulled_idealIso_inv_app_val (j : X ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion j] (C : Set Y) (U : Opens X.toTopCat)
    (s : intrinsicReducedCentreSectionIdeal X (j.base ⁻¹' C) U) :
    ((openImmersion_pulled_idealIso j C).inv.val.app (op U) s).val = s.val := rfl

/-- The FULL original inclusion triangle commutes, retaining every actual component. -/
theorem openImmersion_pulled_idealIso_hom_comp_inclusion (j : X ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion j] (C : Set Y) :
    (openImmersion_pulled_idealIso j C).hom ≫ intrinsicReducedCentreIdealInclusion X (j.base ⁻¹' C) =
      nativePulledIdealInclusion j (intrinsicReducedCentreIdealModule Y C)
        (intrinsicReducedCentreIdealInclusion Y C) := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι (openImmersion_pulled_submodule_eq j C).le

/-- The inverse FULL inclusion triangle commutes as actual native sheaf morphisms. -/
theorem openImmersion_pulled_idealIso_inv_comp_inclusion (j : X ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion j] (C : Set Y) :
    (openImmersion_pulled_idealIso j C).inv ≫ nativePulledIdealInclusion j
      (intrinsicReducedCentreIdealModule Y C) (intrinsicReducedCentreIdealInclusion Y C) =
        intrinsicReducedCentreIdealInclusion X (j.base ⁻¹' C) := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι (openImmersion_pulled_submodule_eq j C).ge

end
end Hironaka.HironakaIntrinsicReducedCentreOpenPullback
