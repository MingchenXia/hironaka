import Hironaka.Resolution.HironakaIntrinsicReducedCentreIdealSheaf
import Mathlib.Geometry.RingedSpace.OpenImmersion

/-!
# Actual original section lifts for intrinsic REDUCED centre ideals

Native local-ring maximal-ideal transport and actual OI inverse sections
produce real original centre section lifts, with full original germ formulas.
This compares isomorphic opens only; arbitrary later pulled ideals retain
ENTIRE images and are never replaced by reduced inverse-centre vanishing.

Blueprint: `hironaka-intrinsic-reduced-centre-open-sections.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Hironaka.HironakaIntrinsicReducedCentreOpenSections

open HironakaIntrinsicReducedCentreIdealSheaf

noncomputable section
universe u
variable {X Y : LocallyRingedSpace.{u}}

/-- Native actual stalk maps transport maximal-ideal membership exactly. -/
theorem stalkMap_mem_maximalIdeal_iff (F : X ⟶ Y) (x : X)
    (r : (Y.presheaf.stalk (F.base x)).carrier) :
    F.stalkMap x r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x).carrier ↔
      r ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk (F.base x)).carrier := by
  simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using
    not_congr (isUnit_map_iff (F.stalkMap x).hom r)

/-- The literal ORIGINAL F.c.app gives an actual intrinsic inverse-centre section. -/
def pullbackIntrinsicSection (F : X ⟶ Y) (C : Set Y) (V : Opens Y.toTopCat)
    (s : intrinsicReducedCentreSectionIdeal Y C V) :
    intrinsicReducedCentreSectionIdeal X (F.base ⁻¹' C) ((Opens.map F.base).obj V) := by
  refine ⟨F.c.app (op V) s.val, ?_⟩
  intro x hx hxC
  have hm := (stalkMap_mem_maximalIdeal_iff F x _).mpr (s.property (F.base x) hx hxC)
  exact (LocallyRingedSpace.stalkMap_germ_apply F V x hx s.val) ▸ hm

/-- SAME original full section map and original stalk/germ equality. -/
theorem pullbackIntrinsicSection_germ (F : X ⟶ Y) (C : Set Y) (V : Opens Y.toTopCat)
    (s : intrinsicReducedCentreSectionIdeal Y C V) (x : X) (hx : F.base x ∈ V) :
    X.presheaf.germ ((Opens.map F.base).obj V) x hx (pullbackIntrinsicSection F C V s).val =
      F.stalkMap x (Y.presheaf.germ V (F.base x) hx s.val) := by
  change X.presheaf.germ _ x hx (F.c.app (op V) s.val) = _
  exact (LocallyRingedSpace.stalkMap_germ_apply F V x hx s.val).symm

/-- The actual native OI inverse section has EXACTLY the original source germ. -/
theorem openImmersion_invApp_germ (j : X ⟶ Y) [H : LocallyRingedSpace.IsOpenImmersion j]
    (V : Opens X.toTopCat) (s : (X.presheaf.obj (op V)).carrier) (x : X) (hx : x ∈ V) :
    j.stalkMap x (Y.presheaf.germ
      ((LocallyRingedSpace.IsOpenImmersion.opensFunctor j).obj V) (j.base x)
      (show j.base x ∈ (LocallyRingedSpace.IsOpenImmersion.opensFunctor j).obj V from ⟨x, hx, rfl⟩)
      (LocallyRingedSpace.IsOpenImmersion.invApp j V s)) = X.presheaf.germ V x hx s := by
  let W := (LocallyRingedSpace.IsOpenImmersion.opensFunctor j).obj V
  have hxW : j.base x ∈ W := ⟨x, hx, rfl⟩
  have hV : (Opens.map j.base).obj W = V := by
    ext z
    change j.base z ∈ j.base '' (V : Set X) ↔ z ∈ V
    constructor
    · rintro ⟨w, hw, hwz⟩
      exact (H.base_open.injective hwz) ▸ hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  rw [LocallyRingedSpace.stalkMap_germ_apply]
  have he := ConcreteCategory.congr_hom (LocallyRingedSpace.IsOpenImmersion.invApp_app j V) s
  have he' : j.c.app (op W) (LocallyRingedSpace.IsOpenImmersion.invApp j V s) =
      X.presheaf.map (eqToHom hV).op s := by
    rw [ConcreteCategory.comp_apply] at he
    convert he using 1
    exact congrArg (fun i : op V ⟶ op ((Opens.map j.base).obj W) => X.presheaf.map i s)
      (Subsingleton.elim _ _)
  exact (congrArg (X.presheaf.germ ((Opens.map j.base).obj W) x hxW) he').trans
    (X.presheaf.germ_res_apply (eqToHom hV) x hxW s)

/-- A genuine source intrinsic section lifts by the SAME actual OI invApp
and remains an actual target intrinsic section, on the original image open. -/
def openImmersionIntrinsicSectionLift (j : X ⟶ Y) [LocallyRingedSpace.IsOpenImmersion j]
    (C : Set Y) (V : Opens X.toTopCat)
    (s : intrinsicReducedCentreSectionIdeal X (j.base ⁻¹' C) V) :
    intrinsicReducedCentreSectionIdeal Y C
      ((LocallyRingedSpace.IsOpenImmersion.opensFunctor j).obj V) := by
  refine ⟨LocallyRingedSpace.IsOpenImmersion.invApp j V s.val, ?_⟩
  rintro y ⟨x, hx, rfl⟩ hxC
  apply (stalkMap_mem_maximalIdeal_iff j x _).mp
  exact (openImmersion_invApp_germ j V s.val x hx).symm ▸ s.property x hx hxC

/-- The original native intrinsic lift preserves the EXACT whole original germ square. -/
theorem openImmersionIntrinsicSectionLift_germ (j : X ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion j] (C : Set Y) (V : Opens X.toTopCat)
    (s : intrinsicReducedCentreSectionIdeal X (j.base ⁻¹' C) V) (x : X) (hx : x ∈ V) :
    j.stalkMap x (Y.presheaf.germ
      ((LocallyRingedSpace.IsOpenImmersion.opensFunctor j).obj V) (j.base x)
      (show j.base x ∈ (LocallyRingedSpace.IsOpenImmersion.opensFunctor j).obj V from ⟨x, hx, rfl⟩)
      (openImmersionIntrinsicSectionLift j C V s).val) = X.presheaf.germ V x hx s.val := by
  change j.stalkMap x (Y.presheaf.germ _ _ _
    (LocallyRingedSpace.IsOpenImmersion.invApp j V s.val)) = _
  exact openImmersion_invApp_germ j V s.val x hx

end
end Hironaka.HironakaIntrinsicReducedCentreOpenSections
