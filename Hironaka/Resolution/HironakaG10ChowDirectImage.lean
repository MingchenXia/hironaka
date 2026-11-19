import Hironaka.Resolution.HironakaSingularModuleSheafStalk
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# The direct image of the structure sheaf as a native module

For a morphism `f : Y ⟶ X` of locally ringed spaces, the direct image `f_* 𝒪_Y` is a
sheaf of `𝒪_X`-modules (Mathlib's `SheafOfModules.pushforward` of the unit module along
the ring-sheaf morphism `f^♯`).  Its stalk at `f y` is identified, `𝒪_{X,f y}`-linearly,
with the stalk `𝒪_{Y,y}` (an `𝒪_{X,f y}`-module through the stalk map of `f`) as soon as
the point map of `f` is inducing, e.g. a homeomorphism.

This is the native object of the finite mapping theorem used by the Chow-side lemma
`chow:flat-bimeromorphic-iso` (blueprint `hironaka-g10-chowside-flat-iso.tex`).

Main declarations:

* `ringHom f` — the morphism of ring sheaves `𝒪_X ⟶ f_* 𝒪_Y`.
* `directImage f` — `f_* 𝒪_Y` as a native sheaf of `𝒪_X`-modules.
* `stalkAddHom f y` and `stalkAddHom_germ` — the additive stalk comparison and its germ formula.
* `stalkAlgebra f y` — `𝒪_{Y,y}` as an `𝒪_{X,f y}`-algebra through the stalk map.
* `stalkLinearEquiv f y hf` — the linear stalk identification for inducing point maps.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hironaka.HironakaG10ChowDirectImage

open HironakaSingularModuleSheafStalk

universe u

variable {X Y : LocallyRingedSpace.{u}} (f : Y ⟶ X)

/-- The morphism of ring sheaves `𝒪_X ⟶ f_* 𝒪_Y` attached to `f`. -/
def ringHom : forgetRing X.toSheafedSpace.sheaf ⟶
    ((Opens.map f.base).sheafPushforwardContinuous RingCat.{u} _ _).obj
      (forgetRing Y.toSheafedSpace.sheaf) where
  hom := Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)

/-- **The direct image `f_* 𝒪_Y` as a native sheaf of `𝒪_X`-modules.** -/
def directImage : SheafOfModules.{u} (forgetRing X.toSheafedSpace.sheaf) :=
  (SheafOfModules.pushforward.{u} (ringHom f)).obj
    (SheafOfModules.unit (forgetRing Y.toSheafedSpace.sheaf))

/-- The sections of `f_* 𝒪_Y` over `U` are the sections of `𝒪_Y` over `f⁻¹ U`. -/
theorem directImage_obj (U : Opens X) :
    ((directImage f).val.obj (op U) : Type u) = (Y.presheaf.obj (op ((Opens.map f.base).obj U))) :=
  rfl

/-- The additive presheaf of `𝒪_Y`. -/
abbrev unitPresheaf : TopCat.Presheaf AddCommGrpCat.{u} Y.toTopCat :=
  (SheafOfModules.unit (forgetRing Y.toSheafedSpace.sheaf)).val.presheaf

/-- The additive presheaf of `f_* 𝒪_Y` is the pushforward of that of `𝒪_Y`. -/
theorem directImage_presheaf :
    (directImage f).val.presheaf = f.base _* (unitPresheaf (Y := Y)) :=
  rfl

/-- The additive comparison `(f_* 𝒪_Y)_{f y} → 𝒪_{Y,y}`. -/
def stalkAddHom (y : Y) :
    ↑(TopCat.Presheaf.stalk (directImage f).val.presheaf (f.base y)) →+ ↑(Y.presheaf.stalk y) :=
  (unitStalkLinearEquiv Y.toSheafedSpace.sheaf y).toAddEquiv.toAddMonoidHom.comp
    (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.base (unitPresheaf (Y := Y)) y).hom

theorem stalkAddHom_germ (y : Y) (U : Opens X) (hy : f.base y ∈ U)
    (m : (directImage f).val.obj (op U)) :
    stalkAddHom f y (TopCat.Presheaf.germ (directImage f).val.presheaf U (f.base y) hy m) =
      Y.presheaf.germ ((Opens.map f.base).obj U) y hy m := by
  have h := ConcreteCategory.congr_hom
    (TopCat.Presheaf.stalkPushforward_germ AddCommGrpCat.{u} f.base (unitPresheaf (Y := Y)) U y hy) m
  change (unitStalkLinearEquiv Y.toSheafedSpace.sheaf y)
    ((TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.base (unitPresheaf (Y := Y)) y).hom
      (TopCat.Presheaf.germ (directImage f).val.presheaf U (f.base y) hy m)) = _
  erw [h]
  exact unitStalkLinearEquiv_germ Y.toSheafedSpace.sheaf y _ hy m

theorem stalkAddHom_bijective (y : Y) (hf : Topology.IsInducing f.base) :
    Function.Bijective (stalkAddHom f y) := by
  have : IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.base
      (unitPresheaf (Y := Y)) y) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing (C := AddCommGrpCat.{u}) hf _ y
  exact (unitStalkLinearEquiv Y.toSheafedSpace.sheaf y).bijective.comp
    (asIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.base
      (unitPresheaf (Y := Y)) y)).addCommGroupIsoToAddEquiv.bijective

/-- `𝒪_{Y,y}` as an `𝒪_{X,f y}`-module through the stalk map of `f`. -/
abbrev stalkAlgebra (y : Y) :
    Algebra ↑(TopCat.Presheaf.stalk X.toSheafedSpace.sheaf.obj (f.base y)) (Y.presheaf.stalk y) :=
  (f.stalkMap y).hom.toAlgebra

/-- The module structure of `stalkAlgebra` (the one used by `RingHom.Flat`). -/
abbrev stalkModule (y : Y) :
    Module ↑(TopCat.Presheaf.stalk X.toSheafedSpace.sheaf.obj (f.base y)) (Y.presheaf.stalk y) :=
  (stalkAlgebra f y).toModule

theorem stalkAddHom_smul (y : Y)
    (r : ↑(TopCat.Presheaf.stalk X.toSheafedSpace.sheaf.obj (f.base y)))
    (m : ↑(TopCat.Presheaf.stalk (directImage f).val.presheaf (f.base y))) :
    stalkAddHom f y (r • m) = (f.stalkMap y).hom r * stalkAddHom f y m := by
  obtain ⟨U, hxU, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq (directImage f).val.presheaf m
  obtain ⟨V, hVU, hxV, r, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq X.presheaf r hxU
  rw [← TopCat.Presheaf.germ_res_apply (directImage f).val.presheaf (homOfLE hVU) (f.base y) hxV m]
  erw [← PresheafOfModules.germ_smul (R := X.presheaf)]
  refine (stalkAddHom_germ f y V hxV _).trans ?_
  erw [stalkAddHom_germ f y V hxV, LocallyRingedSpace.stalkMap_germ_apply, ← map_mul]
  rfl

/-- **Stalks of the direct image.**  If the point map of `f` is inducing (e.g. a
homeomorphism), the stalk of `f_* 𝒪_Y` at `f y` is `𝒪_{X,f y}`-linearly isomorphic to
`𝒪_{Y,y}`, with its module structure through the stalk map of `f`. -/
def stalkLinearEquiv (y : Y) (hf : Topology.IsInducing f.base) :
    letI := stalkModule f y
    ↑(TopCat.Presheaf.stalk (directImage f).val.presheaf (f.base y))
      ≃ₗ[↑(TopCat.Presheaf.stalk X.toSheafedSpace.sheaf.obj (f.base y))] Y.presheaf.stalk y :=
  letI := stalkModule f y
  { Equiv.ofBijective (stalkAddHom f y) (stalkAddHom_bijective f y hf) with
    map_add' := map_add (stalkAddHom f y)
    map_smul' := stalkAddHom_smul f y }

end Hironaka.HironakaG10ChowDirectImage
