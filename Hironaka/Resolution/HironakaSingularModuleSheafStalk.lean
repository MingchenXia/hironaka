import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Topology.Sheaves.Module
import Mathlib.RingTheory.PicardGroup

/-!
# Original native module-sheaf stalks

The scalar action throughout is Mathlib's native CommRingCat module-stalk action.
Local-free rank-one data will produce invertibility of the same original stalk,
without assuming a stalk trivialization or a replacement stalk dictionary.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat.Presheaf

namespace Hironaka.HironakaSingularModuleSheafStalk

universe u

variable {X : TopCat.{u}}

/-- The native ring-valued forgetful image of the actual commutative-ring sheaf. -/
abbrev forgetRing (R : X.Sheaf CommRingCat.{u}) : X.Sheaf RingCat.{u} :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat)).obj R

section Presheaf

variable {R : X.Presheaf CommRingCat.{u}}
  {M N P : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}

/-- Native additive stalk maps are linear for the native original ring-stalk action. -/
def stalkLinearMap (f : M ⟶ N) (x : X) :
    ↑(TopCat.Presheaf.stalk M.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R x)] ↑(TopCat.Presheaf.stalk N.presheaf x) where
  toFun := (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((PresheafOfModules.toPresheaf _).map f)
  map_add' := map_add _
  map_smul' r m := by
    obtain ⟨U, hxU, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
    obtain ⟨V, hVU, hxV, r, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq R r hxU
    rw [← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE hVU) x hxV m]
    simp only [RingHom.id_apply]
    erw [← M.germ_smul (R := R), TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply, ← N.germ_smul]
    congr 1
    exact (f.app (op V)).hom.map_smul r _

@[simp]
theorem stalkLinearMap_germ (f : M ⟶ N) (x : X) (U : Opens X) (hx : x ∈ U)
    (m : M.obj (op U)) :
    stalkLinearMap f x (TopCat.Presheaf.germ M.presheaf U x hx m) =
      TopCat.Presheaf.germ N.presheaf U x hx (f.app (op U) m) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    ((PresheafOfModules.toPresheaf _).map f) m

@[simp]
theorem stalkLinearMap_id (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (x : X) :
    stalkLinearMap (𝟙 M) x = LinearMap.id := by
  ext m
  obtain ⟨U, hx, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
  erw [stalkLinearMap_germ]
  rfl

@[simp]
theorem stalkLinearMap_comp (f : M ⟶ N) (g : N ⟶ P) (x : X) :
    stalkLinearMap (f ≫ g) x = (stalkLinearMap g x).comp (stalkLinearMap f x) := by
  ext m
  obtain ⟨U, hx, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
  simp only [LinearMap.comp_apply]
  erw [stalkLinearMap_germ, stalkLinearMap_germ, stalkLinearMap_germ]
  rfl

/-- A genuine native module-presheaf isomorphism on its same original stalks. -/
def stalkLinearEquiv (e : M ≅ N) (x : X) :
    ↑(TopCat.Presheaf.stalk M.presheaf x) ≃ₗ[↑(TopCat.Presheaf.stalk R x)] ↑(TopCat.Presheaf.stalk N.presheaf x) :=
  LinearEquiv.ofLinearMap (stalkLinearMap e.hom x) (stalkLinearMap e.inv x)
    (by rw [← stalkLinearMap_comp, e.inv_hom_id, stalkLinearMap_id])
    (by rw [← stalkLinearMap_comp, e.hom_inv_id, stalkLinearMap_id])

end Presheaf

variable (R : X.Sheaf CommRingCat.{u})

/-- Forward the existing native CommRingCat action through the forget-ring sheaf expression.
This is definitionally the native action, with no replacement scalar structure. -/
abbrev nativeSheafStalkModule (M : SheafOfModules.{u} (forgetRing R)) (x : X) :
    Module ↑(TopCat.Presheaf.stalk R.obj x) ↑(TopCat.Presheaf.stalk M.val.presheaf x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := R.obj) M.val x

attribute [instance] nativeSheafStalkModule

private def unitStalkAddIso (x : X) :
    TopCat.Presheaf.stalk (SheafOfModules.unit (forgetRing R)).val.presheaf x ≅
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).obj (TopCat.Presheaf.stalk R.obj x) :=
  (preservesColimitIso (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
    ((OpenNhds.inclusion x).op ⋙ R.obj)).symm

private theorem unitStalkAddIso_germ (x : X) (U : Opens X) (hx : x ∈ U)
    (r : R.obj.obj (op U)) :
    (unitStalkAddIso R x).hom
      (TopCat.Presheaf.germ (SheafOfModules.unit (forgetRing R)).val.presheaf U x hx r) =
        TopCat.Presheaf.germ R.obj U x hx r := by
  exact ConcreteCategory.congr_hom
    (ι_preservesColimitIso_inv (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
      ((OpenNhds.inclusion x).op ⋙ R.obj) (op ⟨U, hx⟩)) r

/-- The SAME native unit module stalk, linearly identified with the original ring stalk. -/
def unitStalkLinearEquiv (x : X) :
    ↑(TopCat.Presheaf.stalk (SheafOfModules.unit (forgetRing R)).val.presheaf x) ≃ₗ[↑(TopCat.Presheaf.stalk R.obj x)]
      ↑(TopCat.Presheaf.stalk R.obj x) :=
  { (unitStalkAddIso R x).addCommGroupIsoToAddEquiv with
    map_smul' := by
      intro r m
      obtain ⟨U, hxU, m, rfl⟩ :=
        TopCat.Presheaf.exists_germ_eq (SheafOfModules.unit (forgetRing R)).val.presheaf m
      obtain ⟨V, hVU, hxV, r, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq R.obj r hxU
      rw [← TopCat.Presheaf.germ_res_apply (SheafOfModules.unit (forgetRing R)).val.presheaf
        (homOfLE hVU) x hxV m]
      erw [← PresheafOfModules.germ_smul (R := R.obj)]
      change (unitStalkAddIso R x).hom _ =
        (TopCat.Presheaf.germ R.obj V x hxV r) *
          (show ↑(TopCat.Presheaf.stalk R.obj x) from (unitStalkAddIso R x).hom _)
      rw [unitStalkAddIso_germ, unitStalkAddIso_germ]
      exact (TopCat.Presheaf.germ R.obj V x hxV).hom.map_mul r _ }

@[simp]
theorem unitStalkLinearEquiv_germ (x : X) (U : Opens X) (hx : x ∈ U)
    (r : R.obj.obj (op U)) :
    unitStalkLinearEquiv R x
      (TopCat.Presheaf.germ (SheafOfModules.unit (forgetRing R)).val.presheaf U x hx r) =
        TopCat.Presheaf.germ R.obj U x hx r :=
  unitStalkAddIso_germ R x U hx r

/-- The original native inclusion stalk map into the ORIGINAL commutative ring stalk. -/
def stalkInclusionLinearMap (M : SheafOfModules.{u} (forgetRing R))
    (f : M ⟶ SheafOfModules.unit (forgetRing R)) (x : X) :
    ↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R.obj x)] ↑(TopCat.Presheaf.stalk R.obj x) :=
  (unitStalkLinearEquiv R x).toLinearMap.comp (stalkLinearMap f.val x)

@[simp]
theorem stalkInclusionLinearMap_germ (M : SheafOfModules.{u} (forgetRing R))
    (f : M ⟶ SheafOfModules.unit (forgetRing R)) (x : X)
    (U : Opens X) (hx : x ∈ U) (m : M.val.obj (op U)) :
    stalkInclusionLinearMap R M f x (TopCat.Presheaf.germ M.val.presheaf U x hx m) =
      TopCat.Presheaf.germ R.obj U x hx (f.val.app (op U) m) := by
  change unitStalkLinearEquiv R x (stalkLinearMap f.val x _) = _
  erw [stalkLinearMap_germ, unitStalkLinearEquiv_germ]
  rfl

theorem stalkInclusionLinearMap_injective (M : SheafOfModules.{u} (forgetRing R))
    (f : M ⟶ SheafOfModules.unit (forgetRing R))
    (hf : ∀ U : Opens X, Function.Injective (f.val.app (op U))) (x : X) :
    Function.Injective (stalkInclusionLinearMap R M f x) :=
  (unitStalkLinearEquiv R x).injective.comp
    (TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
      (f := (PresheafOfModules.toPresheaf _).map f.val) hf x)

end Hironaka.HironakaSingularModuleSheafStalk
