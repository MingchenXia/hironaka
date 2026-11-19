import Hironaka.Resolution.HironakaSingularModuleSheafStalk
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# The intrinsic REDUCED-centre ideal on the ORIGINAL locally ringed space

Literal original sections have germ in the native local-ring maximal ideal
at EVERY original centre point. Native unit.Submodule supplies all module
operations/restrictions/inclusion, and original structure-sheaf gluing proves
it is an actual sheaf. No ambient map, model choice, SC or new space category.
This is the REDUCED-centre ideal, not a general nonradical coherent ideal.

Blueprint: `hironaka-intrinsic-reduced-centre-ideal-sheaf.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Hironaka.HironakaIntrinsicReducedCentreIdealSheaf

open HironakaSingularModuleSheafStalk

noncomputable section

universe u
variable (X : LocallyRingedSpace.{u})

/-- ORIGINAL sections with native residue zero at EVERY ORIGINAL centre point. -/
def intrinsicReducedCentreSectionIdeal (C : Set X) (U : Opens X.toTopCat) :
    Ideal (X.presheaf.obj (op U)).carrier where
  carrier := {s | ∀ (x : X) (hx : x ∈ U), x ∈ C →
    X.presheaf.germ U x hx s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x).carrier}
  zero_mem' := by
    intro x hx _hC
    rw [map_zero]
    exact Ideal.zero_mem _
  add_mem' := by
    intro s t hs ht x hx hC
    rw [map_add]
    exact Ideal.add_mem _ (hs x hx hC) (ht x hx hC)
  smul_mem' := by
    intro r s hs x hx hC
    change X.presheaf.germ U x hx (r * s) ∈ _
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ (hs x hx hC)

@[simp] theorem mem_intrinsicReducedCentreSectionIdeal (C : Set X) (U : Opens X.toTopCat)
    (s : (X.presheaf.obj (op U)).carrier) :
    s ∈ intrinsicReducedCentreSectionIdeal X C U ↔
      ∀ (x : X) (hx : x ∈ U), x ∈ C →
        X.presheaf.germ U x hx s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x).carrier := Iff.rfl

/-- The SAME native maximal-ideal condition is preserved by ORIGINAL restriction. -/
theorem intrinsicReducedCentreSectionIdeal_restrict (C : Set X)
    (U V : Opens X.toTopCat) (hUV : U ≤ V) (s : (X.presheaf.obj (op V)).carrier)
    (hs : s ∈ intrinsicReducedCentreSectionIdeal X C V) :
    X.presheaf.map (homOfLE hUV).op s ∈ intrinsicReducedCentreSectionIdeal X C U := by
  intro x hx hC
  rw [X.presheaf.germ_res_apply (homOfLE hUV) x hx s]
  exact hs x (hUV hx) hC

/-- This actual ideal is the REDUCED-centre ideal: its section ideals are radical. -/
theorem intrinsicReducedCentreSectionIdeal_isRadical (C : Set X) (U : Opens X.toTopCat) :
    (intrinsicReducedCentreSectionIdeal X C U).IsRadical := by
  rintro s ⟨k, hk⟩ x hx hC
  have hg := hk x hx hC
  rw [map_pow] at hg
  exact Ideal.IsPrime.isRadical (inferInstanceAs
    ((IsLocalRing.maximalIdeal (X.presheaf.stalk x).carrier).IsPrime)) ⟨k, hg⟩

/-- Native submodule of the ORIGINAL unit presheaf; no module operations copied. -/
def intrinsicReducedCentreSubmodule (C : Set X) :
    (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).Submodule where
  obj U := intrinsicReducedCentreSectionIdeal X C (unop U)
  map f := by
    intro s hs
    exact intrinsicReducedCentreSectionIdeal_restrict X C _ _ (leOfHom f.unop) s hs

/-- The SAME literal actual section ideals with native restriction/scalar operations. -/
def intrinsicReducedCentreModulePresheaf (C : Set X) :
    PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
  (intrinsicReducedCentreSubmodule X C).toPresheafOfModules

@[simp] theorem intrinsicReducedCentreModulePresheaf_map_val (C : Set X)
    {U V : (Opens X.toTopCat)ᵒᵖ} (f : U ⟶ V)
    (s : intrinsicReducedCentreSectionIdeal X C (unop U)) :
    (((intrinsicReducedCentreModulePresheaf X C).presheaf.map f s) :
      intrinsicReducedCentreSectionIdeal X C (unop V)).val = X.presheaf.map f s.val := rfl

/-- ORIGINAL structure-sheaf gluing proves these actual ideal sections form a sheaf. -/
theorem intrinsicReducedCentreModulePresheaf_isSheaf (C : Set X) :
    TopCat.Presheaf.IsSheaf (X := X.toTopCat) (intrinsicReducedCentreModulePresheaf X C).presheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (X := X.toTopCat) _).mpr
  intro ι U sf hcpt
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf U (fun i => (sf i).val) := by
    intro i j
    exact congrArg Subtype.val (hcpt i j)
  obtain ⟨s, hglue, huniq⟩ := X.toSheafedSpace.IsSheaf.isSheafUniqueGluing U
    (fun i => (sf i).val) hcompat
  have hs : s ∈ intrinsicReducedCentreSectionIdeal X C (iSup U) := by
    intro x hx hC
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
    have hg := congrArg (X.presheaf.germ (U i) x hxi) (hglue i)
    rw [X.presheaf.germ_res_apply] at hg
    rw [hg]
    exact (sf i).property x hxi hC
  refine ⟨⟨s, hs⟩, ?_, ?_⟩
  · intro i
    apply Subtype.ext
    exact hglue i
  · intro t ht
    apply Subtype.ext
    apply huniq t.val
    intro i
    exact congrArg Subtype.val (ht i)

/-- The intrinsic reduced-centre ideal as an ACTUAL native module subsheaf on ORIGINAL X. -/
def intrinsicReducedCentreIdealModule (C : Set X) :
    SheafOfModules (forgetRing X.toSheafedSpace.sheaf) where
  val := intrinsicReducedCentreModulePresheaf X C
  isSheaf := intrinsicReducedCentreModulePresheaf_isSheaf X C

/-- The actual inclusion is the SAME original literal section subtype. -/
def intrinsicReducedCentreIdealInclusion (C : Set X) :
    intrinsicReducedCentreIdealModule X C ⟶ SheafOfModules.unit _ :=
  ⟨(intrinsicReducedCentreSubmodule X C).ι⟩

@[simp] theorem intrinsicReducedCentreIdealInclusion_app (C : Set X)
    (U : Opens X.toTopCat) (s : intrinsicReducedCentreSectionIdeal X C U) :
    (intrinsicReducedCentreIdealInclusion X C).val.app (op U) s = s.val := rfl

instance intrinsicReducedCentreIdealInclusion_mono (C : Set X) :
    Mono (intrinsicReducedCentreIdealInclusion X C) := by
  have hmono : Mono ((SheafOfModules.forget _).map (intrinsicReducedCentreIdealInclusion X C)) := by
    change Mono (intrinsicReducedCentreSubmodule X C).ι
    infer_instance
  exact (SheafOfModules.forget _).mono_of_mono_map hmono

end

end Hironaka.HironakaIntrinsicReducedCentreIdealSheaf
