import Hironaka.Resolution.HironakaSingularModuleSheafStalk
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Actual pulled image ideals on arbitrary ORIGINAL locally ringed spaces

For SAME original F:X→Y and actual native b:B→unit O_Y, J_x is EXACTLY
Ideal.map F.stalkMap of the native actual b-stalk range. Literal original
sections test their original germs against that SAME J_x. Native unit.Submodule
and original structure-sheaf gluing give a genuine actual ideal module sheaf.
For ordinary componentwise-injective b this is the standard pulled ideal;
the construction works more generally for any actual b's image ideal.
No ambient map/model, supplied dictionary, radicalization or new space category.

Blueprint: `hironaka-native-pulled-ideal-sheaf.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Hironaka.HironakaNativePulledIdealSheaf

open HironakaSingularModuleSheafStalk

noncomputable section
universe u
variable {X Y : LocallyRingedSpace.{u}}
    (F : X ⟶ Y) (B : SheafOfModules.{u} (forgetRing Y.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit (forgetRing Y.toSheafedSpace.sheaf))

/-- EXACT entire original stalk ideal image, with SAME native b-stalk map. -/
abbrev nativePulledIdealStalkIdeal (x : X) : Ideal (X.presheaf.stalk x).carrier :=
  Ideal.map (F.stalkMap x).hom
    (LinearMap.range (stalkInclusionLinearMap Y.toSheafedSpace.sheaf B b (F.base x)))

/-- Literal ORIGINAL sections with every ORIGINAL germ in the SAME entire ideal. -/
def nativePulledIdealSectionIdeal (U : Opens X.toTopCat) :
    Ideal (X.presheaf.obj (op U)).carrier where
  carrier := {s | ∀ (x : X) (hx : x ∈ U),
    X.presheaf.germ U x hx s ∈ nativePulledIdealStalkIdeal F B b x}
  zero_mem' := by
    intro x hx
    rw [map_zero]
    exact Ideal.zero_mem _
  add_mem' := by
    intro s t hs ht x hx
    rw [map_add]
    exact Ideal.add_mem _ (hs x hx) (ht x hx)
  smul_mem' := by
    intro r s hs x hx
    change X.presheaf.germ U x hx (r * s) ∈ _
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ (hs x hx)

/-- ORIGINAL germ restriction retains the SAME entire pulled image ideal. -/
theorem nativePulledIdealSectionIdeal_restrict (U V : Opens X.toTopCat) (hUV : U ≤ V)
    (s : (X.presheaf.obj (op V)).carrier) (hs : s ∈ nativePulledIdealSectionIdeal F B b V) :
    X.presheaf.map (homOfLE hUV).op s ∈ nativePulledIdealSectionIdeal F B b U := by
  intro x hx
  rw [X.presheaf.germ_res_apply (homOfLE hUV) x hx s]
  exact hs x (hUV hx)

/-- Native original unit submodule; no module operations or scalar actions copied. -/
def nativePulledIdealSubmodule :
    (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).Submodule where
  obj U := nativePulledIdealSectionIdeal F B b (unop U)
  map f := by
    intro s hs
    exact nativePulledIdealSectionIdeal_restrict F B b _ _ (leOfHom f.unop) s hs

/-- The SAME actual section ideals with native unit-presheaf operations. -/
def nativePulledIdealModulePresheaf :
    PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
  (nativePulledIdealSubmodule F B b).toPresheafOfModules

@[simp] theorem nativePulledIdealModulePresheaf_map_val
    {U V : (Opens X.toTopCat)ᵒᵖ} (f : U ⟶ V)
    (s : nativePulledIdealSectionIdeal F B b (unop U)) :
    (((nativePulledIdealModulePresheaf F B b).presheaf.map f s) :
      nativePulledIdealSectionIdeal F B b (unop V)).val = X.presheaf.map f s.val := rfl

/-- The ORIGINAL structure-sheaf gluing proves this actual module presheaf is a sheaf. -/
theorem nativePulledIdealModulePresheaf_isSheaf :
    TopCat.Presheaf.IsSheaf (X := X.toTopCat) (nativePulledIdealModulePresheaf F B b).presheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (X := X.toTopCat) _).mpr
  intro ι U sf hcpt
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf U (fun i => (sf i).val) := by
    intro i j
    exact congrArg Subtype.val (hcpt i j)
  obtain ⟨s, hglue, huniq⟩ := X.toSheafedSpace.IsSheaf.isSheafUniqueGluing U
    (fun i => (sf i).val) hcompat
  have hs : s ∈ nativePulledIdealSectionIdeal F B b (iSup U) := by
    intro x hx
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
    have hg := congrArg (X.presheaf.germ (U i) x hxi) (hglue i)
    rw [X.presheaf.germ_res_apply] at hg
    rw [hg]
    exact (sf i).property x hxi
  refine ⟨⟨s, hs⟩, ?_, ?_⟩
  · intro i
    apply Subtype.ext
    exact hglue i
  · intro t ht
    apply Subtype.ext
    apply huniq t.val
    intro i
    exact congrArg Subtype.val (ht i)

/-- Actual native module subsheaf of ORIGINAL O_X, without ambient presentation. -/
def nativePulledIdealModule : SheafOfModules.{u} (forgetRing X.toSheafedSpace.sheaf) where
  val := nativePulledIdealModulePresheaf F B b
  isSheaf := nativePulledIdealModulePresheaf_isSheaf F B b

/-- The SAME literal original section subtype inclusion. -/
def nativePulledIdealInclusion : nativePulledIdealModule F B b ⟶ SheafOfModules.unit _ :=
  ⟨(nativePulledIdealSubmodule F B b).ι⟩

@[simp] theorem nativePulledIdealInclusion_app (U : Opens X.toTopCat)
    (s : nativePulledIdealSectionIdeal F B b U) :
    (nativePulledIdealInclusion F B b).val.app (op U) s = s.val := rfl

instance nativePulledIdealInclusion_mono : Mono (nativePulledIdealInclusion F B b) := by
  have hmono : Mono ((SheafOfModules.forget _).map (nativePulledIdealInclusion F B b)) := by
    change Mono (nativePulledIdealSubmodule F B b).ι
    infer_instance
  exact (SheafOfModules.forget _).mono_of_mono_map hmono

/-- Literal SAME F.c.app of an actual original b.app section is an actual J section. -/
def nativePulledIdealSection (V : Opens Y.toTopCat) (t : B.val.obj (op V)) :
    nativePulledIdealSectionIdeal F B b ((Opens.map F.base).obj V) := by
  refine ⟨F.c.app (op V) (b.val.app (op V) t), ?_⟩
  intro x hx
  have hm : Y.presheaf.germ V (F.base x) hx (b.val.app (op V) t) ∈
      LinearMap.range (stalkInclusionLinearMap Y.toSheafedSpace.sheaf B b (F.base x)) :=
    ⟨TopCat.Presheaf.germ B.val.presheaf V (F.base x) hx t,
      stalkInclusionLinearMap_germ Y.toSheafedSpace.sheaf B b (F.base x) V hx t⟩
  have hmap : F.stalkMap x (Y.presheaf.germ V (F.base x) hx (b.val.app (op V) t)) ∈
      nativePulledIdealStalkIdeal F B b x := Ideal.mem_map_of_mem (F.stalkMap x).hom hm
  exact (LocallyRingedSpace.stalkMap_germ_apply F V x hx (b.val.app (op V) t)) ▸ hmap

/-- Every literal pulled actual section retains the ORIGINAL full stalk/germ identity. -/
theorem nativePulledIdealSection_germ (V : Opens Y.toTopCat) (t : B.val.obj (op V))
    (x : X) (hx : F.base x ∈ V) :
    X.presheaf.germ ((Opens.map F.base).obj V) x hx (nativePulledIdealSection F B b V t).val =
      F.stalkMap x (Y.presheaf.germ V (F.base x) hx (b.val.app (op V) t)) := by
  change X.presheaf.germ _ x hx (F.c.app (op V) (b.val.app (op V) t)) = _
  exact (LocallyRingedSpace.stalkMap_germ_apply F V x hx (b.val.app (op V) t)).symm

/-- The SAME formula through the genuine native target inclusion-stalk map. -/
theorem nativePulledIdealSection_germ_native (V : Opens Y.toTopCat) (t : B.val.obj (op V))
    (x : X) (hx : F.base x ∈ V) :
    X.presheaf.germ ((Opens.map F.base).obj V) x hx (nativePulledIdealSection F B b V t).val =
      F.stalkMap x (stalkInclusionLinearMap Y.toSheafedSpace.sheaf B b (F.base x)
        (TopCat.Presheaf.germ B.val.presheaf V (F.base x) hx t)) :=
  (nativePulledIdealSection_germ F B b V t x hx).trans
    (congrArg (F.stalkMap x).hom
      (stalkInclusionLinearMap_germ Y.toSheafedSpace.sheaf B b (F.base x) V hx t).symm)

end
end Hironaka.HironakaNativePulledIdealSheaf
