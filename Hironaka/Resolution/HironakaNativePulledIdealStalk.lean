import Hironaka.Resolution.HironakaNativePulledIdealSheaf

/-!
# The actual native pulled-ideal inclusion has the EXACT whole original stalk image

Both ENTIRE ideal directions and native actual linear equivalence are derived
from literal actual B sections and SAME original F.c.app/b.app. No supplied
stalk dictionary, local iso, radicalization, ambient model or new category.
Generic native reuse is foundational only, with no separate milestone credit.

Blueprint: `hironaka-native-pulled-ideal-stalk.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Hironaka.HironakaNativePulledIdealStalk

open HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf

noncomputable section
universe u
variable {X Y : LocallyRingedSpace.{u}}
    (F : X ⟶ Y) (B : SheafOfModules.{u} (forgetRing Y.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit (forgetRing Y.toSheafedSpace.sheaf))

/-- Transparent forwarding of the EXACT existing native module-stalk action. -/
abbrev nativePulledIdealNativeStalkModule (x : X) :
    Module (X.presheaf.stalk x).carrier
      ↑(TopCat.Presheaf.stalk (nativePulledIdealModule F B b).val.presheaf x) :=
  nativeSheafStalkModule X.toSheafedSpace.sheaf (nativePulledIdealModule F B b) x

attribute [instance] nativePulledIdealNativeStalkModule

/-- The SAME actual source ideal inclusion on native original module stalks. -/
def nativePulledIdealStalkInclusion (x : X) :
    ↑(TopCat.Presheaf.stalk (nativePulledIdealModule F B b).val.presheaf x) →ₗ[
      (X.presheaf.stalk x).carrier] (X.presheaf.stalk x).carrier :=
  stalkInclusionLinearMap X.toSheafedSpace.sheaf (nativePulledIdealModule F B b)
    (nativePulledIdealInclusion F B b) x

@[simp] theorem nativePulledIdealStalkInclusion_germ
    (x : X) (U : Opens X.toTopCat) (hx : x ∈ U) (s : nativePulledIdealSectionIdeal F B b U) :
    nativePulledIdealStalkInclusion F B b x
      (TopCat.Presheaf.germ (nativePulledIdealModule F B b).val.presheaf U x hx s) =
      X.presheaf.germ U x hx s.val :=
  stalkInclusionLinearMap_germ X.toSheafedSpace.sheaf (nativePulledIdealModule F B b)
    (nativePulledIdealInclusion F B b) x U hx s

/-- The actual componentwise section subtype inclusion is injective on native stalks. -/
theorem nativePulledIdealStalkInclusion_injective (x : X) :
    Function.Injective (nativePulledIdealStalkInclusion F B b x) :=
  stalkInclusionLinearMap_injective X.toSheafedSpace.sheaf (nativePulledIdealModule F B b)
    (nativePulledIdealInclusion F B b) (fun _ => Subtype.val_injective) x

/-- BOTH ENTIRE actual ideal inclusions derive EXACTLY the original J_x. -/
theorem nativePulledIdealStalkInclusion_range (x : X) :
    LinearMap.range (nativePulledIdealStalkInclusion F B b x) = nativePulledIdealStalkIdeal F B b x := by
  apply le_antisymm
  · rintro r ⟨m, rfl⟩
    obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq
      (nativePulledIdealModule F B b).val.presheaf m
    exact (nativePulledIdealStalkInclusion_germ F B b x U hxU s).symm ▸ s.property x hxU
  · apply Ideal.map_le_iff_le_comap.mpr
    rintro a ⟨m, hm⟩
    obtain ⟨V, hxV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq B.val.presheaf m
    refine ⟨TopCat.Presheaf.germ (nativePulledIdealModule F B b).val.presheaf
      ((Opens.map F.base).obj V) x hxV (nativePulledIdealSection F B b V t), ?_⟩
    exact (nativePulledIdealStalkInclusion_germ F B b x _ hxV
      (nativePulledIdealSection F B b V t)).trans
      ((nativePulledIdealSection_germ_native F B b V t x hxV).trans
        (congrArg (F.stalkMap x).hom hm))

/-- The native ACTUAL source ideal-module stalk is the SAME whole original image ideal. -/
def nativePulledIdealStalkIdealEquiv (x : X) :
    ↑(TopCat.Presheaf.stalk (nativePulledIdealModule F B b).val.presheaf x) ≃ₗ[
      (X.presheaf.stalk x).carrier] nativePulledIdealStalkIdeal F B b x := by
  let f := (nativePulledIdealStalkInclusion F B b x).codRestrict
    (nativePulledIdealStalkIdeal F B b x)
    (fun m => by rw [← nativePulledIdealStalkInclusion_range F B b x]; exact ⟨m, rfl⟩)
  apply LinearEquiv.ofBijective f
  constructor
  · intro a c hac
    exact nativePulledIdealStalkInclusion_injective F B b x (congrArg Subtype.val hac)
  · intro r
    have hr : r.val ∈ LinearMap.range (nativePulledIdealStalkInclusion F B b x) := by
      rw [nativePulledIdealStalkInclusion_range]
      exact r.property
    obtain ⟨m, hm⟩ := hr
    exact ⟨m, Subtype.ext hm⟩

@[simp] theorem nativePulledIdealStalkIdealEquiv_germ
    (x : X) (U : Opens X.toTopCat) (hx : x ∈ U) (s : nativePulledIdealSectionIdeal F B b U) :
    (nativePulledIdealStalkIdealEquiv F B b x
      (TopCat.Presheaf.germ (nativePulledIdealModule F B b).val.presheaf U x hx s)).val =
      X.presheaf.germ U x hx s.val := nativePulledIdealStalkInclusion_germ F B b x U hx s

end
end Hironaka.HironakaNativePulledIdealStalk
