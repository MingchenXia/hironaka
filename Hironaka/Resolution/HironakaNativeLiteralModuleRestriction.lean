import Hironaka.Resolution.HironakaSingularModuleSheafStalk
import Mathlib.Geometry.RingedSpace.OpenImmersion
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward

/-!
# Genuine native module restriction to the LITERAL original X.restrict U

Existing native pushforward₀OfCommRingCat supplies all module operations,
actions and maps; original open-embedding sheaf restriction supplies sheafness.
The original unit and actual ideal inclusions retain literal component values.
No copied scalar actions, ambient model, new space category or certificate.

Blueprint: `hironaka-native-literal-module-restriction.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Hironaka.HironakaNativeLiteralModuleRestriction

open HironakaSingularModuleSheafStalk

noncomputable section
universe u
variable (X : LocallyRingedSpace.{u}) (U : Opens X.toTopCat)

/-- The existing native module-precomposition functor on the LITERAL original restricted space. -/
def nativeModuleRestrictionFunctor :
    SheafOfModules.{u} (forgetRing X.toSheafedSpace.sheaf) ⥤
      SheafOfModules.{u} (forgetRing (X.restrict U.isOpenEmbedding).toSheafedSpace.sheaf) where
  obj M := {
    val := (PresheafOfModules.pushforward₀OfCommRingCat U.isOpenEmbedding.functor X.presheaf).obj M.val
    isSheaf := TopCat.Presheaf.isSheaf_of_isOpenEmbedding U.isOpenEmbedding M.isSheaf }
  map f := ⟨(PresheafOfModules.pushforward₀OfCommRingCat
    U.isOpenEmbedding.functor X.presheaf).map f.val⟩
  map_id M := by ext V s; rfl
  map_comp f g := by ext V s; rfl

/-- SAME actual original module, genuinely restricted by the native functor. -/
abbrev nativeModuleRestriction (M : SheafOfModules.{u} (forgetRing X.toSheafedSpace.sheaf)) :=
  (nativeModuleRestrictionFunctor X U).obj M

@[simp] theorem nativeModuleRestriction_map_app
    {M N : SheafOfModules.{u} (forgetRing X.toSheafedSpace.sheaf)} (f : M ⟶ N)
    (V : Opens (X.restrict U.isOpenEmbedding).toTopCat)
    (s : M.val.obj (op (U.isOpenEmbedding.functor.obj V))) :
    ((nativeModuleRestrictionFunctor X U).map f).val.app (op V) s =
      f.val.app (op (U.isOpenEmbedding.functor.obj V)) s := rfl

/-- The actual native original unit restricts to the SAME literal restricted structure unit. -/
def nativeModuleRestriction_unitIso :
    nativeModuleRestriction X U (SheafOfModules.unit (forgetRing X.toSheafedSpace.sheaf)) ≅
      SheafOfModules.unit (forgetRing (X.restrict U.isOpenEmbedding).toSheafedSpace.sheaf) :=
  Iso.refl _

/-- The actual original inclusion morphism, restricted natively to the literal original open. -/
def nativeRestrictedIdealInclusion
    {M : SheafOfModules.{u} (forgetRing X.toSheafedSpace.sheaf)}
    (b : M ⟶ SheafOfModules.unit (forgetRing X.toSheafedSpace.sheaf)) :
    nativeModuleRestriction X U M ⟶
      SheafOfModules.unit (forgetRing (X.restrict U.isOpenEmbedding).toSheafedSpace.sheaf) :=
  (nativeModuleRestrictionFunctor X U).map b ≫ (nativeModuleRestriction_unitIso X U).hom

@[simp] theorem nativeRestrictedIdealInclusion_app
    {M : SheafOfModules.{u} (forgetRing X.toSheafedSpace.sheaf)}
    (b : M ⟶ SheafOfModules.unit (forgetRing X.toSheafedSpace.sheaf))
    (V : Opens (X.restrict U.isOpenEmbedding).toTopCat)
    (s : M.val.obj (op (U.isOpenEmbedding.functor.obj V))) :
    (nativeRestrictedIdealInclusion X U b).val.app (op V) s =
      b.val.app (op (U.isOpenEmbedding.functor.obj V)) s := rfl

end
end Hironaka.HironakaNativeLiteralModuleRestriction
