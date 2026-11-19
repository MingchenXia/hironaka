import Hironaka.Resolution.HironakaSingularModuleSheafStalk
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits

/-!
# The same original native module stalk functor is exact

The native sheafification adjunction and native abelian stalk functor
preserve the literal original finite presentation. No module action or
module category is copied. Blueprint: `hironaka-g10-native-module-stalk-exact.tex`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Hironaka.HironakaChowNativeModuleStalkExact

open HironakaSingularModuleSheafStalk

universe u v w
variable {X : TopCat.{u}} (R : X.Sheaf CommRingCat.{u})

/-- Original native module stalks and their original linear stalk maps. -/
def nativeStalkFunctor (x : X) :
    SheafOfModules.{u} (forgetRing R) ⥤ ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x) where
  obj M := ModuleCat.of _ ↑(TopCat.Presheaf.stalk M.val.presheaf x)
  map f := ModuleCat.ofHom (stalkLinearMap f.val x)
  map_id M := ModuleCat.hom_ext (stalkLinearMap_id M.val x)
  map_comp f g := ModuleCat.hom_ext (stalkLinearMap_comp f.val g.val x)

private def underlyingStalkIso (x : X) :
    nativeStalkFunctor R x ⋙ forget₂ (ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x)) AddCommGrpCat ≅
      SheafOfModules.toSheaf (forgetRing R) ⋙
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (X := X) x) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro M N f; ext m; rfl)

/-- The original underlying native abelian sheaf on any native site preserves finite colimits. -/
theorem underlyingSheaf_preservesFiniteColimits
    {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    (S : CategoryTheory.Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{u} S) where
  preservesFiniteColimits K _ _ := by
    have : PreservesColimitsOfShape K
        (PresheafOfModules.sheafification (𝟙 S.obj) ⋙
          SheafOfModules.toSheaf.{u} S) :=
      preservesColimitsOfShape_of_natIso
        (PresheafOfModules.sheafificationCompToSheaf (𝟙 S.obj)).symm
    exact ((PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)).preservesColimitsOfShape_iff (SheafOfModules.toSheaf.{u} S) K).mpr
        inferInstance

instance nativeStalkFunctor_preservesFiniteLimits (x : X) : PreservesFiniteLimits (nativeStalkFunctor R x) := by
  have := TopCat.Sheaf.instPreservesFiniteLimitsCompPresheafForgetStalkFunctor
    (C := AddCommGrpCat.{u}) (X := X) x
  have : PreservesFiniteLimits
      (SheafOfModules.toSheaf (forgetRing R) ⋙
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (X := X) x)) :=
    comp_preservesFiniteLimits (SheafOfModules.toSheaf (forgetRing R))
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (X := X) x)
  have : PreservesFiniteLimits
      (nativeStalkFunctor R x ⋙
        forget₂ (ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x)) AddCommGrpCat) :=
    preservesFiniteLimits_of_natIso (underlyingStalkIso R x).symm
  exact preservesFiniteLimits_of_reflects_of_preserves (nativeStalkFunctor R x)
    (forget₂ (ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x)) AddCommGrpCat)

instance nativeStalkFunctor_preservesFiniteColimits (x : X) : PreservesFiniteColimits (nativeStalkFunctor R x) := by
  classical
  have := underlyingSheaf_preservesFiniteColimits (forgetRing R)
  have := (stalkSkyscraperSheafAdjunction (C := AddCommGrpCat.{u}) (X := X) x).isLeftAdjoint
  have : PreservesFiniteColimits
      (SheafOfModules.toSheaf (forgetRing R) ⋙
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (X := X) x)) :=
    comp_preservesFiniteColimits (SheafOfModules.toSheaf (forgetRing R))
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (X := X) x)
  have : PreservesFiniteColimits
      (nativeStalkFunctor R x ⋙
        forget₂ (ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x)) AddCommGrpCat) :=
    preservesFiniteColimits_of_natIso (underlyingStalkIso R x).symm
  exact preservesFiniteColimits_of_reflects_of_preserves (nativeStalkFunctor R x)
    (forget₂ (ModuleCat.{u} ↑(TopCat.Presheaf.stalk R.obj x)) AddCommGrpCat)

/-- A genuine original sheaf epimorphism is surjective on its original module stalk. -/
theorem stalkLinearMap_surjective_of_epi {M N : SheafOfModules.{u} (forgetRing R)}
    (f : M ⟶ N) [Epi f] (x : X) : Function.Surjective (stalkLinearMap f.val x) := by
  exact (ModuleCat.epi_iff_surjective ((nativeStalkFunctor R x).map f)).mp inferInstance

/-- The SAME original native presentation remains a cokernel at the original stalk. -/
def presentationStalkIsColimit {M : SheafOfModules.{u} (forgetRing R)}
    (P : M.Presentation) (x : X) :
    IsColimit ((nativeStalkFunctor R x).mapCocone
      (CokernelCofork.ofπ
        (f := (SheafOfModules.freeHomEquiv _).symm P.relations.s ≫ kernel.ι _)
        P.generators.π (by simp))) :=
  isColimitOfPreserves (nativeStalkFunctor R x) P.isColimit

end Hironaka.HironakaChowNativeModuleStalkExact
