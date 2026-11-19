import Hironaka.Resolution.HironakaNativeLiteralModuleRestriction
import Hironaka.Resolution.HironakaChowNativeModuleStalkExact
import Mathlib.Topology.Sheaves.Over
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! Genuine realization of ARBITRARY native Over(V) modules on the literal
ORIGINAL restricted space, via the EXISTING native module equivalence.
No extension beyond V, copied scalar action, or ambient-module certificate.
Blueprint FIRST: `hironaka-g10-native-arbitrary-over-realization.tex`. -/

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hironaka.HironakaChowNativeArbitraryOverRealization

open HironakaSingularModuleSheafStalk HironakaChowNativeModuleStalkExact

variable (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)

/-- The ACTUAL restricted ring sheaf agrees with the native inverse-site restriction. -/
def realizationRingMap :
    forgetRing (X.restrict U.isOpenEmbedding).𝒪 ⟶
      (U.overEquivalence.inverse.sheafPushforwardContinuous RingCat
        (Opens.grothendieckTopology (TopCat.of U)) ((Opens.grothendieckTopology X.toTopCat).over U)).obj
          ((forgetRing X.𝒪).over U) where
  hom := 𝟙 _

/-- Return map is the ORIGINAL ring presheaf on the native equivalence counit. -/
def returnRingMap :
    (forgetRing X.𝒪).over U ⟶
      (U.overEquivalence.functor.sheafPushforwardContinuous RingCat
        ((Opens.grothendieckTopology X.toTopCat).over U) (Opens.grothendieckTopology (TopCat.of U))).obj
          (forgetRing (X.restrict U.isOpenEmbedding).𝒪) where
  hom := Functor.whiskerRight (NatTrans.op U.overEquivalence.unitInv)
    ((forgetRing X.𝒪).over U).obj

private theorem realization_ring_coherence_one :
    Functor.whiskerRight (NatTrans.op U.overEquivalence.symm.counit)
        ((forgetRing X.𝒪).over U).obj =
      (returnRingMap X U).hom ≫ U.overEquivalence.functor.op.whiskerLeft (realizationRingMap X U).hom := by
  simp only [realizationRingMap,returnRingMap]
  rfl

private theorem realization_ring_coherence_two :
    (realizationRingMap X U).hom ≫ U.overEquivalence.inverse.op.whiskerLeft (returnRingMap X U).hom ≫
      Functor.whiskerRight (NatTrans.op U.overEquivalence.symm.unit)
        (forgetRing (X.restrict U.isOpenEmbedding).𝒪).obj =
      𝟙 (forgetRing (X.restrict U.isOpenEmbedding).𝒪).obj := by
  ext W r
  change X.presheaf.map _ (X.presheaf.map _ r) = r
  rw [← Functor.map_comp_apply]
  have h := ConcreteCategory.congr_hom (X.presheaf.map_id _) r
  convert h using 1
  · exact congrArg (fun k => X.presheaf.map k r) (Subsingleton.elim _ _)
  · rfl

/-- The EXISTING native module equivalence realizes EVERY arbitrary original over-site module. -/
def realizationEquivalence :
    SheafOfModules.{0} ((forgetRing X.𝒪).over U) ≌
      SheafOfModules.{0} (forgetRing (X.restrict U.isOpenEmbedding).𝒪) := by
  have : Functor.IsContinuous U.overEquivalence.symm.functor
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).toTopCat)
      ((Opens.grothendieckTopology X.toTopCat).over U) := by
    change Functor.IsContinuous U.overEquivalence.inverse
      (Opens.grothendieckTopology (TopCat.of U)) ((Opens.grothendieckTopology X.toTopCat).over U)
    infer_instance
  have : Functor.IsContinuous U.overEquivalence.symm.inverse
      ((Opens.grothendieckTopology X.toTopCat).over U)
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).toTopCat) := by
    change Functor.IsContinuous U.overEquivalence.functor
      ((Opens.grothendieckTopology X.toTopCat).over U) (Opens.grothendieckTopology (TopCat.of U))
    infer_instance
  exact SheafOfModules.pushforwardPushforwardEquivalence U.overEquivalence.symm
    (realizationRingMap X U) (returnRingMap X U)
      (realization_ring_coherence_one X U) (realization_ring_coherence_two X U)

/-- Native literal-open realization, with no choice of global ambient module. -/
abbrev realizationFunctor := (realizationEquivalence X U).functor

/-- ORIGINAL native section-map components are retained literally. -/
theorem realization_map_app
    {M N : SheafOfModules.{0} ((forgetRing X.𝒪).over U)} (f : M ⟶ N)
    (W : Opens (X.restrict U.isOpenEmbedding).toTopCat)
    (m : M.val.obj (U.overEquivalence.inverse.op.obj (op W))) :
    ((realizationFunctor X U).map f).val.app (op W) m =
      f.val.app (U.overEquivalence.inverse.op.obj (op W)) m := rfl

/-- Native realization retains the ACTUAL literal restricted unit and its same actions. -/
def realizationUnitIso :
    (realizationFunctor X U).obj (SheafOfModules.unit ((forgetRing X.𝒪).over U)) ≅
      SheafOfModules.unit (forgetRing (X.restrict U.isOpenEmbedding).𝒪) := Iso.refl _

/-- The canonical native coproduct comparison retains the SAME original free indices. -/
def realizationFreeIso (I : Type) :
    (realizationFunctor X U).obj (SheafOfModules.free (R := (forgetRing X.𝒪).over U) I) ≅
      SheafOfModules.free (R := forgetRing (X.restrict U.isOpenEmbedding).𝒪) I :=
  (SheafOfModules.mapFreeIso (realizationFunctor X U) I (realizationUnitIso X U).symm).symm

/-- WHOLE epi on an arbitrary Over(U) module gives actual literal-open stalk surjectivity. -/
theorem realization_stalk_surjective_of_epi
    {M N : SheafOfModules.{0} ((forgetRing X.𝒪).over U)} (f : M ⟶ N) [Epi f] (y : U) :
    Function.Surjective (stalkLinearMap ((realizationFunctor X U).map f).val y) := by
  have : Epi ((realizationFunctor X U).map f) := Functor.map_epi _ _
  exact stalkLinearMap_surjective_of_epi (X.restrict U.isOpenEmbedding).𝒪
    ((realizationFunctor X U).map f) y

end Hironaka.HironakaChowNativeArbitraryOverRealization
