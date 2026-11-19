import Hironaka.Resolution.HironakaChowNativeArbitraryOverRealization
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! Structural native local-over finite-data transport. No analytic coherence
or free-kernel premise, and zero duplicate mathematical-engine credit.
Blueprint FIRST: hironaka-g10-native-local-over-finite-data-transport.tex. -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
namespace Hironaka.HironakaChowNativeLocalOverFiniteDataTransport
open HironakaChowNativeArbitraryOverRealization HironakaSingularModuleSheafStalk

private theorem overPost_continuous_of_equivalence
    {C D : Type} [Category C] [Category D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (G : C ⥤ D) [G.IsEquivalence] [G.IsContinuous J K] (V : C) :
    (Over.post (X := V) G).IsContinuous (J.over V) (K.over (G.obj V)) := by
  apply Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat _ _)
  exact (CoverPreserving.of_isContinuous G J K).overPost V

section LocalSiteRestriction

def localSiteEquivalence (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U)) :
    Over V ≌ Over (U.overEquivalence.inverse.obj V).left :=
  (Over.postEquiv (X := V) U.overEquivalence.symm).trans
    (Over.iteratedSliceEquiv (U.overEquivalence.inverse.obj V))

private theorem localSiteForward_continuous (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U)) :
    (localSiteEquivalence X U V).functor.IsContinuous
      ((Opens.grothendieckTopology (TopCat.of U)).over V)
      ((Opens.grothendieckTopology X.toTopCat).over (U.overEquivalence.inverse.obj V).left) := by
  let JU := Opens.grothendieckTopology (TopCat.of U)
  let JX := Opens.grothendieckTopology X.toTopCat
  let A : Over U := U.overEquivalence.inverse.obj V
  have : U.overEquivalence.inverse.IsContinuous JU (JX.over U) := by
    change U.overEquivalence.inverse.IsContinuous
      (Opens.grothendieckTopology (TopCat.of U)) (JX.over U)
    infer_instance
  have : U.overEquivalence.inverse.IsEquivalence := U.overEquivalence.isEquivalence_inverse
  have : (Over.post (X := V) U.overEquivalence.inverse).IsContinuous (JU.over V) ((JX.over U).over A) :=
    overPost_continuous_of_equivalence JU (JX.over U) U.overEquivalence.inverse V
  change (Over.post (X := V) U.overEquivalence.inverse ⋙ Over.iteratedSliceForward A).IsContinuous
    (JU.over V) (JX.over A.left)
  exact Functor.isContinuous_comp _ _ _ ((JX.over U).over A) _
attribute [local instance] localSiteForward_continuous

private theorem localSiteInverse_continuous (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U)) :
    (localSiteEquivalence X U V).inverse.IsContinuous
      ((Opens.grothendieckTopology X.toTopCat).over (U.overEquivalence.inverse.obj V).left)
      ((Opens.grothendieckTopology (TopCat.of U)).over V) := by
  let JU := Opens.grothendieckTopology (TopCat.of U)
  let JX := Opens.grothendieckTopology X.toTopCat
  let A : Over U := U.overEquivalence.inverse.obj V
  have : U.overEquivalence.functor.IsContinuous (JX.over U) JU := by
    change U.overEquivalence.functor.IsContinuous (JX.over U)
      (Opens.grothendieckTopology (TopCat.of U))
    infer_instance
  have : U.overEquivalence.functor.IsEquivalence := U.overEquivalence.isEquivalence_functor
  have : (Over.post (X := A) U.overEquivalence.functor).IsContinuous
      ((JX.over U).over A) (JU.over (U.overEquivalence.functor.obj A)) :=
    overPost_continuous_of_equivalence (JX.over U) JU U.overEquivalence.functor A
  let c : U.overEquivalence.functor.obj A ⟶ V := U.overEquivalence.counitIso.hom.app V
  have : (Over.map c).IsContinuous (JU.over (U.overEquivalence.functor.obj A)) (JU.over V) :=
    Functor.isContinuous_of_coverPreserving
      (GrothendieckTopology.over_map_compatiblePreserving JU c)
      (GrothendieckTopology.over_map_coverPreserving JU c)
  have : (Over.post (X := A) U.overEquivalence.functor ⋙ Over.map c).IsContinuous
      ((JX.over U).over A) (JU.over V) :=
    Functor.isContinuous_comp _ _ _ (JU.over (U.overEquivalence.functor.obj A)) _
  change (Over.iteratedSliceBackward A ⋙
    (Over.post (X := A) U.overEquivalence.functor ⋙ Over.map c)).IsContinuous
      (JX.over A.left) (JU.over V)
  exact Functor.isContinuous_comp _ _ _ ((JX.over U).over A) _
attribute [local instance] localSiteInverse_continuous

private theorem localSiteForward_cocontinuous (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U)) :
    (localSiteEquivalence X U V).functor.IsCocontinuous
      ((Opens.grothendieckTopology (TopCat.of U)).over V)
      ((Opens.grothendieckTopology X.toTopCat).over (U.overEquivalence.inverse.obj V).left) := by
  let JU := Opens.grothendieckTopology (TopCat.of U)
  let JX := Opens.grothendieckTopology X.toTopCat
  let A : Over U := U.overEquivalence.inverse.obj V
  have : U.overEquivalence.inverse.IsCocontinuous JU (JX.over U) := by
    change U.overEquivalence.inverse.IsCocontinuous
      (Opens.grothendieckTopology (TopCat.of U)) (JX.over U)
    infer_instance
  have : (Over.post (X := V) U.overEquivalence.inverse).IsCocontinuous
      (JU.over V) ((JX.over U).over A) := inferInstance
  change (Over.post (X := V) U.overEquivalence.inverse ⋙ Over.iteratedSliceForward A).IsCocontinuous
    (JU.over V) (JX.over A.left)
  exact isCocontinuous_comp _ _ _ ((JX.over U).over A)
attribute [local instance] localSiteForward_cocontinuous

private theorem localSiteInverse_cocontinuous (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U)) :
    (localSiteEquivalence X U V).inverse.IsCocontinuous
      ((Opens.grothendieckTopology X.toTopCat).over (U.overEquivalence.inverse.obj V).left)
      ((Opens.grothendieckTopology (TopCat.of U)).over V) := by
  let JU := Opens.grothendieckTopology (TopCat.of U)
  let JX := Opens.grothendieckTopology X.toTopCat
  let A : Over U := U.overEquivalence.inverse.obj V
  have : U.overEquivalence.functor.IsCocontinuous (JX.over U) JU := by
    change U.overEquivalence.functor.IsCocontinuous (JX.over U)
      (Opens.grothendieckTopology (TopCat.of U))
    infer_instance
  have : (Over.post (X := A) U.overEquivalence.functor).IsCocontinuous
      ((JX.over U).over A) (JU.over (U.overEquivalence.functor.obj A)) := inferInstance
  let c : U.overEquivalence.functor.obj A ⟶ V := U.overEquivalence.counitIso.hom.app V
  have : (Over.map c).IsCocontinuous (JU.over (U.overEquivalence.functor.obj A)) (JU.over V) :=
    inferInstance
  have : (Over.post (X := A) U.overEquivalence.functor ⋙ Over.map c).IsCocontinuous
      ((JX.over U).over A) (JU.over V) :=
    isCocontinuous_comp _ _ _ (JU.over (U.overEquivalence.functor.obj A))
  change (Over.iteratedSliceBackward A ⋙
    (Over.post (X := A) U.overEquivalence.functor ⋙ Over.map c)).IsCocontinuous
      (JX.over A.left) (JU.over V)
  exact isCocontinuous_comp _ _ _ ((JX.over U).over A)
attribute [local instance] localSiteInverse_cocontinuous

def localRingMap (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U)) :
    (forgetRing (X.restrict U.isOpenEmbedding).𝒪).over V ⟶
      ((localSiteEquivalence X U V).functor.sheafPushforwardContinuous RingCat.{0}
        ((Opens.grothendieckTopology (TopCat.of U)).over V)
        ((Opens.grothendieckTopology X.toTopCat).over (U.overEquivalence.inverse.obj V).left)).obj
          ((forgetRing X.𝒪).over (U.overEquivalence.inverse.obj V).left) where
  hom := 𝟙 _

def localReturnRingMap (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U)) :
    (forgetRing X.𝒪).over (U.overEquivalence.inverse.obj V).left ⟶
      ((localSiteEquivalence X U V).inverse.sheafPushforwardContinuous RingCat.{0}
        ((Opens.grothendieckTopology X.toTopCat).over (U.overEquivalence.inverse.obj V).left)
        ((Opens.grothendieckTopology (TopCat.of U)).over V)).obj
          ((forgetRing (X.restrict U.isOpenEmbedding).𝒪).over V) where
  hom := Functor.whiskerRight (NatTrans.op (localSiteEquivalence X U V).counit)
    ((forgetRing X.𝒪).over (U.overEquivalence.inverse.obj V).left).obj

private theorem local_ring_coherence_one (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U)) :
    Functor.whiskerRight (NatTrans.op (localSiteEquivalence X U V).counit)
      ((forgetRing X.𝒪).over (U.overEquivalence.inverse.obj V).left).obj =
        (localReturnRingMap X U V).hom ≫
          (localSiteEquivalence X U V).inverse.op.whiskerLeft (localRingMap X U V).hom := by
  simp only [localRingMap,localReturnRingMap]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem local_ring_coherence_two (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U)) :
    (localRingMap X U V).hom ≫
      (localSiteEquivalence X U V).functor.op.whiskerLeft (localReturnRingMap X U V).hom ≫
        Functor.whiskerRight (NatTrans.op (localSiteEquivalence X U V).unit)
          ((forgetRing (X.restrict U.isOpenEmbedding).𝒪).over V).obj =
      𝟙 ((forgetRing (X.restrict U.isOpenEmbedding).𝒪).over V).obj := by
  apply NatTrans.ext
  funext T
  apply RingCat.hom_ext
  apply RingHom.ext
  intro r
  change X.presheaf.map _ (X.presheaf.map _ r) = r
  rw [← Functor.map_comp_apply]
  have h := ConcreteCategory.congr_hom (X.presheaf.map_id _) r
  convert h using 1
  · exact congrArg (fun k => X.presheaf.map k r) (Subsingleton.elim _ _)
  · rfl

set_option backward.isDefEq.respectTransparency.types false in
def localModuleEquivalence (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U)) :
    SheafOfModules.{0} ((forgetRing X.𝒪).over (U.overEquivalence.inverse.obj V).left) ≌
      SheafOfModules.{0}
        (J := (Opens.grothendieckTopology (TopCat.of U)).over V)
        ((forgetRing (X.restrict U.isOpenEmbedding).𝒪).over V) := by
  have : (localSiteEquivalence X U V).functor.IsContinuous
      ((Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).toTopCat).over V)
      ((Opens.grothendieckTopology X.toTopCat).over (U.overEquivalence.inverse.obj V).left) := by
    change (localSiteEquivalence X U V).functor.IsContinuous
      ((Opens.grothendieckTopology (TopCat.of U)).over V)
      ((Opens.grothendieckTopology X.toTopCat).over (U.overEquivalence.inverse.obj V).left)
    exact localSiteForward_continuous X U V
  have : (localSiteEquivalence X U V).inverse.IsContinuous
      ((Opens.grothendieckTopology X.toTopCat).over (U.overEquivalence.inverse.obj V).left)
      ((Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).toTopCat).over V) := by
    change (localSiteEquivalence X U V).inverse.IsContinuous
      ((Opens.grothendieckTopology X.toTopCat).over (U.overEquivalence.inverse.obj V).left)
      ((Opens.grothendieckTopology (TopCat.of U)).over V)
    exact localSiteInverse_continuous X U V
  exact SheafOfModules.pushforwardPushforwardEquivalence (localSiteEquivalence X U V)
    (localRingMap X U V) (localReturnRingMap X U V)
      (local_ring_coherence_one X U V) (local_ring_coherence_two X U V)

set_option backward.isDefEq.respectTransparency.types false in
/-- Every forward full map component is the original native component. -/
theorem forward_map_app (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U))
    {M N : SheafOfModules.{0} ((forgetRing X.𝒪).over (U.overEquivalence.inverse.obj V).left)}
    (f : M ⟶ N) (T : Over V)
    (m : M.val.obj ((localSiteEquivalence X U V).functor.op.obj (op T))) :
    (((localModuleEquivalence X U V).functor.map f).val.app (op T)) m =
      f.val.app ((localSiteEquivalence X U V).functor.op.obj (op T)) m := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Every return full map component is the original native component. -/
theorem inverse_map_app (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U))
    {M N : SheafOfModules.{0}
        (J := (Opens.grothendieckTopology (TopCat.of U)).over V)
        ((forgetRing (X.restrict U.isOpenEmbedding).𝒪).over V)}
    (f : M ⟶ N) (T : Over (U.overEquivalence.inverse.obj V).left)
    (m : M.val.obj ((localSiteEquivalence X U V).inverse.op.obj (op T))) :
    (((localModuleEquivalence X U V).inverse.map f).val.app (op T)) m =
      f.val.app ((localSiteEquivalence X U V).inverse.op.obj (op T)) m := rfl

end LocalSiteRestriction

set_option backward.isDefEq.respectTransparency.types false in
/-- The forward native unit is the same original restricted unit. -/
def localUnitIso (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U)) :
    (localModuleEquivalence X U V).functor.obj
      (SheafOfModules.unit ((forgetRing X.𝒪).over (U.overEquivalence.inverse.obj V).left)) ≅
        SheafOfModules.unit (J := (Opens.grothendieckTopology (TopCat.of U)).over V)
          ((forgetRing (X.restrict U.isOpenEmbedding).𝒪).over V) := Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
/-- The return native unit uses the actual unit of the whole equivalence. -/
def localReturnUnitIso (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U)) :
    (localModuleEquivalence X U V).inverse.obj
      (SheafOfModules.unit (J := (Opens.grothendieckTopology (TopCat.of U)).over V)
        ((forgetRing (X.restrict U.isOpenEmbedding).𝒪).over V)) ≅
        SheafOfModules.unit ((forgetRing X.𝒪).over (U.overEquivalence.inverse.obj V).left) :=
  (localModuleEquivalence X U V).inverse.mapIso (localUnitIso X U V).symm ≪≫
    ((localModuleEquivalence X U V).unitIso.app _).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Native free comparison with every original index retained. -/
def localFreeIso (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U)) (I : Type) :
    (localModuleEquivalence X U V).functor.obj
      (SheafOfModules.free (R := (forgetRing X.𝒪).over (U.overEquivalence.inverse.obj V).left) I) ≅
        SheafOfModules.free (J := (Opens.grothendieckTopology (TopCat.of U)).over V)
          (R := (forgetRing (X.restrict U.isOpenEmbedding).𝒪).over V) I :=
  (SheafOfModules.mapFreeIso (localModuleEquivalence X U V).functor I
    (localUnitIso X U V).symm).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Native return free comparison with the same original index. -/
def localReturnFreeIso (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (V : Opens (TopCat.of U)) (I : Type) :
    (localModuleEquivalence X U V).inverse.obj
      (SheafOfModules.free (J := (Opens.grothendieckTopology (TopCat.of U)).over V)
        (R := (forgetRing (X.restrict U.isOpenEmbedding).𝒪).over V) I) ≅
        SheafOfModules.free (R := (forgetRing X.𝒪).over (U.overEquivalence.inverse.obj V).left) I :=
  (SheafOfModules.mapFreeIso (localModuleEquivalence X U V).inverse I
    (localReturnUnitIso X U V).symm).symm

-- The held native cover/free-map mechanism, with original finite indices.
private theorem finitePresentation_pushforward
    {C D : Type} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{0}} {S : Sheaf K RingCat.{0}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{0}]
    [∀ X, HasSheafify (K.over X) AddCommGrpCat.{0}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{0}]
    [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{0}]
    (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{0} K J).obj R)
    (η : (SheafOfModules.pushforward φ).obj (SheafOfModules.unit R) ≅ SheafOfModules.unit S)
    [∀ X, (Over.post G).IsContinuous (K.over X) (J.over _)]
    (h : ∀ (X : D) (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{0,0} <|
      SheafOfModules.pushforward.{0} (R := R.over Y) (F := Over.post (X := X) G ⋙ Over.map f)
        (((Over.forget X).sheafPushforwardContinuous RingCat.{0} (K.over X) K).map φ))
    {M : SheafOfModules.{0} R} [M.IsFinitePresentation] :
    ((SheafOfModules.pushforward φ).obj M).IsFinitePresentation := by
  obtain ⟨P,hP⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  let Q := P.pushforward G φ η h
  refine ⟨Q,⟨fun i => ?_⟩⟩
  exact
    { isFiniteType_generators := ⟨(hP.isFinite_presentation i.2.1).isFiniteType_generators.finite⟩
      isFiniteType_relations := ⟨(hP.isFinite_presentation i.2.1).isFiniteType_relations.finite⟩ }

private theorem finitePresentation_pushforward_of_leftAdjoint
    {C D : Type} [Category C] [Category D] [HasPullbacks C] [HasPullbacks D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{0}} {S : Sheaf K RingCat.{0}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{0}]
    [∀ X, HasSheafify (K.over X) AddCommGrpCat.{0}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{0}]
    [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{0}]
    (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J] [G.IsLeftAdjoint]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{0} K J).obj R) (hφ : IsIso φ)
    (η : (SheafOfModules.pushforward φ).obj (SheafOfModules.unit R) ≅ SheafOfModules.unit S)
    [∀ X, (Over.post G).IsContinuous (K.over X) (J.over _)]
    {M : SheafOfModules.{0} R} [hM : M.IsFinitePresentation] :
    ((SheafOfModules.pushforward φ).obj M).IsFinitePresentation := by
  have : IsIso φ := hφ
  refine finitePresentation_pushforward (R := R) (S := S) G φ η ?_ (M := M)
  intro X Y f
  let G' := Over.post (X := X) G ⋙ Over.map f
  have : G'.IsContinuous (K.over X) (J.over Y) := Functor.isContinuous_comp _ _ _ (J.over _) _
  have : G'.IsCocontinuous (K.over X) (J.over Y) := isCocontinuous_comp _ _ _ (J.over _)
  let ψ : S.over X ⟶
      (G'.sheafPushforwardContinuous RingCat.{0} (K.over X) (J.over Y)).obj (R.over Y) :=
    ((Over.forget X).sheafPushforwardContinuous RingCat.{0} (K.over X) K).map φ
  have : IsIso ψ := by
    change IsIso (((Over.forget X).sheafPushforwardContinuous RingCat.{0} (K.over X) K).map φ)
    infer_instance
  have : (SheafOfModules.pushforward.{0} ψ).IsLeftAdjoint := SheafOfModules.isLeftAdjoint_pushforward_of_isIso ψ
  infer_instance

-- Held QuasicoherentData.pushforward cover/free-map mechanism instantiated
-- for ACTUAL finite generating sections, retaining every original finite index.
private theorem finiteType_pushforward
    {C D : Type} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{0}} {S : Sheaf K RingCat.{0}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{0}]
    [∀ X, HasSheafify (K.over X) AddCommGrpCat.{0}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{0}]
    [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{0}]
    (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{0} K J).obj R)
    (η : (SheafOfModules.pushforward φ).obj (SheafOfModules.unit R) ≅ SheafOfModules.unit S)
    [∀ X, (Over.post G).IsContinuous (K.over X) (J.over _)]
    (h : ∀ (X : D) (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{0,0} <|
      SheafOfModules.pushforward.{0} (R := R.over Y) (F := Over.post (X := X) G ⋙ Over.map f)
        (((Over.forget X).sheafPushforwardContinuous RingCat.{0} (K.over X) K).map φ))
    {M : SheafOfModules.{0} R} [M.IsFiniteType] :
    ((SheafOfModules.pushforward φ).obj M).IsFiniteType := by
  obtain ⟨P,hP⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  let Q : ((SheafOfModules.pushforward φ).obj M).LocalGeneratorsData := {
    I := Σ (X : D) (i : P.I), G.obj X ⟶ P.X i
    X i := i.1
    coversTop Y := by
      refine K.superset_covering ?_ <| G.cover_lift K _ (P.coversTop (G.obj Y))
      intro Z g ⟨i,⟨v⟩⟩
      exact ⟨⟨Z,i,v⟩,⟨𝟙 _⟩⟩
    generators i := by
      letI overS : SheafOfModules.{0} S ⥤ SheafOfModules.{0} (S.over i.1) :=
        SheafOfModules.pushforward (𝟙 _)
      letI G' := Over.post (X := i.1) G ⋙ Over.map i.2.2
      letI ψ : S.over i.1 ⟶
          (G'.sheafPushforwardContinuous RingCat.{0} (K.over i.1) (J.over (P.X i.2.1))).obj
            (R.over (P.X i.2.1)) :=
        ((Over.forget i.1).sheafPushforwardContinuous RingCat.{0} (K.over i.1) K).map φ
      letI e : (SheafOfModules.pushforward ψ).obj (SheafOfModules.unit (R.over (P.X i.2.1))) ≅
          SheafOfModules.unit (S.over i.1) := overS.mapIso η
      haveI : PreservesColimitsOfSize.{0,0} (SheafOfModules.pushforward ψ) := h _ _ _
      exact (P.generators i.2.1).map (SheafOfModules.pushforward ψ) e.symm }
  refine ⟨Q,⟨fun i => ⟨?_⟩⟩⟩
  exact (hP.isFiniteType i.2.1).finite

private theorem finiteType_pushforward_of_leftAdjoint
    {C D : Type} [Category C] [Category D] [HasPullbacks C] [HasPullbacks D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{0}} {S : Sheaf K RingCat.{0}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{0}]
    [∀ X, HasSheafify (K.over X) AddCommGrpCat.{0}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{0}]
    [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{0}]
    (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J] [G.IsLeftAdjoint]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{0} K J).obj R) (hφ : IsIso φ)
    (η : (SheafOfModules.pushforward φ).obj (SheafOfModules.unit R) ≅ SheafOfModules.unit S)
    [∀ X, (Over.post G).IsContinuous (K.over X) (J.over _)]
    {M : SheafOfModules.{0} R} [hM : M.IsFiniteType] :
    ((SheafOfModules.pushforward φ).obj M).IsFiniteType := by
  have : IsIso φ := hφ
  refine finiteType_pushforward (R := R) (S := S) G φ η ?_ (M := M)
  intro X Y f
  let G' := Over.post (X := X) G ⋙ Over.map f
  have : G'.IsContinuous (K.over X) (J.over Y) := Functor.isContinuous_comp _ _ _ (J.over _) _
  have : G'.IsCocontinuous (K.over X) (J.over Y) := isCocontinuous_comp _ _ _ (J.over _)
  let ψ : S.over X ⟶
      (G'.sheafPushforwardContinuous RingCat.{0} (K.over X) (J.over Y)).obj (R.over Y) :=
    ((Over.forget X).sheafPushforwardContinuous RingCat.{0} (K.over X) K).map φ
  have : IsIso ψ := by
    change IsIso (((Over.forget X).sheafPushforwardContinuous RingCat.{0} (K.over X) K).map φ)
    infer_instance
  have : (SheafOfModules.pushforward.{0} ψ).IsLeftAdjoint := SheafOfModules.isLeftAdjoint_pushforward_of_isIso ψ
  infer_instance


section FiniteData

-- Actual native site equivalences supply the nested sheafification proofs.
-- LOCAL instance attributes only: no imported instance or native object is replaced.
private theorem singleOverAddGroupSheafify {X : TopCat.{0}} (U : Opens X) :
    HasSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{0} :=
  U.overEquivalence.hasSheafify ((Opens.grothendieckTopology X).over U)
    (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat.{0}
attribute [local instance] singleOverAddGroupSheafify

private theorem doubleOverAddGroupSheafify {X : TopCat.{0}} (U : Opens X) (V : Over U) :
    HasSheafify (((Opens.grothendieckTopology X).over U).over V) AddCommGrpCat.{0} :=
  (Over.iteratedSliceEquiv V).hasSheafify (((Opens.grothendieckTopology X).over U).over V)
    ((Opens.grothendieckTopology X).over V.left) AddCommGrpCat.{0}
attribute [local instance] doubleOverAddGroupSheafify

private theorem doubleOverAddGroupWeakSheafify {X : TopCat.{0}} (U : Opens X) (V : Over U) :
    HasWeakSheafify (((Opens.grothendieckTopology X).over U).over V) AddCommGrpCat.{0} :=
  (doubleOverAddGroupSheafify U V).isRightAdjoint
attribute [local instance] doubleOverAddGroupWeakSheafify


theorem over_isFinitePresentation
    {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
    (M : SheafOfModules.{0} (forgetRing R)) [M.IsFinitePresentation] (U : Opens X) :
    (M.over U).IsFinitePresentation := by
  exact finitePresentation_pushforward_of_leftAdjoint
    (R := forgetRing R) (S := (forgetRing R).over U)
    (Over.forget U) (𝟙 _) (by infer_instance) (Iso.refl _) (M := M) (hM := inferInstanceAs M.IsFinitePresentation)

set_option backward.isDefEq.respectTransparency.types false in
theorem realization_isFinitePresentation
    (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (M : SheafOfModules.{0} ((forgetRing X.𝒪).over U)) [M.IsFinitePresentation] :
    ((realizationFunctor X U).obj M).IsFinitePresentation := by
  let J := (Opens.grothendieckTopology X.toTopCat).over U
  let K := Opens.grothendieckTopology (TopCat.of U)
  have : U.overEquivalence.inverse.IsContinuous K J := inferInstance
  have : U.overEquivalence.inverse.IsCocontinuous K J := inferInstance
  have : U.overEquivalence.inverse.IsEquivalence := U.overEquivalence.isEquivalence_inverse
  have : IsIso ((sheafToPresheaf K RingCat.{0}).map (realizationRingMap X U)) := by
    change IsIso (𝟙 _)
    infer_instance
  have hφ : IsIso (realizationRingMap X U) :=
    (fullyFaithfulSheafToPresheaf K RingCat.{0}).isIso_of_isIso_map (realizationRingMap X U)
  let : ∀ V : Opens (TopCat.of U),
      (Over.post (X := V) U.overEquivalence.inverse).IsContinuous (K.over V) (J.over _) :=
    fun V => overPost_continuous_of_equivalence K J U.overEquivalence.inverse V
  exact finitePresentation_pushforward_of_leftAdjoint (J := J) (K := K)
    (R := (forgetRing X.𝒪).over U) (S := forgetRing (X.restrict U.isOpenEmbedding).𝒪)
    U.overEquivalence.inverse (realizationRingMap X U) hφ (realizationUnitIso X U) (M := M) (hM := inferInstanceAs M.IsFinitePresentation)

private def returnUnitIso (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat) :
    (realizationEquivalence X U).inverse.obj
      (SheafOfModules.unit (forgetRing (X.restrict U.isOpenEmbedding).𝒪)) ≅
        SheafOfModules.unit ((forgetRing X.𝒪).over U) :=
  (realizationEquivalence X U).inverse.mapIso (realizationUnitIso X U).symm ≪≫
    ((realizationEquivalence X U).unitIso.app _).symm

set_option backward.isDefEq.respectTransparency.types false in
theorem return_isFinitePresentation
    (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (M : SheafOfModules.{0} (forgetRing (X.restrict U.isOpenEmbedding).𝒪))
    [M.IsFinitePresentation] :
    ((realizationEquivalence X U).inverse.obj M).IsFinitePresentation := by
  let J := (Opens.grothendieckTopology X.toTopCat).over U
  let K := Opens.grothendieckTopology (TopCat.of U)
  have : U.overEquivalence.functor.IsContinuous J K := inferInstance
  have : U.overEquivalence.functor.IsCocontinuous J K := inferInstance
  have : U.overEquivalence.functor.IsEquivalence := U.overEquivalence.isEquivalence_functor
  have : IsIso ((sheafToPresheaf J RingCat.{0}).map (returnRingMap X U)) := by
    change IsIso (Functor.whiskerRight (NatTrans.op U.overEquivalence.unitInv)
      ((forgetRing X.𝒪).over U).obj)
    infer_instance
  have hφ : IsIso (returnRingMap X U) :=
    (fullyFaithfulSheafToPresheaf J RingCat.{0}).isIso_of_isIso_map (returnRingMap X U)
  let : ∀ V : Over U,
      (Over.post (X := V) U.overEquivalence.functor).IsContinuous (J.over V) (K.over _) :=
    fun V => overPost_continuous_of_equivalence J K U.overEquivalence.functor V
  exact finitePresentation_pushforward_of_leftAdjoint (J := K) (K := J)
    (R := forgetRing (X.restrict U.isOpenEmbedding).𝒪) (S := (forgetRing X.𝒪).over U)
    U.overEquivalence.functor (returnRingMap X U) hφ (returnUnitIso X U) (M := M) (hM := inferInstanceAs M.IsFinitePresentation)

set_option backward.isDefEq.respectTransparency.types false in
theorem return_isFiniteType
    (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat)
    (M : SheafOfModules.{0} (forgetRing (X.restrict U.isOpenEmbedding).𝒪))
    [M.IsFiniteType] :
    ((realizationEquivalence X U).inverse.obj M).IsFiniteType := by
  let J := (Opens.grothendieckTopology X.toTopCat).over U
  let K := Opens.grothendieckTopology (TopCat.of U)
  have : U.overEquivalence.functor.IsContinuous J K := inferInstance
  have : U.overEquivalence.functor.IsCocontinuous J K := inferInstance
  have : U.overEquivalence.functor.IsEquivalence := U.overEquivalence.isEquivalence_functor
  have : IsIso ((sheafToPresheaf J RingCat.{0}).map (returnRingMap X U)) := by
    change IsIso (Functor.whiskerRight (NatTrans.op U.overEquivalence.unitInv)
      ((forgetRing X.𝒪).over U).obj)
    infer_instance
  have hφ : IsIso (returnRingMap X U) :=
    (fullyFaithfulSheafToPresheaf J RingCat.{0}).isIso_of_isIso_map (returnRingMap X U)
  let : ∀ V : Over U,
      (Over.post (X := V) U.overEquivalence.functor).IsContinuous (J.over V) (K.over _) :=
    fun V => overPost_continuous_of_equivalence J K U.overEquivalence.functor V
  exact finiteType_pushforward_of_leftAdjoint (J := K) (K := J)
    (R := forgetRing (X.restrict U.isOpenEmbedding).𝒪) (S := (forgetRing X.𝒪).over U)
    U.overEquivalence.functor (returnRingMap X U) hφ (returnUnitIso X U) (M := M) (hM := inferInstanceAs M.IsFiniteType)

set_option backward.isDefEq.respectTransparency.types false in
theorem local_forward_isFinitePresentation
    (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat) (V : Opens (TopCat.of U))
    (M : SheafOfModules.{0} ((forgetRing X.𝒪).over (U.overEquivalence.inverse.obj V).left))
    [M.IsFinitePresentation] :
    ((localModuleEquivalence X U V).functor.obj M).IsFinitePresentation := by
  let E := localSiteEquivalence X U V
  let J := (Opens.grothendieckTopology X.toTopCat).over (U.overEquivalence.inverse.obj V).left
  let K := (Opens.grothendieckTopology (TopCat.of U)).over V
  have : E.functor.IsContinuous K J := localSiteForward_continuous X U V
  have : E.functor.IsCocontinuous K J := localSiteForward_cocontinuous X U V
  have : E.functor.IsEquivalence := E.isEquivalence_functor
  have : IsIso ((sheafToPresheaf K RingCat.{0}).map (localRingMap X U V)) := by
    change IsIso (𝟙 _)
    infer_instance
  have hφ : IsIso (localRingMap X U V) :=
    (fullyFaithfulSheafToPresheaf K RingCat.{0}).isIso_of_isIso_map (localRingMap X U V)
  let : ∀ T : Over V, (Over.post (X := T) E.functor).IsContinuous (K.over T) (J.over _) :=
    fun T => overPost_continuous_of_equivalence K J E.functor T
  exact finitePresentation_pushforward_of_leftAdjoint (J := J) (K := K)
    (R := (forgetRing X.𝒪).over (U.overEquivalence.inverse.obj V).left)
    (S := (forgetRing (X.restrict U.isOpenEmbedding).𝒪).over V)
    E.functor (localRingMap X U V) hφ (localUnitIso X U V) (M := M) (hM := inferInstanceAs M.IsFinitePresentation)

set_option backward.isDefEq.respectTransparency.types false in
theorem local_inverse_isFinitePresentation
    (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat) (V : Opens (TopCat.of U))
    (M : SheafOfModules.{0}
        (J := (Opens.grothendieckTopology (TopCat.of U)).over V)
        ((forgetRing (X.restrict U.isOpenEmbedding).𝒪).over V))
    [M.IsFinitePresentation] :
    ((localModuleEquivalence X U V).inverse.obj M).IsFinitePresentation := by
  let E := localSiteEquivalence X U V
  let J := (Opens.grothendieckTopology X.toTopCat).over (U.overEquivalence.inverse.obj V).left
  let K := (Opens.grothendieckTopology (TopCat.of U)).over V
  have : E.inverse.IsContinuous J K := localSiteInverse_continuous X U V
  have : E.inverse.IsCocontinuous J K := localSiteInverse_cocontinuous X U V
  change ((SheafOfModules.pushforward (localReturnRingMap X U V)).obj M).IsFinitePresentation
  have : E.inverse.IsEquivalence := E.isEquivalence_inverse
  have : IsIso ((sheafToPresheaf J RingCat.{0}).map (localReturnRingMap X U V)) := by
    change IsIso (Functor.whiskerRight (NatTrans.op E.counit)
      ((forgetRing X.𝒪).over (U.overEquivalence.inverse.obj V).left).obj)
    infer_instance
  have hφ : IsIso (localReturnRingMap X U V) :=
    (fullyFaithfulSheafToPresheaf J RingCat.{0}).isIso_of_isIso_map (localReturnRingMap X U V)
  let : ∀ T : Over (U.overEquivalence.inverse.obj V).left,
      (Over.post (X := T) E.inverse).IsContinuous (J.over T) (K.over _) :=
    fun T => overPost_continuous_of_equivalence J K E.inverse T
  exact finitePresentation_pushforward_of_leftAdjoint (J := K) (K := J)
    (R := (forgetRing (X.restrict U.isOpenEmbedding).𝒪).over V)
    (S := (forgetRing X.𝒪).over (U.overEquivalence.inverse.obj V).left)
    E.inverse (localReturnRingMap X U V) hφ (localReturnUnitIso X U V) (M := M) (hM := inferInstanceAs M.IsFinitePresentation)

set_option backward.isDefEq.respectTransparency.types false in
theorem local_forward_isFiniteType
    (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat) (V : Opens (TopCat.of U))
    (M : SheafOfModules.{0} ((forgetRing X.𝒪).over (U.overEquivalence.inverse.obj V).left))
    [M.IsFiniteType] :
    ((localModuleEquivalence X U V).functor.obj M).IsFiniteType := by
  let E := localSiteEquivalence X U V
  let J := (Opens.grothendieckTopology X.toTopCat).over (U.overEquivalence.inverse.obj V).left
  let K := (Opens.grothendieckTopology (TopCat.of U)).over V
  have : E.functor.IsContinuous K J := localSiteForward_continuous X U V
  have : E.functor.IsCocontinuous K J := localSiteForward_cocontinuous X U V
  have : E.functor.IsEquivalence := E.isEquivalence_functor
  have : IsIso ((sheafToPresheaf K RingCat.{0}).map (localRingMap X U V)) := by
    change IsIso (𝟙 _)
    infer_instance
  have hφ : IsIso (localRingMap X U V) :=
    (fullyFaithfulSheafToPresheaf K RingCat.{0}).isIso_of_isIso_map (localRingMap X U V)
  let : ∀ T : Over V, (Over.post (X := T) E.functor).IsContinuous (K.over T) (J.over _) :=
    fun T => overPost_continuous_of_equivalence K J E.functor T
  exact finiteType_pushforward_of_leftAdjoint (J := J) (K := K)
    (R := (forgetRing X.𝒪).over (U.overEquivalence.inverse.obj V).left)
    (S := (forgetRing (X.restrict U.isOpenEmbedding).𝒪).over V)
    E.functor (localRingMap X U V) hφ (localUnitIso X U V) (M := M) (hM := inferInstanceAs M.IsFiniteType)


end FiniteData

end Hironaka.HironakaChowNativeLocalOverFiniteDataTransport
