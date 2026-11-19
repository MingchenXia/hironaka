import Hironaka.Resolution.HironakaChowNativeLocalOverStalkTransport
import Hironaka.Resolution.HironakaNativeCyclicCokernelRestriction
import Hironaka.Resolution.HironakaChowNativeFreePartContinuation

/-!
# Whole native local/Over restriction equals original image restriction

All section modules retain their actual native actions. The actual inverse-site
source open equals the original image open; the same original ring presheaf
then identifies their scalar maps. No caller comparison is an input.
-/

set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaNativeOriginalRestrictionComparison

open Hironaka.HolomorphicIdealSheaves
  HironakaNativeOpenSectionIdealTransport HironakaNativeCanonicalSupportRestriction
  HironakaNativeCyclicCokernelRestriction HironakaChowNativeFreePartContinuation
  HironakaChowNativePrimeSupportContinuation HironakaChowNativeLocalOverStalkTransport
  HironakaChowNativeLocalOverFiniteDataTransport HironakaSingularModuleSheafStalk
  HironakaSmoothCentreRealDomainActualSheafStalk

variable {n : ℕ}

/-- The literal actual Over restriction followed by accepted native realization. -/
def localOriginalRestrictionFunctor (U : Opens (ComplexModel n)) (D : Opens U) :
    OriginalModules U ⥤ OriginalModules (originalImageOpen U D) :=
  SheafOfModules.overFunctor.{0} (forgetRing (originalOpenStructureSheaf U)) D ⋙
    localOverTransport (originalSpace n) U D

/-- The actual public inverse-site object, before forgetting its original source. -/
abbrev localOriginalSourceObject (U : Opens (ComplexModel n)) (D : Opens U)
    (A : Opens (originalImageOpen U D)) :=
  (localSiteEquivalence (originalSpace n) U D).inverse.obj
    ((originalImageOpen U D).overEquivalence.inverse.obj A)

/-- Equality of the entire original opens, by their actual point-image formulas. -/
theorem localOriginalSourceOpenEq (U : Opens (ComplexModel n)) (D : Opens U)
    (A : Opens (originalImageOpen U D)) :
    (localOriginalSourceObject U D A).left = (cyclicImageFunctor U D).obj A := by
  ext p
  change (p.val ∈ Subtype.val '' (A : Set (originalImageOpen U D))) ↔
    p ∈ originalImageInclusion U D '' (A : Set (originalImageOpen U D))
  constructor
  · rintro ⟨b, hb, h⟩
    exact ⟨b, hb, Subtype.ext h⟩
  · rintro ⟨b, hb, h⟩
    exact ⟨b, hb, congrArg Subtype.val h⟩

private theorem actual_image_image (U : Opens (ComplexModel n)) (D : Opens U)
    (A : Opens (originalImageOpen U D)) :
    actualOpenImage U ((cyclicImageFunctor U D).obj A) =
      actualOpenImage (originalImageOpen U D) A := by
  ext x
  change (∃ u ∈ (cyclicImageFunctor U D).obj A, u.val = x) ↔ ∃ b ∈ A, b.val = x
  constructor
  · rintro ⟨u, ⟨b, hb, hbu⟩, hux⟩
    exact ⟨b, hb, (congrArg Subtype.val hbu).trans hux⟩
  · rintro ⟨b, hb, hbx⟩
    exact ⟨originalImageInclusion U D b, ⟨b, hb, rfl⟩, hbx⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Every scalar uses the same original presheaf arrow, including its native action. -/
theorem localOriginalScalarEq (U : Opens (ComplexModel n)) (D : Opens U)
    (A : Opens (originalImageOpen U D))
    (r : (originalOpenStructureSheaf (originalImageOpen U D)).presheaf.obj (op A)) :
    (originalOpenStructureSheaf U).presheaf.map
        (eqToHom (localOriginalSourceOpenEq U D A).symm).op
        (localOverRingSectionEquiv (originalSpace n) U D A r) =
      (cyclicRestrictionRingMap U D).hom.app (op A) r := by
  rw [cyclicRestrictionRingMap_app]
  let W := originalImageOpen U D
  let OM := (actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf
  let F := (TopologicalSpace.Opens.isOpenEmbedding (X := TopCat.of (ComplexModel n)) U).functor
  let e := (Over.forget W).mapIso
    ((localSiteEquivalence (originalSpace n) U D).counitIso.app
      (W.overEquivalence.inverse.obj A))
  let f := (F.map (eqToHom (localOriginalSourceOpenEq U D A).symm)).op
  let g := e.hom.op
  let h := (eqToHom (actual_image_image U D A)).op
  change OM.map f (OM.map g r) = OM.map h r
  have hm : OM.map g ≫ OM.map f = OM.map h := by
    rw [← OM.map_comp]
    congr 1
  exact ConcreteCategory.congr_hom hm r

set_option backward.isDefEq.respectTransparency.types false in
private def localOriginalSectionLinearMap (U : Opens (ComplexModel n)) (D : Opens U)
    (M : OriginalModules U) (A : Opens (originalImageOpen U D)) :
    ((localOriginalRestrictionFunctor U D).obj M).val.obj (op A) →ₗ[
      (forgetRing (originalOpenStructureSheaf (originalImageOpen U D))).obj.obj (op A)]
      ((originalImageRestrictionFunctor U D).obj M).val.obj (op A) where
  toFun m := M.val.map (eqToHom (localOriginalSourceOpenEq U D A).symm).op
    ((localOverSectionIso (originalSpace n) U D (M.over D) A).hom m)
  map_add' x y := (congrArg
    (M.val.map (eqToHom (localOriginalSourceOpenEq U D A).symm).op)
    (map_add _ x y)).trans (map_add _ _ _)
  map_smul' r m := by
    let e := localOverSectionIso (originalSpace n) U D (M.over D) A
    let f := (eqToHom (localOriginalSourceOpenEq U D A).symm).op
    have he := localOverSectionIso_smul (originalSpace n) U D (M.over D) A r m
    apply (congrArg (fun t => M.val.map f t) he).trans
    exact (M.val.map_smul f (localOverRingSectionEquiv (originalSpace n) U D A r) (e.hom m)).trans
      (congrArg (fun a => a • (M.val.map f (e.hom m))) (localOriginalScalarEq U D A r))

set_option backward.isDefEq.respectTransparency.types false in
/-- Native section modules with their unchanged actions on every actual open. -/
def localOriginalSectionIso (U : Opens (ComplexModel n)) (D : Opens U)
    (M : OriginalModules U) (A : Opens (originalImageOpen U D)) :
    ((localOriginalRestrictionFunctor U D).obj M).val.obj (op A) ≅
      ((originalImageRestrictionFunctor U D).obj M).val.obj (op A) := by
  apply LinearEquiv.toModuleIso
  apply LinearEquiv.ofBijective (localOriginalSectionLinearMap U D M A)
  let q := M.val.presheaf.mapIso (eqToIso (localOriginalSourceOpenEq U D A).symm).op
  let e := localOverSectionIso (originalSpace n) U D (M.over D) A
  change Function.Bijective (fun m => q.hom (e.hom m))
  exact q.addCommGroupIsoToAddEquiv.bijective.comp e.toLinearEquiv.bijective

set_option backward.isDefEq.respectTransparency.types false in
/-- The whole forward map on every native section. -/
theorem localOriginalSectionIso_hom_apply (U : Opens (ComplexModel n)) (D : Opens U)
    (M : OriginalModules U) (A : Opens (originalImageOpen U D))
    (m : ((localOriginalRestrictionFunctor U D).obj M).val.obj (op A)) :
    (localOriginalSectionIso U D M A).hom m =
      M.val.map (eqToHom (localOriginalSourceOpenEq U D A).symm).op
        ((localOverSectionIso (originalSpace n) U D (M.over D) A).hom m) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual inverse on every native section, not only a generating family. -/
theorem localOriginalSectionIso_inv_apply (U : Opens (ComplexModel n)) (D : Opens U)
    (M : OriginalModules U) (A : Opens (originalImageOpen U D))
    (m : ((originalImageRestrictionFunctor U D).obj M).val.obj (op A)) :
    (localOriginalSectionIso U D M A).inv m =
      (localOverSectionIso (originalSpace n) U D (M.over D) A).inv
        (M.val.map (eqToHom (localOriginalSourceOpenEq U D A)).op m) := by
  apply (localOriginalSectionIso U D M A).toLinearEquiv.injective
  change (localOriginalSectionIso U D M A).hom ((localOriginalSectionIso U D M A).inv m) =
    (localOriginalSectionIso U D M A).hom
      ((localOverSectionIso (originalSpace n) U D (M.over D) A).inv
        (M.val.map (eqToHom (localOriginalSourceOpenEq U D A)).op m))
  rw [Iso.inv_hom_id_apply, localOriginalSectionIso_hom_apply, Iso.inv_hom_id_apply]
  let q := M.val.presheaf.mapIso (eqToIso (localOriginalSourceOpenEq U D A).symm).op
  exact (Iso.inv_hom_id_apply q m).symm

set_option backward.isDefEq.respectTransparency.types false in
private def localOriginalObjectIso (U : Opens (ComplexModel n)) (D : Opens U)
    (M : OriginalModules U) :
    (localOriginalRestrictionFunctor U D).obj M ≅ (originalImageRestrictionFunctor U D).obj M := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun A => localOriginalSectionIso U D M A.unop) ?_
  intro A T f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  let eA := localOverSectionIso (originalSpace n) U D (M.over D) A.unop
  let nA := (eqToHom (localOriginalSourceOpenEq U D A.unop).symm).op
  let nT := (eqToHom (localOriginalSourceOpenEq U D T.unop).symm).op
  let F := (originalImageOpen U D).overEquivalence.inverse ⋙
    (localSiteEquivalence (originalSpace n) U D).inverse ⋙ Over.forget D
  let fc := F.op.map f
  let fd := (cyclicImageFunctor U D).op.map f
  have he := localOverSectionIso_restrict (originalSpace n) U D (M.over D) f.unop s
  apply (congrArg (fun t => M.val.map nT t) he).trans
  change M.val.presheaf.map nT (M.val.presheaf.map fc (eA.hom s)) =
    M.val.presheaf.map fd (M.val.presheaf.map nA (eA.hom s))
  have hm : M.val.presheaf.map fc ≫ M.val.presheaf.map nT =
      M.val.presheaf.map nA ≫ M.val.presheaf.map fd := by
    rw [← M.val.presheaf.map_comp, ← M.val.presheaf.map_comp]
    congr 1
  exact ConcreteCategory.congr_hom hm (eA.hom s)

set_option backward.isDefEq.respectTransparency.types false in
/-- The whole native functor isomorphism, natural in every original whole map. -/
def localOriginalRestrictionIso (U : Opens (ComplexModel n)) (D : Opens U) :
    localOriginalRestrictionFunctor U D ≅ originalImageRestrictionFunctor U D := by
  refine NatIso.ofComponents (fun M => localOriginalObjectIso U D M) ?_
  intro M N f
  ext A s
  let eA := localOverSectionIso (originalSpace n) U D (M.over D) A.unop
  let q := (eqToHom (localOriginalSourceOpenEq U D A.unop).symm).op
  have he := ConcreteCategory.congr_hom
    (localOverSectionIso_naturality (originalSpace n) U D (f.over D) A.unop) s
  apply (congrArg (fun t => N.val.map q t) he).trans
  exact (PresheafOfModules.naturality_apply f.val q (eA.hom s)).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The full native forward component is the all-section native linear map. -/
theorem localOriginalRestrictionIso_hom_app (U : Opens (ComplexModel n)) (D : Opens U)
    (M : OriginalModules U) (A : Opens (originalImageOpen U D))
    (m : ((localOriginalRestrictionFunctor U D).obj M).val.obj (op A)) :
    ((localOriginalRestrictionIso U D).app M).hom.val.app (op A) m =
      (localOriginalSectionIso U D M A).hom m := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The full native inverse component is the actual inverse on every section. -/
theorem localOriginalRestrictionIso_inv_app (U : Opens (ComplexModel n)) (D : Opens U)
    (M : OriginalModules U) (A : Opens (originalImageOpen U D))
    (m : ((originalImageRestrictionFunctor U D).obj M).val.obj (op A)) :
    ((localOriginalRestrictionIso U D).app M).inv.val.app (op A) m =
      (localOriginalSectionIso U D M A).inv m := rfl

/-- Every whole original module map retains its full native square. -/
theorem localOriginalRestrictionIso_naturality (U : Opens (ComplexModel n)) (D : Opens U)
    {M N : OriginalModules U} (f : M ⟶ N) :
    (localOriginalRestrictionFunctor U D).map f ≫
        ((localOriginalRestrictionIso U D).app N).hom =
      ((localOriginalRestrictionIso U D).app M).hom ≫
        (originalImageRestrictionFunctor U D).map f :=
  (localOriginalRestrictionIso U D).hom.naturality f

/-- The actual unit, composed from the whole comparison and the native direct unit. -/
def localOriginalRestrictionUnitIso (U : Opens (ComplexModel n)) (D : Opens U) :
    (localOriginalRestrictionFunctor U D).obj
        (SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U))) ≅
      SheafOfModules.unit (forgetRing (originalOpenStructureSheaf (originalImageOpen U D))) :=
  (localOriginalRestrictionIso U D).app
      (SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U))) ≪≫
    originalImageRestrictionUnitIso U D

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual unit forward equation on every native scalar section. -/
theorem localOriginalRestrictionUnitIso_hom_app
    (U : Opens (ComplexModel n)) (D : Opens U) (A : Opens (originalImageOpen U D))
    (r : ((localOriginalRestrictionFunctor U D).obj
      (SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U)))).val.obj (op A)) :
    (localOriginalRestrictionUnitIso U D).hom.val.app (op A) r =
      originalImageScalarEquiv U D A
        ((localOriginalSectionIso U D
          (SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U))) A).hom r) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual unit inverse equation on every native scalar section. -/
theorem localOriginalRestrictionUnitIso_inv_app
    (U : Opens (ComplexModel n)) (D : Opens U) (A : Opens (originalImageOpen U D))
    (r : (originalOpenStructureSheaf (originalImageOpen U D)).presheaf.obj (op A)) :
    (localOriginalRestrictionUnitIso U D).inv.val.app (op A) r =
      (localOriginalSectionIso U D
        (SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U))) A).inv
          ((originalImageScalarEquiv U D A).symm r) := rfl

/-- Every actual unit map retains the entire native numerator square. -/
theorem localOriginalRestriction_unit_map (U : Opens (ComplexModel n)) (D : Opens U)
    (M : OriginalModules U)
    (κ : SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U)) ⟶ M) :
    (localOriginalRestrictionUnitIso U D).inv ≫
        (localOriginalRestrictionFunctor U D).map κ ≫
        ((localOriginalRestrictionIso U D).app M).hom =
      (originalImageRestrictionUnitIso U D).inv ≫
        (originalImageRestrictionFunctor U D).map κ := by
  simp only [localOriginalRestrictionUnitIso, Iso.trans_inv, Category.assoc]
  rw [localOriginalRestrictionIso_naturality]
  simp

/-- Ordinary equality transport of native categories; zero new transport engine. -/
def originalModuleCategoryTransport {B C : Opens (ComplexModel n)} (h : B = C) :
    OriginalModules B ⥤ OriginalModules C := by
  cases h
  exact 𝟭 _

set_option backward.isDefEq.respectTransparency.types false in
/-- Actual two-stage local restriction compared with ONE direct original restriction. -/
def localOriginalNestedRestrictionIso
    (U : Opens (ComplexModel n)) (D₁ D₂ : Opens U) (h₁₂ : D₁ ≤ D₂) :
    (localOriginalRestrictionFunctor U D₂ ⋙
      localOriginalRestrictionFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)) ⋙
        originalModuleCategoryTransport (originalNestedImageEq U D₁ D₂ h₁₂) ≅
      originalImageRestrictionFunctor U D₁ := by
  let W₂ := originalImageOpen U D₂
  let V₁₂ := originalNestedOpen U D₁ D₂
  let c₂ := Functor.isoWhiskerRight (localOriginalRestrictionIso U D₂)
    (localOriginalRestrictionFunctor W₂ V₁₂)
  let c₁₂ := Functor.isoWhiskerLeft (originalImageRestrictionFunctor U D₂)
    (localOriginalRestrictionIso W₂ V₁₂)
  exact Functor.isoWhiskerRight (c₂ ≪≫ c₁₂)
      (originalModuleCategoryTransport (originalNestedImageEq U D₁ D₂ h₁₂)) ≪≫
    originalNestedRestrictionIso U D₁ D₂ h₁₂

end Hironaka.HironakaNativeOriginalRestrictionComparison
