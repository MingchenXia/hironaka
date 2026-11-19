import Hironaka.Resolution.HironakaNativeOpenSectionIdealTransport
import Hironaka.Resolution.HironakaChowNativePrimeSupportContinuation
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward

/-!
# The same original canonical support module on an actual smaller open

Native precomposition retains the original component modules and restricts
their original scalar actions along the inverse actual scalar map.
The support module is the existing public original factory, for ANY subset.
Blueprint FIRST: `hironaka-g10-native-canonical-support-restriction.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaNativeCanonicalSupportRestriction

noncomputable section

open Hironaka.HolomorphicIdealSheaves
  HironakaNativeOpenSectionIdealTransport HironakaChowNativePrimeSupportContinuation
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaSingularModuleSheafStalk
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaActualAnalyticSubspaceResidue
  HironakaActualAnalyticSubspaceLocalFunctions HironakaReducedComplexAnalyticSpaces

variable {n : ℕ}

/-- The actual image-open in the SAME original coordinate space. -/
def originalImageOpen (U : Opens (ComplexModel n)) (D : Opens U) :
    Opens (ComplexModel n) := actualOpenImage U D

private theorem image_le (U : Opens (ComplexModel n)) (D : Opens U) :
    originalImageOpen U D ≤ U := by
  rintro x ⟨u, hu, hux⟩
  exact hux ▸ u.property

/-- The original point inclusion, with its internally derived membership. -/
def originalImageInclusion (U : Opens (ComplexModel n)) (D : Opens U) :
    originalImageOpen U D → U := fun b => ⟨b.val, image_le U D b.property⟩

private theorem inclusion_mem (U : Opens (ComplexModel n)) (D : Opens U)
    (b : originalImageOpen U D) : originalImageInclusion U D b ∈ D := by
  obtain ⟨u, hu, hub⟩ := b.property
  have h : u = originalImageInclusion U D b := Subtype.ext hub
  exact h ▸ hu

/-- The actual nested open carrier and its coordinate image are biholomorphic. -/
def originalImageCarrierIso (U : Opens (ComplexModel n)) (D : Opens U) :
    D ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ originalImageOpen U D where
  toEquiv := {
    toFun := fun d => ⟨d.val.val, ⟨d.val, d.property, rfl⟩⟩
    invFun := fun b => ⟨originalImageInclusion U D b, inclusion_mem U D b⟩
    left_inv := fun d => by apply Subtype.ext; apply Subtype.ext; rfl
    right_inv := fun b => by apply Subtype.ext; rfl }
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (originalImageOpen U D) _).mp
    change ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun d : D => d.val.val)
    exact (contMDiff_subtype_val (U := U)).comp (contMDiff_subtype_val (U := D))
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff D _).mp
    apply (ContMDiff.subtypeVal_comp_iff U _).mp
    exact contMDiff_subtype_val

private def imageTopMap (U : Opens (ComplexModel n)) (D : Opens U) :
    TopCat.of (originalImageOpen U D) ⟶ TopCat.of U :=
  TopCat.ofHom ⟨originalImageInclusion U D,
    continuous_subtype_val.comp (originalImageCarrierIso U D).symm.contMDiff.continuous⟩

private theorem imageTopMap_open (U : Opens (ComplexModel n)) (D : Opens U) :
    Topology.IsOpenEmbedding (imageTopMap U D).hom :=
  D.isOpenEmbedding'.comp (originalImageCarrierIso U D).symm.toHomeomorph.isOpenEmbedding

private def imageFunctor (U : Opens (ComplexModel n)) (D : Opens U) :
    Opens (originalImageOpen U D) ⥤ Opens U := (imageTopMap_open U D).functor

private theorem image_image (U : Opens (ComplexModel n)) (D : Opens U)
    (A : Opens (originalImageOpen U D)) :
    actualOpenImage U ((imageFunctor U D).obj A) =
      actualOpenImage (originalImageOpen U D) A := by
  ext x
  change (∃ u ∈ (imageFunctor U D).obj A, u.val = x) ↔ ∃ b ∈ A, b.val = x
  constructor
  · rintro ⟨u, ⟨b, hb, hbu⟩, hux⟩
    exact ⟨b, hb, (congrArg Subtype.val hbu).trans hux⟩
  · rintro ⟨b, hb, hbx⟩
    exact ⟨originalImageInclusion U D b, ⟨b, hb, rfl⟩, hbx⟩

private def scalarPresheafIso (U : Opens (ComplexModel n)) (D : Opens U) :
    (imageFunctor U D).op ⋙ (originalOpenStructureSheaf U).presheaf ≅
      (originalOpenStructureSheaf (originalImageOpen U D)).presheaf := by
  let a := (TopologicalSpace.Opens.isOpenEmbedding (X := TopCat.of (ComplexModel n)) U).functor
  let b := (TopologicalSpace.Opens.isOpenEmbedding (X := TopCat.of (ComplexModel n))
    (originalImageOpen U D)).functor
  let e : imageFunctor U D ⋙ a ≅ b := NatIso.ofComponents
    (fun A => eqToIso (image_image U D A)) (by intro A T f; apply Subsingleton.elim)
  exact Functor.isoWhiskerRight (NatIso.op e.symm)
    (actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf

/-- The exact original scalar comparison on every actual image-open. -/
def originalImageScalarEquiv (U : Opens (ComplexModel n)) (D : Opens U)
    (A : Opens (originalImageOpen U D)) :
    ↑((originalOpenStructureSheaf U).presheaf.obj (op ((imageFunctor U D).obj A))) ≃+*
      ↑((originalOpenStructureSheaf (originalImageOpen U D)).presheaf.obj (op A)) :=
  ((scalarPresheafIso U D).app (op A)).commRingCatIsoToRingEquiv

private def scalarRingMap (U : Opens (ComplexModel n)) (D : Opens U) :
    (forgetRing (originalOpenStructureSheaf (originalImageOpen U D))).obj ⟶
      (imageFunctor U D).op ⋙ (forgetRing (originalOpenStructureSheaf U)).obj :=
  Functor.whiskerRight (scalarPresheafIso U D).inv (forget₂ CommRingCat RingCat)

/-- Actual original component modules, with native restriction along ell inverse. -/
def originalImageRestrictionFunctor (U : Opens (ComplexModel n)) (D : Opens U) :
    SheafOfModules.{0} (forgetRing (originalOpenStructureSheaf U)) ⥤
      SheafOfModules.{0} (forgetRing (originalOpenStructureSheaf (originalImageOpen U D))) where
  obj M := {
    val := (PresheafOfModules.pushforward (scalarRingMap U D)).obj M.val
    isSheaf := TopCat.Presheaf.isSheaf_of_isOpenEmbedding (imageTopMap_open U D) M.isSheaf }
  map f := ⟨(PresheafOfModules.pushforward (scalarRingMap U D)).map f.val⟩
  map_id M := by ext A s; rfl
  map_comp f g := by ext A s; rfl

/-- The true unit comparison has component ell, with inverse component ell inverse. -/
def originalImageRestrictionUnitIso (U : Opens (ComplexModel n)) (D : Opens U) :
    (originalImageRestrictionFunctor U D).obj
        (SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U))) ≅
      SheafOfModules.unit (forgetRing (originalOpenStructureSheaf (originalImageOpen U D))) := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun A =>
    ModuleCat.restrictScalarsIsoOfEquiv (originalImageScalarEquiv U D A.unop).symm) ?_
  intro A T f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact ConcreteCategory.congr_hom ((scalarPresheafIso U D).hom.naturality f) s

private abbrev coordinateSpace (n : ℕ) :=
  ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) (ComplexModel n)

private abbrev originalOpenSpace (U : Opens (ComplexModel n)) :=
  (coordinateSpace n).restrict (TopologicalSpace.Opens.isOpenEmbedding
    (X := TopCat.of (ComplexModel n)) U)

private abbrev ambientInclusion (U : Opens (ComplexModel n)) :=
  (coordinateSpace n).ofRestrict (TopologicalSpace.Opens.isOpenEmbedding
    (X := TopCat.of (ComplexModel n)) U)

private abbrev nestedAmbientInclusion (U : Opens (ComplexModel n)) (D : Opens U) :=
  (originalOpenSpace U).ofRestrict (TopologicalSpace.Opens.isOpenEmbedding
    (X := TopCat.of U) D) ≫ ambientInclusion U

private instance nestedAmbientInclusion_open (U : Opens (ComplexModel n)) (D : Opens U) :
    LocallyRingedSpace.IsOpenImmersion (nestedAmbientInclusion U D) := by
  change LocallyRingedSpace.IsOpenImmersion
    ((originalOpenSpace U).ofRestrict
      (TopologicalSpace.Opens.isOpenEmbedding (X := TopCat.of U) D) ≫ ambientInclusion U)
  let : LocallyRingedSpace.IsOpenImmersion
      ((originalOpenSpace U).ofRestrict
        (TopologicalSpace.Opens.isOpenEmbedding (X := TopCat.of U) D)) :=
    LocallyRingedSpace.IsOpenImmersion.ofRestrict (originalOpenSpace U) _
  let : LocallyRingedSpace.IsOpenImmersion (ambientInclusion U) :=
    LocallyRingedSpace.IsOpenImmersion.ofRestrict (coordinateSpace n) _
  exact LocallyRingedSpace.IsOpenImmersion.comp _ _

private def sameRangeIso {X Y Z : LocallyRingedSpace} (f : X ⟶ Z) (g : Y ⟶ Z)
    [LocallyRingedSpace.IsOpenImmersion f] [LocallyRingedSpace.IsOpenImmersion g]
    (h : range f.base = range g.base) : X ≅ Y where
  hom := LocallyRingedSpace.IsOpenImmersion.lift g f h.subset
  inv := LocallyRingedSpace.IsOpenImmersion.lift f g h.symm.subset
  hom_inv_id := by
    apply (cancel_mono f).mp
    rw [Category.assoc, LocallyRingedSpace.IsOpenImmersion.lift_fac,
      LocallyRingedSpace.IsOpenImmersion.lift_fac, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono g).mp
    rw [Category.assoc, LocallyRingedSpace.IsOpenImmersion.lift_fac,
      LocallyRingedSpace.IsOpenImmersion.lift_fac, Category.id_comp]

private theorem image_ranges (U : Opens (ComplexModel n)) (D : Opens U) :
    range (ambientInclusion (originalImageOpen U D)).base =
      range (nestedAmbientInclusion U D).base := by
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    obtain ⟨u, hu, hub⟩ := b.property
    exact ⟨⟨u, hu⟩, hub⟩
  · rintro ⟨d, rfl⟩
    exact ⟨⟨d.val.val, ⟨d.val, d.property, rfl⟩⟩, rfl⟩

/-- FULL native comparison of the actual image carrier with the literal nested restriction. -/
def originalImageRestrictionIso (U : Opens (ComplexModel n)) (D : Opens U) :
    originalOpenSpace (originalImageOpen U D) ≅
      (originalOpenSpace U).restrict (TopologicalSpace.Opens.isOpenEmbedding
        (X := TopCat.of U) D) :=
  sameRangeIso (ambientInclusion (originalImageOpen U D))
    (nestedAmbientInclusion U D) (image_ranges U D)

/-- The comparison retains the full SAME original ambient inclusion square. -/
theorem originalImageRestrictionIso_ambient (U : Opens (ComplexModel n)) (D : Opens U) :
    (originalImageRestrictionIso U D).hom ≫ nestedAmbientInclusion U D =
      ambientInclusion (originalImageOpen U D) :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ (image_ranges U D).subset

/-- Every comparison point is exactly the internally derived inverse carrier map. -/
theorem originalImageRestrictionIso_point (U : Opens (ComplexModel n)) (D : Opens U)
    (b : originalImageOpen U D) :
    (originalImageRestrictionIso U D).hom.base b = (originalImageCarrierIso U D).symm b := by
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun f => f.base b) (originalImageRestrictionIso_ambient U D)

private abbrev imageSupport (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U) :=
  (originalImageInclusion U D) ⁻¹' W

private abbrev nestedSupport (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U) :=
  (Subtype.val : D → U) ⁻¹' W

private def supportCarrierIso (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U) :
    actualSubspaceLocallyRingedSpace (n := n) (imageSupport U D W) ≅
      actualSubspaceLocallyRingedSpace (n := n) (nestedSupport U D W) :=
  actualSubspaceBiholomorphicIso (originalImageCarrierIso U D).symm _ _ (fun _ => Iff.rfl)

private def supportOpenMap (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U) :
    actualSubspaceLocallyRingedSpace (n := n) (imageSupport U D W) ⟶
      actualSubspaceLocallyRingedSpace (n := n) W :=
  (supportCarrierIso U D W).hom ≫ actualOpenSubspaceMap (n := n) W D

private instance supportOpenMap_isOpenImmersion
    (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U) :
    LocallyRingedSpace.IsOpenImmersion (supportOpenMap U D W) := by
  change LocallyRingedSpace.IsOpenImmersion
    ((supportCarrierIso U D W).hom ≫ actualOpenSubspaceMap (n := n) W D)
  infer_instance

private def imageSupportOpen (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U)
    (A : Opens (originalImageOpen U D)) : Opens (TopCat.of (imageSupport U D W)) :=
  (Opens.map (actualSubspaceTopInclusion (imageSupport U D W))).obj A

private def oldSupportOpen (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U)
    (A : Opens (originalImageOpen U D)) : Opens (TopCat.of W) :=
  (Opens.map (actualSubspaceTopInclusion W)).obj ((imageFunctor U D).obj A)

private theorem support_open_image (U : Opens (ComplexModel n)) (D : Opens U)
    (W : Set U) (A : Opens (originalImageOpen U D)) :
    (inferInstance : LocallyRingedSpace.IsOpenImmersion (supportOpenMap U D W)).base_open.functor.obj
        (imageSupportOpen U D W A) = oldSupportOpen U D W A := by
  ext w
  constructor
  · rintro ⟨y, hy, hyw⟩
    exact ⟨y.val, hy, congrArg Subtype.val hyw⟩
  · rintro ⟨b, hb, hbw⟩
    change originalImageInclusion U D b = w.val at hbw
    have hbW : originalImageInclusion U D b ∈ W := hbw.symm ▸ w.property
    exact ⟨⟨b, hbW⟩, hb, Subtype.ext hbw⟩

private theorem support_open_preimage (U : Opens (ComplexModel n)) (D : Opens U)
    (W : Set U) (A : Opens (originalImageOpen U D)) :
    (Opens.map (supportOpenMap U D W).base).obj (oldSupportOpen U D W A) =
      imageSupportOpen U D W A := by
  ext y
  change (∃ b ∈ A, originalImageInclusion U D b = originalImageInclusion U D y.val) ↔ y.val ∈ A
  constructor
  · rintro ⟨b, hb, hby⟩
    have h : b = y.val := Subtype.ext (congrArg (fun u : U => u.val) hby)
    exact h ▸ hb
  · intro hy
    exact ⟨y.val, hy, rfl⟩

private def oldSupportFunctor (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U) :
    Opens (originalImageOpen U D) ⥤ Opens (TopCat.of W) :=
  imageFunctor U D ⋙ Opens.map (actualSubspaceTopInclusion W)

private def newSupportFunctor (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U) :
    Opens (originalImageOpen U D) ⥤ Opens (TopCat.of (imageSupport U D W)) :=
  Opens.map (actualSubspaceTopInclusion (imageSupport U D W))

private def supportPreimageIso (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U) :
    oldSupportFunctor U D W ⋙ Opens.map (supportOpenMap U D W).base ≅
      newSupportFunctor U D W :=
  NatIso.ofComponents (fun A => eqToIso (support_open_preimage U D W A))
    (by intro A T f; apply Subsingleton.elim)

private def supportSectionMap (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U) :
    (oldSupportFunctor U D W).op ⋙ (actualSubspaceSheaf (n := n) W).presheaf ⟶
      (newSupportFunctor U D W).op ⋙
        (actualSubspaceSheaf (n := n) (imageSupport U D W)).presheaf :=
  Functor.whiskerLeft (oldSupportFunctor U D W).op (supportOpenMap U D W).c ≫
    (Functor.isoWhiskerRight (NatIso.op (supportPreimageIso U D W).symm)
      (actualSubspaceSheaf (n := n) (imageSupport U D W)).presheaf).hom

private instance supportSectionMap_app_isIso
    (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U)
    (A : (Opens (originalImageOpen U D))ᵒᵖ) :
    IsIso ((supportSectionMap U D W).app A) := by
  have h : IsIso ((supportOpenMap U D W).c.app (op (oldSupportOpen U D W A.unop))) :=
    PresheafedSpace.IsOpenImmersion.c_iso' (supportOpenMap U D W).toHom
      (imageSupportOpen U D W A.unop) (support_open_image U D W A.unop).symm
  change IsIso ((supportOpenMap U D W).c.app (op (oldSupportOpen U D W A.unop)) ≫
    (Functor.isoWhiskerRight (NatIso.op (supportPreimageIso U D W).symm)
      (actualSubspaceSheaf (n := n) (imageSupport U D W)).presheaf).hom.app A)
  exact IsIso.comp_isIso' h
    ((Functor.isoWhiskerRight (NatIso.op (supportPreimageIso U D W).symm)
      (actualSubspaceSheaf (n := n) (imageSupport U D W)).presheaf).app A).isIso_hom

private def supportSectionIso (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U) :
    (oldSupportFunctor U D W).op ⋙ (actualSubspaceSheaf (n := n) W).presheaf ≅
      (newSupportFunctor U D W).op ⋙
        (actualSubspaceSheaf (n := n) (imageSupport U D W)).presheaf :=
  NatIso.ofComponents (fun A => asIso ((supportSectionMap U D W).app A))
    (by intro A T f; exact (supportSectionMap U D W).naturality f)

private def normalizedBaseMap {T : TopCat.{0}} {F G : T.Presheaf CommRingCat.{0}}
    (f : PresheafedSpace.mk T F ⟶ PresheafedSpace.mk T G)
    (hf : f.base = 𝟙 T) : G ⟶ F :=
  f.c ≫ (TopCat.Presheaf.pushforwardEq hf F).hom ≫ (TopCat.Presheaf.Pushforward.id F).hom

private theorem normalizedBaseMap_congr {T : TopCat.{0}} {F G : T.Presheaf CommRingCat.{0}}
    {f g : PresheafedSpace.mk T F ⟶ PresheafedSpace.mk T G} (h : f = g)
    (hf : f.base = 𝟙 T) (hg : g.base = 𝟙 T) :
    normalizedBaseMap f hf = normalizedBaseMap g hg := by
  cases h
  rfl

private theorem normalizedBaseMap_id {T : TopCat.{0}} {F G : T.Presheaf CommRingCat.{0}}
    (c : G ⟶ F) :
    normalizedBaseMap (⟨𝟙 T, c⟩ : PresheafedSpace.mk T F ⟶ PresheafedSpace.mk T G) rfl = c := by
  apply NatTrans.ext
  funext V
  change c.app V ≫ F.map (𝟙 V) ≫ 𝟙 (F.obj V) = c.app V
  rw [F.map_id, Category.comp_id, Category.comp_id]

private theorem nativeComparisonBase (U : Opens (ComplexModel n)) :
    (ChartedSpace.restrictLocallyRingedSpaceIso (IM := 𝓘(ℂ, ComplexModel n)) U).hom.base =
      𝟙 (TopCat.of U) := by
  exact (congrArg (fun f => f.base)
    (actualLiteralStructureRingIso_native (n := n) U)).symm

private def canonicalNativeScalarIso (U : Opens (ComplexModel n)) :
    actualComplexStructureSheaf (n := n) U ≅ originalOpenStructureSheaf U := by
  let e := (LocallyRingedSpace.forgetToSheafedSpace ⋙
    SheafedSpace.forgetToPresheafedSpace).mapIso
      (ChartedSpace.restrictLocallyRingedSpaceIso (IM := 𝓘(ℂ, ComplexModel n)) U)
  let eP := PresheafedSpace.sheafIsoOfIso e
  let eQ := eP ≪≫ TopCat.Presheaf.pushforwardEq (nativeComparisonBase U) _ ≪≫
    TopCat.Presheaf.Pushforward.id _
  exact (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology (TopCat.of U))
    CommRingCat).preimageIso eQ

private theorem canonicalNativeScalarIso_eq (U : Opens (ComplexModel n)) :
    canonicalNativeScalarIso U = (actualLiteralStructureRingIso (n := n) U).symm := by
  apply Iso.ext
  apply (sheafToPresheaf (Opens.grothendieckTopology (TopCat.of U)) CommRingCat).map_injective
  let f : PresheafedSpace.mk (TopCat.of U) (originalOpenStructureSheaf U).presheaf ⟶
      PresheafedSpace.mk (TopCat.of U) (actualComplexStructureSheaf (n := n) U).presheaf :=
    (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace).map
      (ChartedSpace.restrictLocallyRingedSpaceIso (IM := 𝓘(ℂ, ComplexModel n)) U).hom
  have hf : f.base = 𝟙 (TopCat.of U) := nativeComparisonBase U
  change normalizedBaseMap f hf = (actualLiteralStructureRingIso (n := n) U).inv.hom
  have h := normalizedBaseMap_congr
    (show actualLiteralComparisonPresheafHom (n := n) U = f from
      actualLiteralStructureRingIso_native (n := n) U) rfl hf
  exact h.symm.trans (normalizedBaseMap_id _)

private theorem canonicalQuotient_app (U : Opens (ComplexModel n)) (W : Set U)
    (O : Opens U) (r : (originalOpenStructureSheaf U).presheaf.obj (op O)) :
    (originalPrimeSupportQuotient U W).val.app (op O) r =
      (actualSubspaceInclusion (n := n) W).c.app (op O)
        ((actualLiteralStructureRingIso (n := n) U).hom.hom.app (op O) r) := by
  change (actualSubspaceInclusion (n := n) W).c.app (op O)
    ((canonicalNativeScalarIso U).inv.hom.app (op O) r) = _
  exact congrArg ((actualSubspaceInclusion (n := n) W).c.app (op O))
    (ConcreteCategory.congr_hom
      (congrArg (fun e => e.inv.hom.app (op O)) (canonicalNativeScalarIso_eq U)) r)

private theorem canonicalSupport_smul (U : Opens (ComplexModel n)) (W : Set U)
    (O : Opens U) (r : (forgetRing (originalOpenStructureSheaf U)).obj.obj (op O))
    (s : (originalPrimeSupportModule U W).val.obj (op O)) :
    (r • s : (originalPrimeSupportModule U W).val.obj (op O)) =
      (show (actualSubspaceSheaf (n := n) W).presheaf.obj
          (op ((Opens.map (actualSubspaceTopInclusion W)).obj O)) from
        (originalPrimeSupportQuotient U W).val.app (op O) r) *
      (show (actualSubspaceSheaf (n := n) W).presheaf.obj
          (op ((Opens.map (actualSubspaceTopInclusion W)).obj O)) from s) := rfl

private theorem supportOpenMap_point (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U) :
    supportOpenMap U D W ≫ subspacePointMap (n := n) W =
      subspacePointMap (n := n) (imageSupport U D W) := by
  have hD : actualOpenSubspaceMap (n := n) W D ≫ subspacePointMap (n := n) W =
      subspacePointMap (n := n) (nestedSupport U D W) :=
    actualSubspaceMap_point contMDiff_subtype_val (fun _ hx => hx)
  have hE : (supportCarrierIso U D W).hom ≫
      subspacePointMap (n := n) (nestedSupport U D W) =
        subspacePointMap (n := n) (imageSupport U D W) :=
    actualSubspaceMap_point (originalImageCarrierIso U D).symm.contMDiff (fun _ hx => hx)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (supportCarrierIso U D W).hom ≫ k) hD).trans hE)

private theorem supportSectionMap_germ (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U)
    (A : Opens (originalImageOpen U D)) (y : imageSupport U D W) (hy : y.val ∈ A)
    (s : (actualSubspaceSheaf (n := n) W).presheaf.obj (op (oldSupportOpen U D W A))) :
    (actualSubspaceSheaf (n := n) (imageSupport U D W)).presheaf.germ
        (imageSupportOpen U D W A) y hy ((supportSectionMap U D W).app (op A) s) =
      (supportOpenMap U D W).stalkMap y
        ((actualSubspaceSheaf (n := n) W).presheaf.germ (oldSupportOpen U D W A)
          ((supportOpenMap U D W).base y) ⟨y.val, hy, rfl⟩ s) := by
  change (actualSubspaceSheaf (n := n) (imageSupport U D W)).presheaf.germ
    (imageSupportOpen U D W A) y hy
      ((actualSubspaceSheaf (n := n) (imageSupport U D W)).presheaf.map
        (eqToHom (support_open_preimage U D W A).symm).op
        ((supportOpenMap U D W).c.app (op (oldSupportOpen U D W A)) s)) = _
  exact ((actualSubspaceSheaf (n := n) (imageSupport U D W)).presheaf.germ_res_apply
    (eqToHom (support_open_preimage U D W A).symm) y hy _).trans
      (LocallyRingedSpace.stalkMap_germ_apply (supportOpenMap U D W)
        (oldSupportOpen U D W A) y ⟨y.val, hy, rfl⟩ s).symm

private theorem supportSectionMap_eval (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U)
    (A : Opens (originalImageOpen U D)) (y : imageSupport U D W) (hy : y.val ∈ A)
    (s : (actualSubspaceSheaf (n := n) W).presheaf.obj (op (oldSupportOpen U D W A))) :
    actualSubspaceStalkEval (n := n) (imageSupport U D W) y
      ((actualSubspaceSheaf (n := n) (imageSupport U D W)).presheaf.germ
        (imageSupportOpen U D W A) y hy ((supportSectionMap U D W).app (op A) s)) =
      actualSubspaceStalkEval (n := n) W ((supportOpenMap U D W).base y)
        ((actualSubspaceSheaf (n := n) W).presheaf.germ (oldSupportOpen U D W A)
          ((supportOpenMap U D W).base y) ⟨y.val, hy, rfl⟩ s) :=
  (congrArg (actualSubspaceStalkEval (n := n) (imageSupport U D W) y)
    (supportSectionMap_germ U D W A y hy s)).trans
      (actualSubspaceMap_eval_of_point_compatible (supportOpenMap U D W)
        (supportOpenMap_point U D W) y _)

private theorem sectionCast_apply {P Q : Opens (ComplexModel n)} (h : P = Q)
    (s : actualComplexSection (n := n) P) (x : Q) :
    (actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf.map
      (eqToHom h.symm).op s x = s ⟨x.val, h.symm ▸ x.property⟩ := by
  subst Q
  rfl

private theorem original_scalar_value (U : Opens (ComplexModel n)) (D : Opens U)
    (A : Opens (originalImageOpen U D))
    (r : (originalOpenStructureSheaf U).presheaf.obj (op ((imageFunctor U D).obj A)))
    (b : originalImageOpen U D) (hb : b ∈ A) :
    (actualLiteralStructureRingIso (n := n) (originalImageOpen U D)).hom.hom.app
        (op A) (originalImageScalarEquiv U D A r) ⟨b, hb⟩ =
      (actualLiteralStructureRingIso (n := n) U).hom.hom.app
        (op ((imageFunctor U D).obj A)) r
          ⟨originalImageInclusion U D b, ⟨b, hb, rfl⟩⟩ := by
  have hB := actualOpenSectionRingEquiv_apply (n := n) (originalImageOpen U D) A
    (show actualComplexSection (n := n) (actualOpenImage (originalImageOpen U D) A) from
      originalImageScalarEquiv U D A r) ⟨b, hb⟩
  have hU := actualOpenSectionRingEquiv_apply (n := n) U ((imageFunctor U D).obj A)
    (show actualComplexSection (n := n) (actualOpenImage U ((imageFunctor U D).obj A)) from r)
    ⟨originalImageInclusion U D b, ⟨b, hb, rfl⟩⟩
  apply hB.trans
  apply Eq.trans _ hU.symm
  change (actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf.map
    (eqToHom (image_image U D A).symm).op r _ = _
  exact sectionCast_apply (image_image U D A) r _

private theorem canonicalQuotient_eval (U : Opens (ComplexModel n)) (W : Set U)
    (O : Opens U) (y : W) (hy : y.val ∈ O)
    (r : (originalOpenStructureSheaf U).presheaf.obj (op O)) :
    actualSubspaceStalkEval (n := n) W y
      ((actualSubspaceSheaf (n := n) W).presheaf.germ
        ((Opens.map (actualSubspaceTopInclusion W)).obj O) y hy
          ((originalPrimeSupportQuotient U W).val.app (op O) r)) =
      (actualLiteralStructureRingIso (n := n) U).hom.hom.app (op O) r ⟨y.val, hy⟩ := by
  have hq := congrArg (fun s : (actualSubspaceSheaf (n := n) W).presheaf.obj
      (op ((Opens.map (actualSubspaceTopInclusion W)).obj O)) =>
    actualSubspaceStalkEval (n := n) W y
      ((actualSubspaceSheaf (n := n) W).presheaf.germ
        ((Opens.map (actualSubspaceTopInclusion W)).obj O) y hy s))
      (canonicalQuotient_app U W O r)
  exact hq.trans ((congrArg (actualSubspaceStalkEval (n := n) W y)
    (LocallyRingedSpace.stalkMap_germ_apply (actualSubspaceInclusion (n := n) W)
      O y hy ((actualLiteralStructureRingIso (n := n) U).hom.hom.app (op O) r)).symm).trans
        (actualSubspaceStalkEval_inclusion_germ W O _ y hy))

private theorem supportSectionMap_quotient (U : Opens (ComplexModel n)) (D : Opens U)
    (W : Set U) (A : Opens (originalImageOpen U D))
    (r : (originalOpenStructureSheaf U).presheaf.obj (op ((imageFunctor U D).obj A))) :
    (supportSectionMap U D W).app (op A)
        ((originalPrimeSupportQuotient U W).val.app (op ((imageFunctor U D).obj A)) r) =
      (originalPrimeSupportQuotient (originalImageOpen U D) (imageSupport U D W)).val.app
        (op A) (originalImageScalarEquiv U D A r) := by
  apply actualSubspaceSection_ext_eval (imageSupport U D W) (imageSupportOpen U D W A)
  intro y hy
  exact (supportSectionMap_eval U D W A y hy _).trans
    ((canonicalQuotient_eval U W ((imageFunctor U D).obj A)
      ((supportOpenMap U D W).base y) ⟨y.val, hy, rfl⟩ r).trans
        ((original_scalar_value U D A r y.val hy).symm.trans
          (canonicalQuotient_eval (originalImageOpen U D) (imageSupport U D W) A
            y hy (originalImageScalarEquiv U D A r)).symm))

private def supportLinearMap (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U)
    (A : Opens (originalImageOpen U D)) :
    ((originalImageRestrictionFunctor U D).obj (originalPrimeSupportModule U W)).val.obj
        (op A) →ₗ[(forgetRing (originalOpenStructureSheaf (originalImageOpen U D))).obj.obj (op A)]
      (originalPrimeSupportModule (originalImageOpen U D) (imageSupport U D W)).val.obj (op A) where
  toFun := (supportSectionMap U D W).app (op A)
  map_add' := map_add _
  map_smul' r s := by
    change (supportSectionMap U D W).app (op A)
      ((show (actualSubspaceSheaf (n := n) W).presheaf.obj (op (oldSupportOpen U D W A)) from
        (originalPrimeSupportQuotient U W).val.app (op ((imageFunctor U D).obj A))
          ((originalImageScalarEquiv U D A).symm r)) *
        (show (actualSubspaceSheaf (n := n) W).presheaf.obj (op (oldSupportOpen U D W A)) from s)) =
      (show (actualSubspaceSheaf (n := n) (imageSupport U D W)).presheaf.obj
        (op (imageSupportOpen U D W A)) from
          (originalPrimeSupportQuotient (originalImageOpen U D) (imageSupport U D W)).val.app
            (op A) r) *
        (show (actualSubspaceSheaf (n := n) (imageSupport U D W)).presheaf.obj
          (op (imageSupportOpen U D W A)) from (supportSectionMap U D W).app (op A) s)
    have hm := ((supportSectionMap U D W).app (op A)).hom.map_mul
      (show (actualSubspaceSheaf (n := n) W).presheaf.obj (op (oldSupportOpen U D W A)) from
        (originalPrimeSupportQuotient U W).val.app (op ((imageFunctor U D).obj A))
          ((originalImageScalarEquiv U D A).symm r))
      (show (actualSubspaceSheaf (n := n) W).presheaf.obj (op (oldSupportOpen U D W A)) from s)
    apply hm.trans
    apply congrArg (fun t : (actualSubspaceSheaf (n := n) (imageSupport U D W)).presheaf.obj
      (op (imageSupportOpen U D W A)) => t *
        (show (actualSubspaceSheaf (n := n) (imageSupport U D W)).presheaf.obj
          (op (imageSupportOpen U D W A)) from (supportSectionMap U D W).app (op A) s))
    exact (supportSectionMap_quotient U D W A ((originalImageScalarEquiv U D A).symm r)).trans
      (congrArg ((originalPrimeSupportQuotient (originalImageOpen U D)
        (imageSupport U D W)).val.app (op A)) ((originalImageScalarEquiv U D A).apply_symm_apply r))

private def supportComponentIso (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U)
    (A : Opens (originalImageOpen U D)) :
    ((originalImageRestrictionFunctor U D).obj (originalPrimeSupportModule U W)).val.obj (op A) ≅
      (originalPrimeSupportModule (originalImageOpen U D) (imageSupport U D W)).val.obj (op A) :=
  (LinearEquiv.ofBijective (supportLinearMap U D W A)
    (((supportSectionIso U D W).app (op A)).commRingCatIsoToRingEquiv.bijective)).toModuleIso

/-- The SAME original native support module, with all its actual support sections. -/
def canonicalSupportOpenRestrictionIso (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U) :
    (originalImageRestrictionFunctor U D).obj (originalPrimeSupportModule U W) ≅
      originalPrimeSupportModule (originalImageOpen U D) (imageSupport U D W) := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun A => supportComponentIso U D W A.unop) ?_
  intro A T f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact ConcreteCategory.congr_hom ((supportSectionMap U D W).naturality f) s

/-- Every forward component is the actual native open-subspace pullback. -/
theorem canonicalSupportOpenRestrictionIso_hom_app
    (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U)
    (A : Opens (originalImageOpen U D))
    (s : (originalPrimeSupportModule U W).val.obj (op ((imageFunctor U D).obj A))) :
    (canonicalSupportOpenRestrictionIso U D W).hom.val.app (op A) s =
      (supportSectionMap U D W).app (op A) s := rfl

/-- Every inverse component is the inverse of that SAME all-section isomorphism. -/
theorem canonicalSupportOpenRestrictionIso_inv_app
    (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U)
    (A : Opens (originalImageOpen U D))
    (s : (originalPrimeSupportModule (originalImageOpen U D) (imageSupport U D W)).val.obj (op A)) :
    (canonicalSupportOpenRestrictionIso U D W).inv.val.app (op A) s =
      (supportSectionIso U D W).inv.app (op A) s := by
  apply (((supportSectionIso U D W).app (op A)).commRingCatIsoToRingEquiv).injective
  exact ((ConcreteCategory.congr_hom
    (congrArg (fun f => f.val.app (op A))
      (canonicalSupportOpenRestrictionIso U D W).inv_hom_id) s).trans
        (ConcreteCategory.congr_hom
          ((supportSectionIso U D W).inv_hom_id_app (op A)) s).symm)

/-- The full ORIGINAL unit-to-support square, with its genuine unit comparison. -/
theorem canonicalSupportOpenRestrictionIso_quotient
    (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U) :
    (originalImageRestrictionFunctor U D).map (originalPrimeSupportQuotient U W) ≫
        (canonicalSupportOpenRestrictionIso U D W).hom =
      (originalImageRestrictionUnitIso U D).hom ≫
        originalPrimeSupportQuotient (originalImageOpen U D) (imageSupport U D W) := by
  ext A r
  exact supportSectionMap_quotient U D W A.unop r

private def directRestrictionStalkIso (U : Opens (ComplexModel n)) (D : Opens U)
    (M : SheafOfModules.{0} (forgetRing (originalOpenStructureSheaf U)))
    (b : originalImageOpen U D) :
    TopCat.Presheaf.stalk ((originalImageRestrictionFunctor U D).obj M).val.presheaf b ≅
      TopCat.Presheaf.stalk M.val.presheaf (originalImageInclusion U D b) :=
  PresheafedSpace.restrictStalkIso
    (PresheafedSpace.mk (TopCat.of U) M.val.presheaf) (imageTopMap_open U D) b

/-- The entire original stalk, at EVERY ambient point, with no support-membership input. -/
def canonicalSupportRestrictionStalkEquiv
    (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U) (b : originalImageOpen U D) :
    ↑(TopCat.Presheaf.stalk (originalPrimeSupportModule U W).val.presheaf
      (originalImageInclusion U D b)) ≃+
      ↑(TopCat.Presheaf.stalk
        (originalPrimeSupportModule (originalImageOpen U D) (imageSupport U D W)).val.presheaf b) :=
  (directRestrictionStalkIso U D (originalPrimeSupportModule U W) b).symm.addCommGroupIsoToAddEquiv.trans
    ((TopCat.Presheaf.stalkFunctor (X := TopCat.of (originalImageOpen U D)) AddCommGrpCat b).mapIso
      ((PresheafOfModules.toPresheaf _).mapIso ((SheafOfModules.forget _).mapIso
        (canonicalSupportOpenRestrictionIso U D W)))).addCommGroupIsoToAddEquiv

private def scalarReadbackIso (U : Opens (ComplexModel n)) (D : Opens U)
    (b : originalImageOpen U D) :
    TopCat.Presheaf.stalk (X := TopCat.of (originalImageOpen U D))
      ((imageFunctor U D).op ⋙ (originalOpenStructureSheaf U).presheaf) b ≅
      (originalOpenStructureSheaf U).presheaf.stalk (originalImageInclusion U D b) :=
  PresheafedSpace.restrictStalkIso
    (PresheafedSpace.mk (TopCat.of U) (originalOpenStructureSheaf U).presheaf)
    (imageTopMap_open U D) b

/-- The genuine original scalar map on stalks, with the actual open readback. -/
def originalImageStalkRingEquiv (U : Opens (ComplexModel n)) (D : Opens U)
    (b : originalImageOpen U D) :
    ↑((originalOpenStructureSheaf U).presheaf.stalk (originalImageInclusion U D b)) ≃+*
      ↑((originalOpenStructureSheaf (originalImageOpen U D)).presheaf.stalk b) :=
  ((scalarReadbackIso U D b).symm ≪≫
    (TopCat.Presheaf.stalkFunctor (X := TopCat.of (originalImageOpen U D)) CommRingCat b).mapIso
      (scalarPresheafIso U D)).commRingCatIsoToRingEquiv

/-- Every scalar section germ is the SAME native section under ell. -/
theorem originalImageStalkRingEquiv_germ
    (U : Opens (ComplexModel n)) (D : Opens U) (b : originalImageOpen U D)
    (A : Opens (originalImageOpen U D)) (hb : b ∈ A)
    (r : (originalOpenStructureSheaf U).presheaf.obj (op ((imageFunctor U D).obj A))) :
    originalImageStalkRingEquiv U D b
      ((originalOpenStructureSheaf U).presheaf.germ ((imageFunctor U D).obj A)
        (originalImageInclusion U D b) ⟨b, hb, rfl⟩ r) =
      (originalOpenStructureSheaf (originalImageOpen U D)).presheaf.germ A b hb
        (originalImageScalarEquiv U D A r) := by
  change ((TopCat.Presheaf.stalkFunctor (X := TopCat.of (originalImageOpen U D)) CommRingCat b).map
    (scalarPresheafIso U D).hom)
    ((scalarReadbackIso U D b).inv _) = _
  erw [PresheafedSpace.restrictStalkIso_inv_eq_germ_apply
    (PresheafedSpace.mk (TopCat.of U) (originalOpenStructureSheaf U).presheaf)
    (imageTopMap_open U D) A b hb r]
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply
    (X := TopCat.of (originalImageOpen U D)) A b hb (scalarPresheafIso U D).hom r

private theorem supportStalk_germ_image
    (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U) (b : originalImageOpen U D)
    (A : Opens (originalImageOpen U D)) (hb : b ∈ A)
    (s : (originalPrimeSupportModule U W).val.obj (op ((imageFunctor U D).obj A))) :
    canonicalSupportRestrictionStalkEquiv U D W b
      (TopCat.Presheaf.germ (originalPrimeSupportModule U W).val.presheaf
        ((imageFunctor U D).obj A) (originalImageInclusion U D b) ⟨b, hb, rfl⟩ s) =
      TopCat.Presheaf.germ
        (originalPrimeSupportModule (originalImageOpen U D) (imageSupport U D W)).val.presheaf
        A b hb ((canonicalSupportOpenRestrictionIso U D W).hom.val.app (op A) s) := by
  change ((TopCat.Presheaf.stalkFunctor (X := TopCat.of (originalImageOpen U D)) AddCommGrpCat b).map
    ((PresheafOfModules.toPresheaf _).map (canonicalSupportOpenRestrictionIso U D W).hom.val))
      ((directRestrictionStalkIso U D (originalPrimeSupportModule U W) b).inv _) = _
  erw [PresheafedSpace.restrictStalkIso_inv_eq_germ_apply
    (PresheafedSpace.mk (TopCat.of U) (originalPrimeSupportModule U W).val.presheaf)
    (imageTopMap_open U D) A b hb s]
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply A b hb
    ((PresheafOfModules.toPresheaf _).map (canonicalSupportOpenRestrictionIso U D W).hom.val) s

private def inverseImageOpen (U : Opens (ComplexModel n)) (D : Opens U) (O : Opens U) :
    Opens (originalImageOpen U D) := (Opens.map (imageTopMap U D)).obj O

private theorem image_inverseImage_le (U : Opens (ComplexModel n)) (D : Opens U)
    (O : Opens U) : (imageFunctor U D).obj (inverseImageOpen U D O) ≤ O := by
  rintro u ⟨b, hb, rfl⟩
  exact hb

/-- EVERY support-section representative is read on its actual smaller original open. -/
theorem canonicalSupportRestrictionStalkEquiv_germ
    (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U) (b : originalImageOpen U D)
    (O : Opens U) (hb : originalImageInclusion U D b ∈ O)
    (s : (originalPrimeSupportModule U W).val.obj (op O)) :
    canonicalSupportRestrictionStalkEquiv U D W b
      (TopCat.Presheaf.germ (originalPrimeSupportModule U W).val.presheaf O
        (originalImageInclusion U D b) hb s) =
      TopCat.Presheaf.germ
        (originalPrimeSupportModule (originalImageOpen U D) (imageSupport U D W)).val.presheaf
        (inverseImageOpen U D O) b hb
          ((canonicalSupportOpenRestrictionIso U D W).hom.val.app (op (inverseImageOpen U D O))
            ((originalPrimeSupportModule U W).val.map (homOfLE (image_inverseImage_le U D O)).op s)) := by
  have hg := TopCat.Presheaf.germ_res_apply (originalPrimeSupportModule U W).val.presheaf
    (homOfLE (image_inverseImage_le U D O)) (originalImageInclusion U D b) ⟨b, hb, rfl⟩ s
  exact (congrArg (canonicalSupportRestrictionStalkEquiv U D W b) hg.symm).trans
    (supportStalk_germ_image U D W b (inverseImageOpen U D O) hb _)

/-- The inverse formula holds for EVERY support section, without an ambient lift. -/
theorem canonicalSupportRestrictionStalkEquiv_symm_germ
    (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U) (b : originalImageOpen U D)
    (A : Opens (originalImageOpen U D)) (hb : b ∈ A)
    (s : (originalPrimeSupportModule (originalImageOpen U D) (imageSupport U D W)).val.obj (op A)) :
    (canonicalSupportRestrictionStalkEquiv U D W b).symm
      (TopCat.Presheaf.germ
        (originalPrimeSupportModule (originalImageOpen U D) (imageSupport U D W)).val.presheaf
        A b hb s) =
      TopCat.Presheaf.germ (originalPrimeSupportModule U W).val.presheaf
        ((imageFunctor U D).obj A) (originalImageInclusion U D b) ⟨b, hb, rfl⟩
          ((canonicalSupportOpenRestrictionIso U D W).inv.val.app (op A) s) := by
  apply (canonicalSupportRestrictionStalkEquiv U D W b).injective
  rw [AddEquiv.apply_symm_apply]
  have h := supportStalk_germ_image U D W b A hb
    ((canonicalSupportOpenRestrictionIso U D W).inv.val.app (op A) s)
  have hi := ConcreteCategory.congr_hom
    (congrArg (fun f => f.val.app (op A)) (canonicalSupportOpenRestrictionIso U D W).inv_hom_id) s
  exact (h.trans (congrArg
    (TopCat.Presheaf.germ
      (originalPrimeSupportModule (originalImageOpen U D) (imageSupport U D W)).val.presheaf A b hb) hi)).symm

private theorem supportSection_original_smul
    (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U)
    (A : Opens (originalImageOpen U D))
    (r : (forgetRing (originalOpenStructureSheaf U)).obj.obj (op ((imageFunctor U D).obj A)))
    (s : (originalPrimeSupportModule U W).val.obj (op ((imageFunctor U D).obj A))) :
    (canonicalSupportOpenRestrictionIso U D W).hom.val.app (op A) (r • s) =
      (show (forgetRing (originalOpenStructureSheaf (originalImageOpen U D))).obj.obj (op A) from
        originalImageScalarEquiv U D A r) •
        (canonicalSupportOpenRestrictionIso U D W).hom.val.app (op A) s := by
  have h := ((canonicalSupportOpenRestrictionIso U D W).hom.val.app (op A)).hom.map_smul
    (originalImageScalarEquiv U D A r) s
  change (canonicalSupportOpenRestrictionIso U D W).hom.val.app (op A)
    ((show (forgetRing (originalOpenStructureSheaf U)).obj.obj (op ((imageFunctor U D).obj A)) from
      (originalImageScalarEquiv U D A).symm (originalImageScalarEquiv U D A r)) • s) = _ at h
  exact (congrArg (fun a : (forgetRing (originalOpenStructureSheaf U)).obj.obj
      (op ((imageFunctor U D).obj A)) =>
    (canonicalSupportOpenRestrictionIso U D W).hom.val.app (op A) (a • s))
      ((originalImageScalarEquiv U D A).symm_apply_apply r)).symm.trans h

private abbrev originalSupportStalkModule (U : Opens (ComplexModel n)) (W : Set U) (u : U) :
    Module ↑((originalOpenStructureSheaf U).presheaf.stalk u)
      ↑(TopCat.Presheaf.stalk (originalPrimeSupportModule U W).val.presheaf u) :=
  nativeSheafStalkModule (originalOpenStructureSheaf U) (originalPrimeSupportModule U W) u

attribute [local instance] originalSupportStalkModule

private abbrev originalUnitStalkModule (U : Opens (ComplexModel n)) (u : U) :
    Module ↑((originalOpenStructureSheaf U).presheaf.stalk u)
      ↑(TopCat.Presheaf.stalk
        (SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U))).val.presheaf u) :=
  nativeSheafStalkModule (originalOpenStructureSheaf U)
    (SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U))) u

attribute [local instance] originalUnitStalkModule

/-- EVERY native scalar and EVERY actual support stalk element retain their original action. -/
theorem canonicalSupportRestrictionStalkEquiv_smul
    (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U) (b : originalImageOpen U D)
    (r : ↑((originalOpenStructureSheaf U).presheaf.stalk (originalImageInclusion U D b)))
    (m : ↑(TopCat.Presheaf.stalk (originalPrimeSupportModule U W).val.presheaf
      (originalImageInclusion U D b))) :
    canonicalSupportRestrictionStalkEquiv U D W b (r • m) =
      originalImageStalkRingEquiv U D b r • canonicalSupportRestrictionStalkEquiv U D W b m := by
  obtain ⟨O, hbO, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (originalPrimeSupportModule U W).val.presheaf m
  obtain ⟨P, hPO, hbP, a, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq
    (originalOpenStructureSheaf U).presheaf r hbO
  let A := inverseImageOpen U D P
  let sP : (originalPrimeSupportModule U W).val.obj (op P) :=
    (originalPrimeSupportModule U W).val.map (homOfLE hPO).op s
  let sA : (originalPrimeSupportModule U W).val.obj (op ((imageFunctor U D).obj A)) :=
    (originalPrimeSupportModule U W).val.map
    (homOfLE (image_inverseImage_le U D P)).op sP
  let aA : (forgetRing (originalOpenStructureSheaf U)).obj.obj (op ((imageFunctor U D).obj A)) :=
    (originalOpenStructureSheaf U).presheaf.map
    (homOfLE (image_inverseImage_le U D P)).op a
  have hm : TopCat.Presheaf.germ (originalPrimeSupportModule U W).val.presheaf
      ((imageFunctor U D).obj A) (originalImageInclusion U D b) ⟨b, hbP, rfl⟩ sA =
      TopCat.Presheaf.germ (originalPrimeSupportModule U W).val.presheaf O
        (originalImageInclusion U D b) hbO s :=
    (TopCat.Presheaf.germ_res_apply (originalPrimeSupportModule U W).val.presheaf
      (homOfLE (image_inverseImage_le U D P)) (originalImageInclusion U D b)
        ⟨b, hbP, rfl⟩ sP).trans
      (TopCat.Presheaf.germ_res_apply (originalPrimeSupportModule U W).val.presheaf
        (homOfLE hPO) (originalImageInclusion U D b) hbP s)
  have hr := TopCat.Presheaf.germ_res_apply (originalOpenStructureSheaf U).presheaf
    (homOfLE (image_inverseImage_le U D P)) (originalImageInclusion U D b) ⟨b, hbP, rfl⟩ a
  erw [← hm, ← hr]
  erw [← (originalPrimeSupportModule U W).val.germ_smul
    (R := (originalOpenStructureSheaf U).presheaf)]
  erw [supportStalk_germ_image U D W b A hbP (aA • sA),
    supportStalk_germ_image U D W b A hbP sA,
    originalImageStalkRingEquiv_germ U D b A hbP aA]
  exact (congrArg (TopCat.Presheaf.germ
    (originalPrimeSupportModule (originalImageOpen U D) (imageSupport U D W)).val.presheaf A b hbP)
      (supportSection_original_smul U D W A aA sA)).trans
        ((originalPrimeSupportModule (originalImageOpen U D) (imageSupport U D W)).val.germ_smul
          (R := (originalOpenStructureSheaf (originalImageOpen U D)).presheaf) b A hbP _ _)

private theorem exists_scalar_image_germ
    (U : Opens (ComplexModel n)) (D : Opens U) (b : originalImageOpen U D)
    (r : ↑((originalOpenStructureSheaf U).presheaf.stalk (originalImageInclusion U D b))) :
    ∃ (A : Opens (originalImageOpen U D)) (hb : b ∈ A)
      (a : (originalOpenStructureSheaf U).presheaf.obj (op ((imageFunctor U D).obj A))),
      (originalOpenStructureSheaf U).presheaf.germ ((imageFunctor U D).obj A)
        (originalImageInclusion U D b) ⟨b, hb, rfl⟩ a = r := by
  obtain ⟨A, hb, a, ha⟩ := TopCat.Presheaf.exists_germ_eq
    (X := TopCat.of (originalImageOpen U D))
    ((imageFunctor U D).op ⋙ (originalOpenStructureSheaf U).presheaf)
      ((scalarReadbackIso U D b).inv r)
  refine ⟨A, hb, a, ?_⟩
  have hg := PresheafedSpace.restrictStalkIso_hom_eq_germ_apply
    (PresheafedSpace.mk (TopCat.of U) (originalOpenStructureSheaf U).presheaf)
    (imageTopMap_open U D) A b hb a
  exact hg.symm.trans ((congrArg (scalarReadbackIso U D b).hom ha).trans
    (ConcreteCategory.congr_hom (scalarReadbackIso U D b).inv_hom_id r))

private def ambientScalarReadbackIso (U : Opens (ComplexModel n)) (u : U) :
    (originalOpenStructureSheaf U).presheaf.stalk u ≅
      (actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf.stalk u.val := by
  let X := PresheafedSpace.mk (TopCat.of (ComplexModel n))
    (actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf
  let i : TopCat.of U ⟶ TopCat.of (ComplexModel n) :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  exact PresheafedSpace.restrictStalkIso X (f := i) U.isOpenEmbedding' u

private theorem ambientScalarReadbackIso_germ (U : Opens (ComplexModel n)) (u : U)
    (O : Opens U) (hu : u ∈ O)
    (r : (originalOpenStructureSheaf U).presheaf.obj (op O)) :
    (ambientScalarReadbackIso U u).hom
      ((originalOpenStructureSheaf U).presheaf.germ O u hu r) =
      (actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf.germ
        (actualOpenImage U O) u.val ⟨u, hu, rfl⟩ r := by
  let X := PresheafedSpace.mk (TopCat.of (ComplexModel n))
    (actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf
  let i : TopCat.of U ⟶ TopCat.of (ComplexModel n) :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  exact PresheafedSpace.restrictStalkIso_hom_eq_germ_apply X (f := i) U.isOpenEmbedding' O u hu r

/-- The scalar map is exactly gamma-B composed with inverse gamma-U of the SAME original ambient. -/
theorem originalImageStalkRingEquiv_original
    (U : Opens (ComplexModel n)) (D : Opens U) (b : originalImageOpen U D)
    (r : ↑((originalOpenStructureSheaf U).presheaf.stalk (originalImageInclusion U D b))) :
    originalImageStalkRingEquiv U D b r =
      actualOriginalRestrictionStalkEquiv (n := n) (originalImageOpen U D) b
        ((actualOriginalRestrictionStalkEquiv (n := n) U
          (originalImageInclusion U D b)).symm r) := by
  obtain ⟨A, hb, a, rfl⟩ := exists_scalar_image_germ U D b r
  apply (actualOriginalRestrictionStalkEquiv (n := n) (originalImageOpen U D) b).symm.injective
  erw [RingEquiv.symm_apply_apply, originalImageStalkRingEquiv_germ U D b A hb a]
  change (ambientScalarReadbackIso (originalImageOpen U D) b).hom
        ((originalOpenStructureSheaf (originalImageOpen U D)).presheaf.germ A b hb
          (originalImageScalarEquiv U D A a)) =
    (ambientScalarReadbackIso U (originalImageInclusion U D b)).hom
        ((originalOpenStructureSheaf U).presheaf.germ ((imageFunctor U D).obj A)
          (originalImageInclusion U D b) ⟨b, hb, rfl⟩ a)
  apply (ambientScalarReadbackIso_germ (originalImageOpen U D) b A hb _).trans
  apply Eq.trans _ (ambientScalarReadbackIso_germ U (originalImageInclusion U D b)
    ((imageFunctor U D).obj A) ⟨b, hb, rfl⟩ a).symm
  change (actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf.germ
    (actualOpenImage (originalImageOpen U D) A) b.val _
      ((actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf.map
        (eqToHom (image_image U D A).symm).op a) = _
  exact (actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf.germ_res_apply
    (eqToHom (image_image U D A).symm) b.val _ a

/-- The inverse retains the inverse SAME native scalar action. -/
theorem canonicalSupportRestrictionStalkEquiv_symm_smul
    (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U) (b : originalImageOpen U D)
    (r : ↑((originalOpenStructureSheaf (originalImageOpen U D)).presheaf.stalk b))
    (m : ↑(TopCat.Presheaf.stalk
      (originalPrimeSupportModule (originalImageOpen U D) (imageSupport U D W)).val.presheaf b)) :
    (canonicalSupportRestrictionStalkEquiv U D W b).symm (r • m) =
      (originalImageStalkRingEquiv U D b).symm r •
        (canonicalSupportRestrictionStalkEquiv U D W b).symm m := by
  apply (canonicalSupportRestrictionStalkEquiv U D W b).injective
  erw [AddEquiv.apply_symm_apply, canonicalSupportRestrictionStalkEquiv_smul,
    RingEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- The existing ORIGINAL unit map on its native ring/module stalks. -/
def canonicalSupportQuotientStalkMap (U : Opens (ComplexModel n)) (W : Set U) (u : U) :
    ↑((originalOpenStructureSheaf U).presheaf.stalk u) →ₗ[↑((originalOpenStructureSheaf U).presheaf.stalk u)]
      ↑(TopCat.Presheaf.stalk (originalPrimeSupportModule U W).val.presheaf u) :=
  (stalkLinearMap (R := (originalOpenStructureSheaf U).presheaf)
    (originalPrimeSupportQuotient U W).val u).comp
      (unitStalkLinearEquiv (originalOpenStructureSheaf U) u).symm.toLinearMap

private theorem canonicalSupportQuotientStalkMap_germ
    (U : Opens (ComplexModel n)) (W : Set U) (u : U) (O : Opens U) (hu : u ∈ O)
    (r : (originalOpenStructureSheaf U).presheaf.obj (op O)) :
    canonicalSupportQuotientStalkMap U W u
      ((originalOpenStructureSheaf U).presheaf.germ O u hu r) =
      TopCat.Presheaf.germ (originalPrimeSupportModule U W).val.presheaf O u hu
        ((originalPrimeSupportQuotient U W).val.app (op O) r) := by
  have h : (unitStalkLinearEquiv (originalOpenStructureSheaf U) u).symm
      ((originalOpenStructureSheaf U).presheaf.germ O u hu r) =
      TopCat.Presheaf.germ
        (SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U))).val.presheaf O u hu r := by
    apply (unitStalkLinearEquiv (originalOpenStructureSheaf U) u).injective
    exact ((unitStalkLinearEquiv (originalOpenStructureSheaf U) u).apply_symm_apply _).trans
      (unitStalkLinearEquiv_germ (originalOpenStructureSheaf U) u O hu r).symm
  change stalkLinearMap (originalPrimeSupportQuotient U W).val u
    ((unitStalkLinearEquiv (originalOpenStructureSheaf U) u).symm _) = _
  erw [h]
  exact stalkLinearMap_germ (originalPrimeSupportQuotient U W).val u O hu r

/-- EVERY original scalar numerator satisfies the full native stalk unit square. -/
theorem canonicalSupportRestrictionStalkEquiv_quotient
    (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U) (b : originalImageOpen U D)
    (r : ↑((originalOpenStructureSheaf U).presheaf.stalk (originalImageInclusion U D b))) :
    canonicalSupportRestrictionStalkEquiv U D W b
      (canonicalSupportQuotientStalkMap U W (originalImageInclusion U D b) r) =
      canonicalSupportQuotientStalkMap (originalImageOpen U D) (imageSupport U D W) b
        (originalImageStalkRingEquiv U D b r) := by
  obtain ⟨A, hb, a, rfl⟩ := exists_scalar_image_germ U D b r
  erw [canonicalSupportQuotientStalkMap_germ,
    supportStalk_germ_image U D W b A hb,
    originalImageStalkRingEquiv_germ U D b A hb,
    canonicalSupportQuotientStalkMap_germ]
  exact congrArg (TopCat.Presheaf.germ
    (originalPrimeSupportModule (originalImageOpen U D) (imageSupport U D W)).val.presheaf A b hb)
      (supportSectionMap_quotient U D W A a)

/-- The inverse numerator formula holds without surjectivity of either unit map. -/
theorem canonicalSupportRestrictionStalkEquiv_symm_quotient
    (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U) (b : originalImageOpen U D)
    (r : ↑((originalOpenStructureSheaf (originalImageOpen U D)).presheaf.stalk b)) :
    (canonicalSupportRestrictionStalkEquiv U D W b).symm
      (canonicalSupportQuotientStalkMap (originalImageOpen U D) (imageSupport U D W) b r) =
      canonicalSupportQuotientStalkMap U W (originalImageInclusion U D b)
        ((originalImageStalkRingEquiv U D b).symm r) := by
  apply (canonicalSupportRestrictionStalkEquiv U D W b).injective
  erw [AddEquiv.apply_symm_apply, canonicalSupportRestrictionStalkEquiv_quotient,
    RingEquiv.apply_symm_apply]

private abbrev intrinsicAmbientInclusion (U : Opens (ComplexModel n)) :=
  ChartedSpace.locallyRingedSpaceMap (IM := 𝓘(ℂ, ComplexModel n))
    (IN := 𝓘(ℂ, ComplexModel n)) (Subtype.val : U → ComplexModel n) contMDiff_subtype_val

private theorem nativeComparison_ambient (U : Opens (ComplexModel n)) :
    (ChartedSpace.restrictLocallyRingedSpaceIso (IM := 𝓘(ℂ, ComplexModel n)) U).hom ≫
        intrinsicAmbientInclusion U = ambientInclusion U :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ (by rfl)

/-- The actual native inclusion between the SAME original coordinate restrictions. -/
def originalImageNativeInclusion (U : Opens (ComplexModel n)) (D : Opens U) :
    originalOpenSpace (originalImageOpen U D) ⟶ originalOpenSpace U :=
  (originalImageRestrictionIso U D).hom ≫
    (originalOpenSpace U).ofRestrict (TopologicalSpace.Opens.isOpenEmbedding (X := TopCat.of U) D)

theorem originalImageNativeInclusion_ambient (U : Opens (ComplexModel n)) (D : Opens U) :
    originalImageNativeInclusion U D ≫ ambientInclusion U =
      ambientInclusion (originalImageOpen U D) :=
  (Category.assoc _ _ _).trans (originalImageRestrictionIso_ambient U D)

theorem originalImageNativeInclusion_point (U : Opens (ComplexModel n)) (D : Opens U)
    (b : originalImageOpen U D) :
    (originalImageNativeInclusion U D).base b = originalImageInclusion U D b :=
  congrArg Subtype.val (originalImageRestrictionIso_point U D b)

private theorem imageInclusion_contMDiff (U : Opens (ComplexModel n)) (D : Opens U) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (originalImageInclusion U D) :=
  (contMDiff_subtype_val (U := D)).comp (originalImageCarrierIso U D).symm.contMDiff

private abbrev intrinsicImageInclusion (U : Opens (ComplexModel n)) (D : Opens U) :=
  ChartedSpace.locallyRingedSpaceMap (IM := 𝓘(ℂ, ComplexModel n))
    (IN := 𝓘(ℂ, ComplexModel n)) (originalImageInclusion U D) (imageInclusion_contMDiff U D)

private theorem intrinsicImageInclusion_ambient (U : Opens (ComplexModel n)) (D : Opens U) :
    intrinsicImageInclusion U D ≫ intrinsicAmbientInclusion U =
      intrinsicAmbientInclusion (originalImageOpen U D) := rfl

/-- FULL native compatibility with the actual holomorphic inclusion, retaining both scalar maps. -/
theorem originalImageNativeInclusion_actual (U : Opens (ComplexModel n)) (D : Opens U) :
    originalImageNativeInclusion U D ≫
        (ChartedSpace.restrictLocallyRingedSpaceIso (IM := 𝓘(ℂ, ComplexModel n)) U).hom =
      (ChartedSpace.restrictLocallyRingedSpaceIso (IM := 𝓘(ℂ, ComplexModel n))
        (originalImageOpen U D)).hom ≫ intrinsicImageInclusion U D := by
  apply (cancel_mono (intrinsicAmbientInclusion U)).mp
  calc
    _ = originalImageNativeInclusion U D ≫ ambientInclusion U := by
      rw [Category.assoc, nativeComparison_ambient]
    _ = ambientInclusion (originalImageOpen U D) := originalImageNativeInclusion_ambient U D
    _ = _ := by rw [Category.assoc, intrinsicImageInclusion_ambient, nativeComparison_ambient]

private theorem intrinsicImage_preimage (U : Opens (ComplexModel n)) (D : Opens U)
    (A : Opens (originalImageOpen U D)) :
    (Opens.map (intrinsicImageInclusion U D).base).obj ((imageFunctor U D).obj A) = A := by
  ext b
  change (∃ a ∈ A, originalImageInclusion U D a = originalImageInclusion U D b) ↔ b ∈ A
  constructor
  · rintro ⟨a, ha, hab⟩
    exact (Subtype.ext (congrArg (fun u : U => u.val) hab) : a = b) ▸ ha
  · intro hb
    exact ⟨b, hb, rfl⟩

private def intrinsicImageSectionMap (U : Opens (ComplexModel n)) (D : Opens U)
    (A : Opens (originalImageOpen U D)) :
    (actualComplexStructureSheaf (n := n) U).presheaf.obj (op ((imageFunctor U D).obj A)) ⟶
      (actualComplexStructureSheaf (n := n) (originalImageOpen U D)).presheaf.obj (op A) :=
  (intrinsicImageInclusion U D).c.app (op ((imageFunctor U D).obj A)) ≫
    (actualComplexStructureSheaf (n := n) (originalImageOpen U D)).presheaf.map
      (eqToHom (intrinsicImage_preimage U D A).symm).op

/-- The FULL intrinsic scalar-section square on every actual image open. -/
theorem originalImageScalarEquiv_intrinsic (U : Opens (ComplexModel n)) (D : Opens U)
    (A : Opens (originalImageOpen U D))
    (r : (originalOpenStructureSheaf U).presheaf.obj (op ((imageFunctor U D).obj A))) :
    (actualLiteralStructureRingIso (n := n) (originalImageOpen U D)).hom.hom.app (op A)
        (originalImageScalarEquiv U D A r) =
      intrinsicImageSectionMap U D A
        ((actualLiteralStructureRingIso (n := n) U).hom.hom.app (op ((imageFunctor U D).obj A)) r) := by
  apply Subtype.ext
  funext b
  change (actualLiteralStructureRingIso (n := n) (originalImageOpen U D)).hom.hom.app (op A)
      (originalImageScalarEquiv U D A r) b =
    (actualLiteralStructureRingIso (n := n) U).hom.hom.app (op ((imageFunctor U D).obj A)) r
      ⟨originalImageInclusion U D b.val, ⟨b.val, b.property, rfl⟩⟩
  exact original_scalar_value U D A r b.val b.property

/-- The original scalar comparison commutes with EVERY smaller actual open. -/
theorem originalImageScalarEquiv_naturality
    (U : Opens (ComplexModel n)) (D : Opens U)
    (A T : Opens (originalImageOpen U D)) (hTA : T ≤ A)
    (r : (originalOpenStructureSheaf U).presheaf.obj (op ((imageFunctor U D).obj A))) :
    (originalOpenStructureSheaf (originalImageOpen U D)).presheaf.map (homOfLE hTA).op
      (originalImageScalarEquiv U D A r) =
    originalImageScalarEquiv U D T
      ((originalOpenStructureSheaf U).presheaf.map ((imageFunctor U D).map (homOfLE hTA)).op r) :=
  (ConcreteCategory.congr_hom ((scalarPresheafIso U D).hom.naturality (homOfLE hTA).op) r).symm

/-- Inverse scalar sections obey the inverse original restriction square. -/
theorem originalImageScalarEquiv_symm_naturality
    (U : Opens (ComplexModel n)) (D : Opens U)
    (A T : Opens (originalImageOpen U D)) (hTA : T ≤ A)
    (r : (originalOpenStructureSheaf (originalImageOpen U D)).presheaf.obj (op A)) :
    (originalOpenStructureSheaf U).presheaf.map ((imageFunctor U D).map (homOfLE hTA)).op
      ((originalImageScalarEquiv U D A).symm r) =
    (originalImageScalarEquiv U D T).symm
      ((originalOpenStructureSheaf (originalImageOpen U D)).presheaf.map (homOfLE hTA).op r) :=
  (ConcreteCategory.congr_hom ((scalarPresheafIso U D).inv.naturality (homOfLE hTA).op) r).symm

/-- The genuine unit comparison is ell on EVERY original component. -/
theorem originalImageRestrictionUnitIso_hom_app
    (U : Opens (ComplexModel n)) (D : Opens U) (A : Opens (originalImageOpen U D))
    (r : (originalOpenStructureSheaf U).presheaf.obj (op ((imageFunctor U D).obj A))) :
    (originalImageRestrictionUnitIso U D).hom.val.app (op A) r =
      originalImageScalarEquiv U D A r := rfl

private theorem nativeImage_preimage (U : Opens (ComplexModel n)) (D : Opens U)
    (A : Opens (originalImageOpen U D)) :
    (Opens.map (originalImageNativeInclusion U D).base).obj ((imageFunctor U D).obj A) = A := by
  ext b
  change (originalImageNativeInclusion U D).base b ∈ (imageFunctor U D).obj A ↔ b ∈ A
  have hp := originalImageNativeInclusion_point U D (show originalImageOpen U D from b)
  exact (Iff.of_eq (congrArg (fun u : U => u ∈ (imageFunctor U D).obj A) hp)).trans
    (Iff.of_eq (congrArg (fun O => b ∈ O) (intrinsicImage_preimage U D A)))

private theorem nativeImage_scalar_raw (U : Opens (ComplexModel n)) (D : Opens U) :
    (originalImageNativeInclusion U D).toHom ≫ actualLiteralComparisonPresheafHom (n := n) U =
      actualLiteralComparisonPresheafHom (n := n) (originalImageOpen U D) ≫
        (intrinsicImageInclusion U D).toHom := by
  let F := LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace
  have h := congrArg (fun f => F.map f) (originalImageNativeInclusion_actual U D)
  rw [F.map_comp, F.map_comp, ← actualLiteralStructureRingIso_native,
    ← actualLiteralStructureRingIso_native] at h
  exact h

private theorem normalized_scalar_square
    {T S : TopCat.{0}} {RT GT : T.Presheaf CommRingCat.{0}}
    {RS GS : S.Presheaf CommRingCat.{0}} (eT : RT ≅ GT) (eS : RS ≅ GS)
    (j : PresheafedSpace.mk S RS ⟶ PresheafedSpace.mk T RT)
    (i : PresheafedSpace.mk S GS ⟶ PresheafedSpace.mk T GT)
    (H : j ≫ (⟨𝟙 T, eT.inv⟩ : PresheafedSpace.mk T RT ⟶ PresheafedSpace.mk T GT) =
      (⟨𝟙 S, eS.inv⟩ : PresheafedSpace.mk S RS ⟶ PresheafedSpace.mk S GS) ≫ i)
    (O : Opens T) (A : Opens S) (hj : (Opens.map j.base).obj O = A)
    (hi : (Opens.map i.base).obj O = A) :
    j.c.app (op O) ≫ RS.map (eqToHom hj.symm).op =
      eT.hom.app (op O) ≫ i.c.app (op O) ≫ GS.map (eqToHom hi.symm).op ≫ eS.inv.app (op A) := by
  have hc := PresheafedSpace.congr_app H (op O)
  simp only [PresheafedSpace.comp_c_app] at hc
  change eT.inv.app (op O) ≫ j.c.app (op O) =
    i.c.app (op O) ≫ eS.inv.app (op ((Opens.map i.base).obj O)) ≫
      RS.map (eqToHom (congrArg op (hi.trans hj.symm))) at hc
  have hcast : RS.map (eqToHom (congrArg op (hi.trans hj.symm))) ≫
      RS.map (eqToHom hj.symm).op = RS.map (eqToHom hi.symm).op := by
    rw [← RS.map_comp]
    congr 1
  calc
    _ = eT.hom.app (op O) ≫ (eT.inv.app (op O) ≫ j.c.app (op O)) ≫
        RS.map (eqToHom hj.symm).op := by
      simp only [← Category.assoc, eT.hom_inv_id_app, Category.id_comp]
    _ = eT.hom.app (op O) ≫
        (i.c.app (op O) ≫ eS.inv.app (op ((Opens.map i.base).obj O)) ≫
          RS.map (eqToHom (congrArg op (hi.trans hj.symm)))) ≫ RS.map (eqToHom hj.symm).op := by rw [hc]
    _ = eT.hom.app (op O) ≫ i.c.app (op O) ≫
        eS.inv.app (op ((Opens.map i.base).obj O)) ≫ RS.map (eqToHom hi.symm).op := by
      simp only [Category.assoc]
      rw [hcast]
    _ = _ := by rw [eS.inv.naturality (eqToHom hi.symm).op]

private def nativeImageScalarSectionMap (U : Opens (ComplexModel n)) (D : Opens U)
    (A : Opens (originalImageOpen U D)) :
    (originalOpenStructureSheaf U).presheaf.obj (op ((imageFunctor U D).obj A)) ⟶
      (originalOpenStructureSheaf (originalImageOpen U D)).presheaf.obj (op A) :=
  (originalImageNativeInclusion U D).c.app (op ((imageFunctor U D).obj A)) ≫
    (originalOpenStructureSheaf (originalImageOpen U D)).presheaf.map
      (eqToHom (nativeImage_preimage U D A).symm).op

/-- ell is EXACTLY the native original inclusion component, after its derived preimage equality. -/
theorem originalImageScalarEquiv_native (U : Opens (ComplexModel n)) (D : Opens U)
    (A : Opens (originalImageOpen U D))
    (r : (originalOpenStructureSheaf U).presheaf.obj (op ((imageFunctor U D).obj A))) :
    nativeImageScalarSectionMap U D A r = originalImageScalarEquiv U D A r := by
  have h := normalized_scalar_square
    ((sheafToPresheaf (Opens.grothendieckTopology (TopCat.of U)) CommRingCat).mapIso
      (actualLiteralStructureRingIso (n := n) U))
    ((sheafToPresheaf (Opens.grothendieckTopology (TopCat.of (originalImageOpen U D)))
      CommRingCat).mapIso (actualLiteralStructureRingIso (n := n) (originalImageOpen U D)))
    (originalImageNativeInclusion U D).toHom (intrinsicImageInclusion U D).toHom
    (nativeImage_scalar_raw U D) ((imageFunctor U D).obj A) A
    (nativeImage_preimage U D A) (intrinsicImage_preimage U D A)
  have hr := ConcreteCategory.congr_hom h r
  change nativeImageScalarSectionMap U D A r =
    (actualLiteralStructureRingIso (n := n) (originalImageOpen U D)).inv.hom.app (op A)
      (intrinsicImageSectionMap U D A
        ((actualLiteralStructureRingIso (n := n) U).hom.hom.app (op ((imageFunctor U D).obj A)) r)) at hr
  exact hr.trans ((congrArg
    ((actualLiteralStructureRingIso (n := n) (originalImageOpen U D)).inv.hom.app (op A))
      (originalImageScalarEquiv_intrinsic U D A r)).symm.trans
        (ConcreteCategory.congr_hom
          (congrArg (fun f => f.hom.app (op A))
            (actualLiteralStructureRingIso (n := n) (originalImageOpen U D)).hom_inv_id) _))

private theorem scalarStalk_cast_germ {T : TopCat.{0}} (R : T.Presheaf CommRingCat.{0})
    {x y : T} (h : x = y) (O : Opens T) (hx : x ∈ O) (r : R.obj (op O)) :
    (eqToHom (congrArg (fun p => R.stalk p) h)) (R.germ O x hx r) =
      R.germ O y (h ▸ hx) r := by
  cases h
  rfl

private def nativeImageStalkMap (U : Opens (ComplexModel n)) (D : Opens U)
    (b : originalImageOpen U D) :
    (originalOpenStructureSheaf U).presheaf.stalk (originalImageInclusion U D b) ⟶
      (originalOpenStructureSheaf (originalImageOpen U D)).presheaf.stalk b :=
  eqToHom (congrArg (fun u : U => (originalOpenStructureSheaf U).presheaf.stalk u)
    (originalImageNativeInclusion_point U D b).symm) ≫
      (originalImageNativeInclusion U D).stalkMap b

private theorem nativeImageStalkMap_germ
    (U : Opens (ComplexModel n)) (D : Opens U) (b : originalImageOpen U D)
    (A : Opens (originalImageOpen U D)) (hb : b ∈ A)
    (r : (originalOpenStructureSheaf U).presheaf.obj (op ((imageFunctor U D).obj A))) :
    nativeImageStalkMap U D b
      ((originalOpenStructureSheaf U).presheaf.germ ((imageFunctor U D).obj A)
        (originalImageInclusion U D b) ⟨b, hb, rfl⟩ r) =
      (originalOpenStructureSheaf (originalImageOpen U D)).presheaf.germ A b hb
        (originalImageScalarEquiv U D A r) := by
  have hcast := scalarStalk_cast_germ (originalOpenStructureSheaf U).presheaf
    (originalImageNativeInclusion_point U D b).symm ((imageFunctor U D).obj A) ⟨b, hb, rfl⟩ r
  have hj := LocallyRingedSpace.stalkMap_germ_apply (originalImageNativeInclusion U D)
    ((imageFunctor U D).obj A) b
      ((originalImageNativeInclusion_point U D b).symm ▸ (show originalImageInclusion U D b ∈
        (imageFunctor U D).obj A from ⟨b, hb, rfl⟩)) r
  have hn := (originalOpenStructureSheaf (originalImageOpen U D)).presheaf.germ_res_apply
    (eqToHom (nativeImage_preimage U D A).symm) b hb
      ((originalImageNativeInclusion U D).c.app (op ((imageFunctor U D).obj A)) r)
  exact (congrArg ((originalImageNativeInclusion U D).stalkMap b) hcast).trans
    (hj.trans (hn.symm.trans (congrArg
      ((originalOpenStructureSheaf (originalImageOpen U D)).presheaf.germ A b hb)
        (originalImageScalarEquiv_native U D A r))))

/-- The whole scalar equivalence is the SAME native original inclusion stalk map. -/
theorem originalImageStalkRingEquiv_native
    (U : Opens (ComplexModel n)) (D : Opens U) (b : originalImageOpen U D)
    (r : ↑((originalOpenStructureSheaf U).presheaf.stalk (originalImageInclusion U D b))) :
    originalImageStalkRingEquiv U D b r = nativeImageStalkMap U D b r := by
  obtain ⟨A, hb, a, rfl⟩ := exists_scalar_image_germ U D b r
  exact (originalImageStalkRingEquiv_germ U D b A hb a).trans
    (nativeImageStalkMap_germ U D b A hb a).symm

/-- Every support-section restriction square is the FULL native module-map naturality. -/
theorem canonicalSupportOpenRestrictionIso_restrict
    (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U)
    (A T : Opens (originalImageOpen U D)) (hTA : T ≤ A)
    (s : (originalPrimeSupportModule U W).val.obj (op ((imageFunctor U D).obj A))) :
    (canonicalSupportOpenRestrictionIso U D W).hom.val.app (op T)
      ((originalPrimeSupportModule U W).val.map ((imageFunctor U D).map (homOfLE hTA)).op s) =
    (originalPrimeSupportModule (originalImageOpen U D) (imageSupport U D W)).val.map
      (homOfLE hTA).op ((canonicalSupportOpenRestrictionIso U D W).hom.val.app (op A) s) :=
  PresheafOfModules.naturality_apply (canonicalSupportOpenRestrictionIso U D W).hom.val
    (homOfLE hTA).op s

private def transportOriginalModules {B C : Opens (ComplexModel n)} (h : B = C) :
    SheafOfModules.{0} (forgetRing (originalOpenStructureSheaf B)) ⥤
      SheafOfModules.{0} (forgetRing (originalOpenStructureSheaf C)) := by
  cases h
  exact 𝟭 _

private def transportOriginalOpens {B C : Opens (ComplexModel n)} (h : B = C) :
    Opens B ⥤ Opens C := by
  cases h
  exact 𝟭 _

private def transportOriginalPoint {B C : Opens (ComplexModel n)} (h : B = C) : B → C := by
  cases h
  exact id

private theorem transportOriginalPoint_val {B C : Opens (ComplexModel n)} (h : B = C) (b : B) :
    (transportOriginalPoint h b).val = b.val := by
  cases h
  rfl

private theorem transportOriginalPoint_symm {B C : Opens (ComplexModel n)} (h : B = C) (b : B) :
    transportOriginalPoint h.symm (transportOriginalPoint h b) = b := by
  cases h
  rfl

private theorem transportOriginalOpens_mem {B C : Opens (ComplexModel n)} (h : B = C)
    (A : Opens B) (c : C) :
    c ∈ (transportOriginalOpens h).obj A ↔ transportOriginalPoint h.symm c ∈ A := by
  cases h
  rfl

private def transportOriginalScalarEquiv {B C : Opens (ComplexModel n)} (h : B = C)
    (A : Opens C) :
    ↑((forgetRing (originalOpenStructureSheaf C)).obj.obj (op A)) ≃+*
      ↑((forgetRing (originalOpenStructureSheaf B)).obj.obj
        (op ((transportOriginalOpens h.symm).obj A))) := by
  cases h
  exact RingEquiv.refl _

private def transportOriginalSectionIso {B C : Opens (ComplexModel n)} (h : B = C)
    (M : SheafOfModules.{0} (forgetRing (originalOpenStructureSheaf B))) (A : Opens C) :
    ((transportOriginalModules h).obj M).val.obj (op A) ≅
      (ModuleCat.restrictScalars (transportOriginalScalarEquiv h A).toRingHom).obj
        (M.val.obj (op ((transportOriginalOpens h.symm).obj A))) := by
  cases h
  exact Iso.refl _

/-- The actual smaller open inside the FIRST original image carrier. -/
def originalNestedOpen (U : Opens (ComplexModel n)) (D₁ D₂ : Opens U) :
    Opens (originalImageOpen U D₂) := inverseImageOpen U D₂ D₁

private theorem originalNestedOpen_image (U : Opens (ComplexModel n)) (D₁ D₂ : Opens U)
    (h₁₂ : D₁ ≤ D₂) :
    (imageFunctor U D₂).obj (originalNestedOpen U D₁ D₂) = D₁ := by
  apply le_antisymm (image_inverseImage_le U D₂ D₁)
  intro u hu
  let b := originalImageCarrierIso U D₂ ⟨u, h₁₂ hu⟩
  have hb : originalImageInclusion U D₂ b = u := by apply Subtype.ext; rfl
  exact ⟨b, (show originalImageInclusion U D₂ b ∈ D₁ from hb.symm ▸ hu), hb⟩

/-- The two final coordinate image opens are equal, from ordinary nested-open inclusion alone. -/
theorem originalNestedImageEq (U : Opens (ComplexModel n)) (D₁ D₂ : Opens U)
    (h₁₂ : D₁ ≤ D₂) :
    originalImageOpen (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂) =
      originalImageOpen U D₁ :=
  (image_image U D₂ (originalNestedOpen U D₁ D₂)).symm.trans
    (congrArg (actualOpenImage U) (originalNestedOpen_image U D₁ D₂ h₁₂))

private theorem originalNestedSectionOpenEq (U : Opens (ComplexModel n)) (D₁ D₂ : Opens U)
    (h₁₂ : D₁ ≤ D₂) (A : Opens (originalImageOpen U D₁)) :
    (imageFunctor U D₂).obj
      ((imageFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)).obj
        ((transportOriginalOpens (originalNestedImageEq U D₁ D₂ h₁₂).symm).obj A)) =
      (imageFunctor U D₁).obj A := by
  let H := originalNestedImageEq U D₁ D₂ h₁₂
  ext u
  constructor
  · rintro ⟨b₂, ⟨b₁₂, hb₁₂, hb₂⟩, hu⟩
    refine ⟨transportOriginalPoint H b₁₂, ?_, ?_⟩
    · exact (transportOriginalOpens_mem H.symm A b₁₂).mp hb₁₂
    · apply Subtype.ext
      exact (transportOriginalPoint_val H b₁₂).trans
        ((congrArg (fun b : originalImageOpen U D₂ => b.val) hb₂).trans
          (congrArg (fun b : U => b.val) hu))
  · rintro ⟨b₁, hb₁, hu⟩
    let b₁₂ := transportOriginalPoint H.symm b₁
    refine ⟨originalImageInclusion (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂) b₁₂,
      ⟨b₁₂, ?_, rfl⟩, ?_⟩
    · exact (transportOriginalOpens_mem H.symm A b₁₂).mpr
        ((transportOriginalPoint_symm H.symm b₁).symm ▸ hb₁)
    · apply Subtype.ext
      exact (transportOriginalPoint_val H.symm b₁).trans
        (congrArg (fun b : U => b.val) hu)

private theorem transportOriginalScalarOpenEq {B C : Opens (ComplexModel n)} (h : B = C)
    (A : Opens C) :
    actualOpenImage B ((transportOriginalOpens h.symm).obj A) = actualOpenImage C A := by
  cases h
  rfl

private theorem transportOriginalScalarEquiv_apply {B C : Opens (ComplexModel n)} (h : B = C)
    (A : Opens C) (r : (originalOpenStructureSheaf C).presheaf.obj (op A)) :
    transportOriginalScalarEquiv h A r =
      (actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf.map
        (eqToHom (transportOriginalScalarOpenEq h A)).op r := by
  cases h
  exact (ConcreteCategory.congr_hom
    ((actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf.map_id _) r).symm

private theorem originalNestedScalarEq (U : Opens (ComplexModel n)) (D₁ D₂ : Opens U)
    (h₁₂ : D₁ ≤ D₂) (A : Opens (originalImageOpen U D₁))
    (a : (originalOpenStructureSheaf (originalImageOpen U D₁)).presheaf.obj (op A)) :
    (originalOpenStructureSheaf U).presheaf.map
      (eqToHom (originalNestedSectionOpenEq U D₁ D₂ h₁₂ A).symm).op
      ((originalImageScalarEquiv U D₂
        ((imageFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)).obj
          ((transportOriginalOpens (originalNestedImageEq U D₁ D₂ h₁₂).symm).obj A))).symm
        ((originalImageScalarEquiv (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)
          ((transportOriginalOpens (originalNestedImageEq U D₁ D₂ h₁₂).symm).obj A)).symm
            (transportOriginalScalarEquiv (originalNestedImageEq U D₁ D₂ h₁₂) A a))) =
      (originalImageScalarEquiv U D₁ A).symm a := by
  let H := originalNestedImageEq U D₁ D₂ h₁₂
  let A₀ := (transportOriginalOpens H.symm).obj A
  let F₁₂ := imageFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)
  let OM := (actualComplexStructureSheaf (n := n) (ComplexModel n)).presheaf
  let fH := (eqToHom (transportOriginalScalarOpenEq H A)).op
  let f₁₂ := (eqToHom (image_image (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂) A₀)).op
  let f₂ := (eqToHom (image_image U D₂ (F₁₂.obj A₀))).op
  let f₀ := ((TopologicalSpace.Opens.isOpenEmbedding (X := TopCat.of (ComplexModel n)) U).functor.map
    (eqToHom (originalNestedSectionOpenEq U D₁ D₂ h₁₂ A).symm)).op
  let f₁ := (eqToHom (image_image U D₁ A)).op
  have hm : OM.map fH ≫ OM.map f₁₂ ≫ OM.map f₂ ≫ OM.map f₀ = OM.map f₁ := by
    congr 1
  change OM.map f₀ (OM.map f₂ (OM.map f₁₂ (transportOriginalScalarEquiv H A a))) = OM.map f₁ a
  exact (congrArg (fun r => OM.map f₀ (OM.map f₂ (OM.map f₁₂ r)))
    (transportOriginalScalarEquiv_apply H A a)).trans (ConcreteCategory.congr_hom hm a)

private theorem transportOriginalSectionIso_restrict {B C : Opens (ComplexModel n)} (h : B = C)
    (M : SheafOfModules.{0} (forgetRing (originalOpenStructureSheaf B)))
    {A T : (Opens C)ᵒᵖ} (f : A ⟶ T)
    (s : ((transportOriginalModules h).obj M).val.obj A) :
    (transportOriginalSectionIso h M T.unop).hom (((transportOriginalModules h).obj M).val.map f s) =
      M.val.map ((transportOriginalOpens h.symm).op.map f)
        ((transportOriginalSectionIso h M A.unop).hom s) := by
  cases h
  rfl

private theorem transportOriginalSectionIso_map {B C : Opens (ComplexModel n)} (h : B = C)
    {M N : SheafOfModules.{0} (forgetRing (originalOpenStructureSheaf B))} (f : M ⟶ N)
    (A : Opens C) (s : ((transportOriginalModules h).obj M).val.obj (op A)) :
    (transportOriginalSectionIso h N A).hom (((transportOriginalModules h).map f).val.app (op A) s) =
      f.val.app (op ((transportOriginalOpens h.symm).obj A))
        ((transportOriginalSectionIso h M A).hom s) := by
  cases h
  rfl

private def nestedRestrictionLinearMap (U : Opens (ComplexModel n)) (D₁ D₂ : Opens U)
    (h₁₂ : D₁ ≤ D₂) (M : SheafOfModules.{0} (forgetRing (originalOpenStructureSheaf U)))
    (A : Opens (originalImageOpen U D₁)) :
    ((transportOriginalModules (originalNestedImageEq U D₁ D₂ h₁₂)).obj
      ((originalImageRestrictionFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)).obj
        ((originalImageRestrictionFunctor U D₂).obj M))).val.obj (op A) →ₗ[
      (forgetRing (originalOpenStructureSheaf (originalImageOpen U D₁))).obj.obj (op A)]
      ((originalImageRestrictionFunctor U D₁).obj M).val.obj (op A) where
  toFun s := M.val.map (eqToHom (originalNestedSectionOpenEq U D₁ D₂ h₁₂ A).symm).op
    ((transportOriginalSectionIso (originalNestedImageEq U D₁ D₂ h₁₂)
      ((originalImageRestrictionFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)).obj
        ((originalImageRestrictionFunctor U D₂).obj M)) A).hom s)
  map_add' x y := (congrArg
    (M.val.map (eqToHom (originalNestedSectionOpenEq U D₁ D₂ h₁₂ A).symm).op)
    (map_add _ x y)).trans (map_add _ _ _)
  map_smul' r s := by
    let H := originalNestedImageEq U D₁ D₂ h₁₂
    let A₀ := (transportOriginalOpens H.symm).obj A
    let V := originalNestedOpen U D₁ D₂
    let F₁₂ := imageFunctor (originalImageOpen U D₂) V
    let N := (originalImageRestrictionFunctor (originalImageOpen U D₂) V).obj
      ((originalImageRestrictionFunctor U D₂).obj M)
    let e := transportOriginalSectionIso H N A
    let f := (eqToHom (originalNestedSectionOpenEq U D₁ D₂ h₁₂ A).symm).op
    let m₀ : M.val.obj (op ((imageFunctor U D₂).obj (F₁₂.obj A₀))) := e.hom s
    let a₀ : (forgetRing (originalOpenStructureSheaf U)).obj.obj
        (op ((imageFunctor U D₂).obj (F₁₂.obj A₀))) :=
      (originalImageScalarEquiv U D₂ (F₁₂.obj A₀)).symm
        ((originalImageScalarEquiv (originalImageOpen U D₂) V A₀).symm
          (transportOriginalScalarEquiv H A r))
    have he := e.hom.hom.map_smul r s
    apply (congrArg (fun t : N.val.obj (op A₀) => M.val.map f t) he).trans
    change M.val.map f (a₀ • m₀) =
      (show (forgetRing (originalOpenStructureSheaf U)).obj.obj (op ((imageFunctor U D₁).obj A)) from
        (originalImageScalarEquiv U D₁ A).symm r) •
        (show M.val.obj (op ((imageFunctor U D₁).obj A)) from M.val.map f m₀)
    exact (M.val.map_smul f a₀ m₀).trans
      (congrArg (fun a : (forgetRing (originalOpenStructureSheaf U)).obj.obj
          (op ((imageFunctor U D₁).obj A)) =>
        a • (show M.val.obj (op ((imageFunctor U D₁).obj A)) from M.val.map f m₀))
          (originalNestedScalarEq U D₁ D₂ h₁₂ A r))

private def nestedRestrictionComponentIso (U : Opens (ComplexModel n)) (D₁ D₂ : Opens U)
    (h₁₂ : D₁ ≤ D₂) (M : SheafOfModules.{0} (forgetRing (originalOpenStructureSheaf U)))
    (A : Opens (originalImageOpen U D₁)) :
    ((transportOriginalModules (originalNestedImageEq U D₁ D₂ h₁₂)).obj
      ((originalImageRestrictionFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)).obj
        ((originalImageRestrictionFunctor U D₂).obj M))).val.obj (op A) ≅
      ((originalImageRestrictionFunctor U D₁).obj M).val.obj (op A) := by
  apply LinearEquiv.toModuleIso
  apply LinearEquiv.ofBijective (nestedRestrictionLinearMap U D₁ D₂ h₁₂ M A)
  let q := M.val.presheaf.mapIso (eqToIso (originalNestedSectionOpenEq U D₁ D₂ h₁₂ A).symm).op
  let e := transportOriginalSectionIso (originalNestedImageEq U D₁ D₂ h₁₂)
      ((originalImageRestrictionFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)).obj
        ((originalImageRestrictionFunctor U D₂).obj M)) A
  change Function.Bijective (fun s => q.hom (e.hom s))
  exact q.addCommGroupIsoToAddEquiv.bijective.comp e.toLinearEquiv.bijective

private def nestedRestrictionObjectIso (U : Opens (ComplexModel n)) (D₁ D₂ : Opens U)
    (h₁₂ : D₁ ≤ D₂) (M : SheafOfModules.{0} (forgetRing (originalOpenStructureSheaf U))) :
    (transportOriginalModules (originalNestedImageEq U D₁ D₂ h₁₂)).obj
      ((originalImageRestrictionFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)).obj
        ((originalImageRestrictionFunctor U D₂).obj M)) ≅
      (originalImageRestrictionFunctor U D₁).obj M := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun A => nestedRestrictionComponentIso U D₁ D₂ h₁₂ M A.unop) ?_
  intro A T f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  let H := originalNestedImageEq U D₁ D₂ h₁₂
  let N := (originalImageRestrictionFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)).obj
    ((originalImageRestrictionFunctor U D₂).obj M)
  let eA := transportOriginalSectionIso H N A.unop
  let nA := (eqToHom (originalNestedSectionOpenEq U D₁ D₂ h₁₂ A.unop).symm).op
  let nT := (eqToHom (originalNestedSectionOpenEq U D₁ D₂ h₁₂ T.unop).symm).op
  let fc := (imageFunctor U D₂).op.map
    ((imageFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)).op.map
      ((transportOriginalOpens H.symm).op.map f))
  let fd := (imageFunctor U D₁).op.map f
  have he := transportOriginalSectionIso_restrict H N f s
  apply (congrArg (fun t : N.val.obj (op ((transportOriginalOpens H.symm).obj T.unop)) =>
    M.val.map nT t) he).trans
  change M.val.presheaf.map nT (M.val.presheaf.map fc (eA.hom s)) =
    M.val.presheaf.map fd (M.val.presheaf.map nA (eA.hom s))
  have hm : M.val.presheaf.map fc ≫ M.val.presheaf.map nT =
      M.val.presheaf.map nA ≫ M.val.presheaf.map fd := by
    rw [← M.val.presheaf.map_comp, ← M.val.presheaf.map_comp]
    congr 1
  exact ConcreteCategory.congr_hom hm (eA.hom s)

/-- Genuine native nested restriction for EVERY original module, derived independently of Theta. -/
def originalNestedRestrictionIso (U : Opens (ComplexModel n)) (D₁ D₂ : Opens U)
    (h₁₂ : D₁ ≤ D₂) :
    (originalImageRestrictionFunctor U D₂ ⋙
      originalImageRestrictionFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)) ⋙
        transportOriginalModules (originalNestedImageEq U D₁ D₂ h₁₂) ≅
      originalImageRestrictionFunctor U D₁ := by
  refine NatIso.ofComponents (fun M => nestedRestrictionObjectIso U D₁ D₂ h₁₂ M) ?_
  intro M N f
  ext A s
  let H := originalNestedImageEq U D₁ D₂ h₁₂
  let Q := originalImageRestrictionFunctor U D₂ ⋙
    originalImageRestrictionFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)
  let a₀ := (transportOriginalOpens H.symm).obj A.unop
  let m₀ := (transportOriginalSectionIso H (Q.obj M) A.unop).hom s
  let q := (eqToHom (originalNestedSectionOpenEq U D₁ D₂ h₁₂ A.unop).symm).op
  have he := transportOriginalSectionIso_map H (Q.map f) A.unop s
  apply (congrArg (fun t : (Q.obj N).val.obj (op a₀) => N.val.map q t) he).trans
  exact (PresheafOfModules.naturality_apply f.val q m₀).symm

private def supportSectionValue (U : Opens (ComplexModel n)) (W : Set U) (O : Opens U)
    (y : W) (hy : y.val ∈ O) (s : (originalPrimeSupportModule U W).val.obj (op O)) : ℂ :=
  actualSubspaceStalkEval (n := n) W y
    ((actualSubspaceSheaf (n := n) W).presheaf.germ
      ((Opens.map (actualSubspaceTopInclusion W)).obj O) y hy s)

private theorem supportSectionValue_restrict (U : Opens (ComplexModel n)) (W : Set U)
    {O T : Opens U} (f : T ⟶ O) (y : W) (hy : y.val ∈ T)
    (s : (originalPrimeSupportModule U W).val.obj (op O)) :
    supportSectionValue U W T y hy ((originalPrimeSupportModule U W).val.map f.op s) =
      supportSectionValue U W O y ((leOfHom f) hy) s :=
  congrArg (actualSubspaceStalkEval (n := n) W y)
    ((actualSubspaceSheaf (n := n) W).presheaf.germ_res_apply
      ((Opens.map (actualSubspaceTopInclusion W)).map f) y hy s)

private theorem supportSectionValue_point (U : Opens (ComplexModel n)) (W : Set U)
    (O : Opens U) (y z : W) (h : y = z) (hy : y.val ∈ O) (hz : z.val ∈ O)
    (s : (originalPrimeSupportModule U W).val.obj (op O)) :
    supportSectionValue U W O y hy s = supportSectionValue U W O z hz s := by
  cases h
  rfl

private theorem supportHom_ext_value (U : Opens (ComplexModel n)) (W : Set U)
    (N : SheafOfModules.{0} (forgetRing (originalOpenStructureSheaf U)))
    (f g : N ⟶ originalPrimeSupportModule U W)
    (h : ∀ (A : Opens U) (y : W) (hy : y.val ∈ A) (s : N.val.obj (op A)),
      supportSectionValue U W A y hy (f.val.app (op A) s) =
        supportSectionValue U W A y hy (g.val.app (op A) s)) : f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro A
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply actualSubspaceSection_ext_eval (n := n) W
    ((Opens.map (actualSubspaceTopInclusion W)).obj A.unop)
  intro y hy
  exact h A.unop y hy s

private theorem thetaSectionValue (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U)
    (A : Opens (originalImageOpen U D)) (y : imageSupport U D W) (hy : y.val ∈ A)
    (s : (originalPrimeSupportModule U W).val.obj (op ((imageFunctor U D).obj A))) :
    supportSectionValue (originalImageOpen U D) (imageSupport U D W) A y hy
      ((canonicalSupportOpenRestrictionIso U D W).hom.val.app (op A) s) =
    supportSectionValue U W ((imageFunctor U D).obj A)
      ((supportOpenMap U D W).base y) ⟨y.val, hy, rfl⟩ s :=
  supportSectionMap_eval U D W A y hy s

private def transportOriginalSupportIso {B C : Opens (ComplexModel n)} (h : B = C) (W : Set B) :
    (transportOriginalModules h).obj (originalPrimeSupportModule B W) ≅
      originalPrimeSupportModule C ((transportOriginalPoint h.symm) ⁻¹' W) := by
  cases h
  exact Iso.refl _

private theorem transportOriginalMembership {B C : Opens (ComplexModel n)} (h : B = C)
    (A : Opens C) (c : C) (hc : c ∈ A) :
    transportOriginalPoint h.symm c ∈ (transportOriginalOpens h.symm).obj A := by
  cases h
  exact hc

private theorem transportOriginalSupportValue {B C : Opens (ComplexModel n)} (h : B = C)
    (W : Set B) (A : Opens C) (y : (transportOriginalPoint h.symm) ⁻¹' W)
    (hy : y.val ∈ A)
    (s : ((transportOriginalModules h).obj (originalPrimeSupportModule B W)).val.obj (op A)) :
    supportSectionValue C ((transportOriginalPoint h.symm) ⁻¹' W) A y hy
      ((transportOriginalSupportIso h W).hom.val.app (op A) s) =
    supportSectionValue B W ((transportOriginalOpens h.symm).obj A)
      ⟨transportOriginalPoint h.symm y.val, y.property⟩
      (transportOriginalMembership h A y.val hy)
      ((transportOriginalSectionIso h (originalPrimeSupportModule B W) A).hom s) := by
  cases h
  rfl

private theorem equalOriginalSupportValue (U : Opens (ComplexModel n)) {W T : Set U}
    (h : W = T) (O : Opens U) (y : T) (hy : y.val ∈ O)
    (s : (originalPrimeSupportModule U W).val.obj (op O)) :
    supportSectionValue U T O y hy
      ((eqToIso (congrArg (originalPrimeSupportModule U) h)).hom.val.app (op O) s) =
    supportSectionValue U W O ⟨y.val, h.symm ▸ y.property⟩ hy s := by
  cases h
  rfl

private def transportOriginalSupportToIso {B C : Opens (ComplexModel n)} (h : B = C)
    (W : Set B) (T : Set C) (hW : (transportOriginalPoint h.symm) ⁻¹' W = T) :
    (transportOriginalModules h).obj (originalPrimeSupportModule B W) ≅
      originalPrimeSupportModule C T :=
  transportOriginalSupportIso h W ≪≫ eqToIso (congrArg (originalPrimeSupportModule C) hW)

private theorem transportOriginalSupportToIso_value {B C : Opens (ComplexModel n)} (h : B = C)
    (W : Set B) (T : Set C) (hW : (transportOriginalPoint h.symm) ⁻¹' W = T)
    (A : Opens C) (y : T) (hy : y.val ∈ A)
    (s : ((transportOriginalModules h).obj (originalPrimeSupportModule B W)).val.obj (op A)) :
    supportSectionValue C T A y hy ((transportOriginalSupportToIso h W T hW).hom.val.app (op A) s) =
      supportSectionValue B W ((transportOriginalOpens h.symm).obj A)
        ⟨transportOriginalPoint h.symm y.val, (Set.ext_iff.mp hW y.val).mpr y.property⟩
        (transportOriginalMembership h A y.val hy)
        ((transportOriginalSectionIso h (originalPrimeSupportModule B W) A).hom s) := by
  cases h
  change W = T at hW
  cases hW
  rfl

private theorem transportOriginalSupportMap_value {B C : Opens (ComplexModel n)} (h : B = C)
    (W : Set B) (T : Set C) (hW : (transportOriginalPoint h.symm) ⁻¹' W = T)
    (N : SheafOfModules.{0} (forgetRing (originalOpenStructureSheaf B)))
    (f : N ⟶ originalPrimeSupportModule B W)
    (A : Opens C) (y : T) (hy : y.val ∈ A)
    (s : ((transportOriginalModules h).obj N).val.obj (op A)) :
    supportSectionValue C T A y hy
      ((((transportOriginalModules h).map f) ≫ (transportOriginalSupportToIso h W T hW).hom).val.app
        (op A) s) =
      supportSectionValue B W ((transportOriginalOpens h.symm).obj A)
        ⟨transportOriginalPoint h.symm y.val, (Set.ext_iff.mp hW y.val).mpr y.property⟩
        (transportOriginalMembership h A y.val hy)
        (f.val.app (op ((transportOriginalOpens h.symm).obj A))
          ((transportOriginalSectionIso h N A).hom s)) := by
  cases h
  change W = T at hW
  cases hW
  rfl

private theorem originalNestedPointEq (U : Opens (ComplexModel n)) (D₁ D₂ : Opens U)
    (h₁₂ : D₁ ≤ D₂) (b : originalImageOpen U D₁) :
    originalImageInclusion U D₂
      (originalImageInclusion (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)
        (transportOriginalPoint (originalNestedImageEq U D₁ D₂ h₁₂).symm b)) =
      originalImageInclusion U D₁ b := by
  apply Subtype.ext
  exact transportOriginalPoint_val (originalNestedImageEq U D₁ D₂ h₁₂).symm b

private theorem originalNestedSupportEq (U : Opens (ComplexModel n)) (D₁ D₂ : Opens U)
    (h₁₂ : D₁ ≤ D₂) (W : Set U) :
    (transportOriginalPoint (originalNestedImageEq U D₁ D₂ h₁₂).symm) ⁻¹'
      imageSupport (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)
        (imageSupport U D₂ W) = imageSupport U D₁ W := by
  ext b
  exact Iff.of_eq (congrArg (fun u : U => u ∈ W) (originalNestedPointEq U D₁ D₂ h₁₂ b))

/-- The final support factory is the SAME original factory after the derived carrier equality. -/
def originalNestedSupportTransportIso (U : Opens (ComplexModel n)) (D₁ D₂ : Opens U)
    (h₁₂ : D₁ ≤ D₂) (W : Set U) :
    (transportOriginalModules (originalNestedImageEq U D₁ D₂ h₁₂)).obj
      (originalPrimeSupportModule
        (originalImageOpen (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂))
        (imageSupport (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂) (imageSupport U D₂ W))) ≅
      originalPrimeSupportModule (originalImageOpen U D₁) (imageSupport U D₁ W) :=
  transportOriginalSupportToIso (originalNestedImageEq U D₁ D₂ h₁₂) _ _
    (originalNestedSupportEq U D₁ D₂ h₁₂ W)

private def innerThetaMap (U : Opens (ComplexModel n)) (D : Opens U)
    (V : Opens (originalImageOpen U D)) (W : Set U) :
    (originalImageRestrictionFunctor (originalImageOpen U D) V).obj
      ((originalImageRestrictionFunctor U D).obj (originalPrimeSupportModule U W)) ⟶
      originalPrimeSupportModule (originalImageOpen (originalImageOpen U D) V)
        (imageSupport (originalImageOpen U D) V (imageSupport U D W)) :=
  (originalImageRestrictionFunctor (originalImageOpen U D) V).map
    (canonicalSupportOpenRestrictionIso U D W).hom ≫
      (canonicalSupportOpenRestrictionIso (originalImageOpen U D) V (imageSupport U D W)).hom

private theorem innerThetaMap_value (U : Opens (ComplexModel n)) (D : Opens U)
    (V : Opens (originalImageOpen U D)) (W : Set U)
    (A : Opens (originalImageOpen (originalImageOpen U D) V))
    (y : imageSupport (originalImageOpen U D) V (imageSupport U D W)) (hy : y.val ∈ A)
    (s : (originalPrimeSupportModule U W).val.obj
      (op ((imageFunctor U D).obj ((imageFunctor (originalImageOpen U D) V).obj A)))) :
    supportSectionValue (originalImageOpen (originalImageOpen U D) V)
      (imageSupport (originalImageOpen U D) V (imageSupport U D W)) A y hy
      ((innerThetaMap U D V W).val.app (op A) s) =
      supportSectionValue U W ((imageFunctor U D).obj ((imageFunctor (originalImageOpen U D) V).obj A))
        ((supportOpenMap U D W).base
          ((supportOpenMap (originalImageOpen U D) V (imageSupport U D W)).base y))
        ⟨(supportOpenMap (originalImageOpen U D) V (imageSupport U D W)).base y |>.val,
          ⟨y.val, hy, rfl⟩, rfl⟩ s :=
  (thetaSectionValue (originalImageOpen U D) V (imageSupport U D W) A y hy
    ((canonicalSupportOpenRestrictionIso U D W).hom.val.app
      (op ((imageFunctor (originalImageOpen U D) V).obj A)) s)).trans
        (thetaSectionValue U D W ((imageFunctor (originalImageOpen U D) V).obj A)
          ((supportOpenMap (originalImageOpen U D) V (imageSupport U D W)).base y) ⟨y.val, hy, rfl⟩ s)

private def nestedThetaMap (U : Opens (ComplexModel n)) (D₁ D₂ : Opens U)
    (h₁₂ : D₁ ≤ D₂) (W : Set U) :
    (transportOriginalModules (originalNestedImageEq U D₁ D₂ h₁₂)).obj
      ((originalImageRestrictionFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)).obj
        ((originalImageRestrictionFunctor U D₂).obj (originalPrimeSupportModule U W))) ⟶
      originalPrimeSupportModule (originalImageOpen U D₁) (imageSupport U D₁ W) :=
  (transportOriginalModules (originalNestedImageEq U D₁ D₂ h₁₂)).map
    (innerThetaMap U D₂ (originalNestedOpen U D₁ D₂) W) ≫
      (originalNestedSupportTransportIso U D₁ D₂ h₁₂ W).hom

private def directThetaMap (U : Opens (ComplexModel n)) (D₁ D₂ : Opens U)
    (h₁₂ : D₁ ≤ D₂) (W : Set U) :
    (transportOriginalModules (originalNestedImageEq U D₁ D₂ h₁₂)).obj
      ((originalImageRestrictionFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)).obj
        ((originalImageRestrictionFunctor U D₂).obj (originalPrimeSupportModule U W))) ⟶
      originalPrimeSupportModule (originalImageOpen U D₁) (imageSupport U D₁ W) :=
  ((originalNestedRestrictionIso U D₁ D₂ h₁₂).app (originalPrimeSupportModule U W)).hom ≫
    (canonicalSupportOpenRestrictionIso U D₁ W).hom

private def nestedSectionReadback (U : Opens (ComplexModel n)) (D₁ D₂ : Opens U)
    (h₁₂ : D₁ ≤ D₂) (W : Set U) (A : Opens (originalImageOpen U D₁))
    (s : ((transportOriginalModules (originalNestedImageEq U D₁ D₂ h₁₂)).obj
      ((originalImageRestrictionFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)).obj
        ((originalImageRestrictionFunctor U D₂).obj (originalPrimeSupportModule U W)))).val.obj (op A)) :
    (originalPrimeSupportModule U W).val.obj (op (((imageFunctor U D₂).obj ((imageFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)).obj ((transportOriginalOpens (originalNestedImageEq U D₁ D₂ h₁₂).symm).obj A))))) :=
  (transportOriginalSectionIso (originalNestedImageEq U D₁ D₂ h₁₂)
    ((originalImageRestrictionFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)).obj
      ((originalImageRestrictionFunctor U D₂).obj (originalPrimeSupportModule U W))) A).hom s

private def nestedSupportOldPoint (U : Opens (ComplexModel n)) (D₁ D₂ : Opens U)
    (h₁₂ : D₁ ≤ D₂) (W : Set U) (y : imageSupport U D₁ W) : W :=
  (supportOpenMap U D₂ W).base
    ((supportOpenMap (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)
      (imageSupport U D₂ W)).base ((⟨transportOriginalPoint (originalNestedImageEq U D₁ D₂ h₁₂).symm y.val, (Set.ext_iff.mp (originalNestedSupportEq U D₁ D₂ h₁₂ W) y.val).mpr y.property⟩ : imageSupport (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂) (imageSupport U D₂ W))))

private theorem nestedSupportOldPoint_eq (U : Opens (ComplexModel n)) (D₁ D₂ : Opens U)
    (h₁₂ : D₁ ≤ D₂) (W : Set U) (y : imageSupport U D₁ W) :
    nestedSupportOldPoint U D₁ D₂ h₁₂ W y = (supportOpenMap U D₁ W).base y := by
  apply Subtype.ext
  exact originalNestedPointEq U D₁ D₂ h₁₂ y.val

private theorem nestedSupportOldPoint_mem (U : Opens (ComplexModel n)) (D₁ D₂ : Opens U)
    (h₁₂ : D₁ ≤ D₂) (W : Set U) (A : Opens (originalImageOpen U D₁))
    (y : imageSupport U D₁ W) (hy : y.val ∈ A) :
    (nestedSupportOldPoint U D₁ D₂ h₁₂ W y).val ∈ ((imageFunctor U D₂).obj ((imageFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)).obj ((transportOriginalOpens (originalNestedImageEq U D₁ D₂ h₁₂).symm).obj A))) :=
  ⟨(supportOpenMap (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)
      (imageSupport U D₂ W)).base ((⟨transportOriginalPoint (originalNestedImageEq U D₁ D₂ h₁₂).symm y.val, (Set.ext_iff.mp (originalNestedSupportEq U D₁ D₂ h₁₂ W) y.val).mpr y.property⟩ : imageSupport (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂) (imageSupport U D₂ W))) |>.val,
    ⟨((⟨transportOriginalPoint (originalNestedImageEq U D₁ D₂ h₁₂).symm y.val, (Set.ext_iff.mp (originalNestedSupportEq U D₁ D₂ h₁₂ W) y.val).mpr y.property⟩ : imageSupport (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂) (imageSupport U D₂ W))).val,
      transportOriginalMembership (originalNestedImageEq U D₁ D₂ h₁₂) A y.val hy, rfl⟩, rfl⟩

private theorem nestedThetaMap_eq (U : Opens (ComplexModel n)) (D₁ D₂ : Opens U)
    (h₁₂ : D₁ ≤ D₂) (W : Set U) :
    nestedThetaMap U D₁ D₂ h₁₂ W =
      (transportOriginalModules (originalNestedImageEq U D₁ D₂ h₁₂)).map
        (innerThetaMap U D₂ (originalNestedOpen U D₁ D₂) W) ≫
          (originalNestedSupportTransportIso U D₁ D₂ h₁₂ W).hom := rfl

private theorem nestedSupportTransportIso_eq (U : Opens (ComplexModel n)) (D₁ D₂ : Opens U)
    (h₁₂ : D₁ ≤ D₂) (W : Set U) :
    originalNestedSupportTransportIso U D₁ D₂ h₁₂ W =
      transportOriginalSupportToIso (originalNestedImageEq U D₁ D₂ h₁₂)
        (imageSupport (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂) (imageSupport U D₂ W))
        (imageSupport U D₁ W) (originalNestedSupportEq U D₁ D₂ h₁₂ W) := rfl

private theorem nestedSectionReadback_eq (U : Opens (ComplexModel n)) (D₁ D₂ : Opens U)
    (h₁₂ : D₁ ≤ D₂) (W : Set U) (A : Opens (originalImageOpen U D₁))
    (s : ((transportOriginalModules (originalNestedImageEq U D₁ D₂ h₁₂)).obj
      ((originalImageRestrictionFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)).obj
        ((originalImageRestrictionFunctor U D₂).obj (originalPrimeSupportModule U W)))).val.obj (op A)) :
    nestedSectionReadback U D₁ D₂ h₁₂ W A s =
      (transportOriginalSectionIso (originalNestedImageEq U D₁ D₂ h₁₂)
        ((originalImageRestrictionFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)).obj
          ((originalImageRestrictionFunctor U D₂).obj (originalPrimeSupportModule U W))) A).hom s := rfl

private theorem nestedThetaMap_transport_value
    (U : Opens (ComplexModel n)) (D₁ D₂ : Opens U) (h₁₂ : D₁ ≤ D₂) (W : Set U)
    (A : Opens (originalImageOpen U D₁)) (y : imageSupport U D₁ W) (hy : y.val ∈ A)
    (s : ((transportOriginalModules (originalNestedImageEq U D₁ D₂ h₁₂)).obj
      ((originalImageRestrictionFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)).obj
        ((originalImageRestrictionFunctor U D₂).obj (originalPrimeSupportModule U W)))).val.obj (op A)) :
    supportSectionValue (originalImageOpen U D₁) (imageSupport U D₁ W) A y hy
      ((nestedThetaMap U D₁ D₂ h₁₂ W).val.app (op A) s) =
      supportSectionValue (originalImageOpen (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂))
        (imageSupport (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂) (imageSupport U D₂ W))
        (((transportOriginalOpens (originalNestedImageEq U D₁ D₂ h₁₂).symm).obj A)) ((⟨transportOriginalPoint (originalNestedImageEq U D₁ D₂ h₁₂).symm y.val, (Set.ext_iff.mp (originalNestedSupportEq U D₁ D₂ h₁₂ W) y.val).mpr y.property⟩ : imageSupport (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂) (imageSupport U D₂ W)))
        (transportOriginalMembership (originalNestedImageEq U D₁ D₂ h₁₂) A y.val hy)
        ((innerThetaMap U D₂ (originalNestedOpen U D₁ D₂) W).val.app
          (op (((transportOriginalOpens (originalNestedImageEq U D₁ D₂ h₁₂).symm).obj A))) (nestedSectionReadback U D₁ D₂ h₁₂ W A s)) := by
  have h := transportOriginalSupportMap_value
    (B := originalImageOpen (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂))
    (C := originalImageOpen U D₁)
    (originalNestedImageEq U D₁ D₂ h₁₂)
    (imageSupport (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂) (imageSupport U D₂ W))
    (imageSupport U D₁ W) (originalNestedSupportEq U D₁ D₂ h₁₂ W)
    ((originalImageRestrictionFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)).obj
      ((originalImageRestrictionFunctor U D₂).obj (originalPrimeSupportModule U W)))
    (innerThetaMap U D₂ (originalNestedOpen U D₁ D₂) W) A y hy s
  have hm := (nestedThetaMap_eq U D₁ D₂ h₁₂ W).trans
    (congrArg (fun e :
      (transportOriginalModules (originalNestedImageEq U D₁ D₂ h₁₂)).obj
        (originalPrimeSupportModule
          (originalImageOpen (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂))
          (imageSupport (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂) (imageSupport U D₂ W))) ≅
        originalPrimeSupportModule (originalImageOpen U D₁) (imageSupport U D₁ W) =>
      (transportOriginalModules (originalNestedImageEq U D₁ D₂ h₁₂)).map
        (innerThetaMap U D₂ (originalNestedOpen U D₁ D₂) W) ≫ e.hom)
      (nestedSupportTransportIso_eq U D₁ D₂ h₁₂ W))
  have hl := congrArg (fun f :
    (transportOriginalModules (originalNestedImageEq U D₁ D₂ h₁₂)).obj
      ((originalImageRestrictionFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)).obj
        ((originalImageRestrictionFunctor U D₂).obj (originalPrimeSupportModule U W))) ⟶
      originalPrimeSupportModule (originalImageOpen U D₁) (imageSupport U D₁ W) =>
    supportSectionValue (originalImageOpen U D₁) (imageSupport U D₁ W) A y hy
      (f.val.app (op A) s)) hm
  have hr := congrArg (fun t :
    (originalPrimeSupportModule U W).val.obj
      (op ((imageFunctor U D₂).obj ((imageFunctor (originalImageOpen U D₂)
        (originalNestedOpen U D₁ D₂)).obj
          ((transportOriginalOpens (originalNestedImageEq U D₁ D₂ h₁₂).symm).obj A)))) =>
    supportSectionValue (originalImageOpen (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂))
      (imageSupport (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂) (imageSupport U D₂ W))
      ((transportOriginalOpens (originalNestedImageEq U D₁ D₂ h₁₂).symm).obj A)
      (⟨transportOriginalPoint (originalNestedImageEq U D₁ D₂ h₁₂).symm y.val,
        (Set.ext_iff.mp (originalNestedSupportEq U D₁ D₂ h₁₂ W) y.val).mpr y.property⟩ :
        imageSupport (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂) (imageSupport U D₂ W))
      (transportOriginalMembership (originalNestedImageEq U D₁ D₂ h₁₂) A y.val hy)
      ((innerThetaMap U D₂ (originalNestedOpen U D₁ D₂) W).val.app
        (op ((transportOriginalOpens (originalNestedImageEq U D₁ D₂ h₁₂).symm).obj A)) t))
    (nestedSectionReadback_eq U D₁ D₂ h₁₂ W A s).symm
  exact hl.trans (h.trans hr)


private theorem originalNestedRestrictionIso_hom_app
    (U : Opens (ComplexModel n)) (D₁ D₂ : Opens U) (h₁₂ : D₁ ≤ D₂)
    (M : SheafOfModules.{0} (forgetRing (originalOpenStructureSheaf U)))
    (A : Opens (originalImageOpen U D₁))
    (s : ((transportOriginalModules (originalNestedImageEq U D₁ D₂ h₁₂)).obj
      ((originalImageRestrictionFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)).obj
        ((originalImageRestrictionFunctor U D₂).obj M))).val.obj (op A)) :
    ((originalNestedRestrictionIso U D₁ D₂ h₁₂).app M).hom.val.app (op A) s =
      M.val.map (eqToHom (originalNestedSectionOpenEq U D₁ D₂ h₁₂ A).symm).op
        ((transportOriginalSectionIso (originalNestedImageEq U D₁ D₂ h₁₂)
          ((originalImageRestrictionFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)).obj
            ((originalImageRestrictionFunctor U D₂).obj M)) A).hom s) := rfl

private theorem directThetaMap_value
    (U : Opens (ComplexModel n)) (D₁ D₂ : Opens U) (h₁₂ : D₁ ≤ D₂) (W : Set U)
    (A : Opens (originalImageOpen U D₁)) (y : imageSupport U D₁ W) (hy : y.val ∈ A)
    (s : ((transportOriginalModules (originalNestedImageEq U D₁ D₂ h₁₂)).obj
      ((originalImageRestrictionFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)).obj
        ((originalImageRestrictionFunctor U D₂).obj (originalPrimeSupportModule U W)))).val.obj (op A)) :
    supportSectionValue (originalImageOpen U D₁) (imageSupport U D₁ W) A y hy
      ((directThetaMap U D₁ D₂ h₁₂ W).val.app (op A) s) =
      supportSectionValue U W
        ((imageFunctor U D₂).obj ((imageFunctor (originalImageOpen U D₂)
          (originalNestedOpen U D₁ D₂)).obj
            ((transportOriginalOpens (originalNestedImageEq U D₁ D₂ h₁₂).symm).obj A)))
        ((supportOpenMap U D₁ W).base y)
        ((leOfHom (eqToHom (originalNestedSectionOpenEq U D₁ D₂ h₁₂ A).symm))
          ⟨y.val, hy, rfl⟩)
        (nestedSectionReadback U D₁ D₂ h₁₂ W A s) := by
  have hc := congrArg (fun t : (originalPrimeSupportModule U W).val.obj
      (op ((imageFunctor U D₁).obj A)) =>
    supportSectionValue (originalImageOpen U D₁) (imageSupport U D₁ W) A y hy
      ((canonicalSupportOpenRestrictionIso U D₁ W).hom.val.app (op A) t))
    (originalNestedRestrictionIso_hom_app U D₁ D₂ h₁₂ (originalPrimeSupportModule U W) A s)
  have ht := thetaSectionValue U D₁ W A y hy
    ((originalPrimeSupportModule U W).val.map
      (eqToHom (originalNestedSectionOpenEq U D₁ D₂ h₁₂ A).symm).op
        (nestedSectionReadback U D₁ D₂ h₁₂ W A s))
  have hr := supportSectionValue_restrict U W
    (eqToHom (originalNestedSectionOpenEq U D₁ D₂ h₁₂ A).symm)
    ((supportOpenMap U D₁ W).base y) ⟨y.val, hy, rfl⟩
    (nestedSectionReadback U D₁ D₂ h₁₂ W A s)
  exact hc.trans (ht.trans hr)

private theorem nestedThetaMap_eq_direct
    (U : Opens (ComplexModel n)) (D₁ D₂ : Opens U) (h₁₂ : D₁ ≤ D₂) (W : Set U) :
    nestedThetaMap U D₁ D₂ h₁₂ W = directThetaMap U D₁ D₂ h₁₂ W := by
  apply supportHom_ext_value (originalImageOpen U D₁) (imageSupport U D₁ W)
    ((transportOriginalModules (originalNestedImageEq U D₁ D₂ h₁₂)).obj
      ((originalImageRestrictionFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)).obj
        ((originalImageRestrictionFunctor U D₂).obj (originalPrimeSupportModule U W))))
    (nestedThetaMap U D₁ D₂ h₁₂ W) (directThetaMap U D₁ D₂ h₁₂ W)
  intro A y hy s
  have ht := nestedThetaMap_transport_value U D₁ D₂ h₁₂ W A y hy s
  have hi := innerThetaMap_value U D₂ (originalNestedOpen U D₁ D₂) W
    ((transportOriginalOpens (originalNestedImageEq U D₁ D₂ h₁₂).symm).obj A)
    (⟨transportOriginalPoint (originalNestedImageEq U D₁ D₂ h₁₂).symm y.val,
      (Set.ext_iff.mp (originalNestedSupportEq U D₁ D₂ h₁₂ W) y.val).mpr y.property⟩ :
      imageSupport (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂) (imageSupport U D₂ W))
    (transportOriginalMembership (originalNestedImageEq U D₁ D₂ h₁₂) A y.val hy)
    (nestedSectionReadback U D₁ D₂ h₁₂ W A s)
  have hp := supportSectionValue_point U W
    ((imageFunctor U D₂).obj ((imageFunctor (originalImageOpen U D₂)
      (originalNestedOpen U D₁ D₂)).obj
        ((transportOriginalOpens (originalNestedImageEq U D₁ D₂ h₁₂).symm).obj A)))
    (nestedSupportOldPoint U D₁ D₂ h₁₂ W y) ((supportOpenMap U D₁ W).base y)
    (nestedSupportOldPoint_eq U D₁ D₂ h₁₂ W y)
    (nestedSupportOldPoint_mem U D₁ D₂ h₁₂ W A y hy)
    ((leOfHom (eqToHom (originalNestedSectionOpenEq U D₁ D₂ h₁₂ A).symm))
      ⟨y.val, hy, rfl⟩)
    (nestedSectionReadback U D₁ D₂ h₁₂ W A s)
  exact ht.trans (hi.trans (hp.trans (directThetaMap_value U D₁ D₂ h₁₂ W A y hy s).symm))


/-- FULL native Theta composition on nested ORIGINAL opens, with derived carrier transport. -/
theorem canonicalSupportOpenRestrictionIso_naturality
    (U : Opens (ComplexModel n)) (D₁ D₂ : Opens U) (h₁₂ : D₁ ≤ D₂) (W : Set U) :
    (show (transportOriginalModules (originalNestedImageEq U D₁ D₂ h₁₂)).obj
      ((originalImageRestrictionFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)).obj
        ((originalImageRestrictionFunctor U D₂).obj (originalPrimeSupportModule U W))) ⟶
      originalPrimeSupportModule (originalImageOpen U D₁) (imageSupport U D₁ W) from
      (transportOriginalModules (originalNestedImageEq U D₁ D₂ h₁₂)).map
      ((originalImageRestrictionFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)).map
        (canonicalSupportOpenRestrictionIso U D₂ W).hom ≫
          (canonicalSupportOpenRestrictionIso (originalImageOpen U D₂)
            (originalNestedOpen U D₁ D₂) (imageSupport U D₂ W)).hom) ≫
      (originalNestedSupportTransportIso U D₁ D₂ h₁₂ W).hom) =
    (show (transportOriginalModules (originalNestedImageEq U D₁ D₂ h₁₂)).obj
      ((originalImageRestrictionFunctor (originalImageOpen U D₂) (originalNestedOpen U D₁ D₂)).obj
        ((originalImageRestrictionFunctor U D₂).obj (originalPrimeSupportModule U W))) ⟶
      originalPrimeSupportModule (originalImageOpen U D₁) (imageSupport U D₁ W) from
      ((originalNestedRestrictionIso U D₁ D₂ h₁₂).app (originalPrimeSupportModule U W)).hom ≫
          (canonicalSupportOpenRestrictionIso U D₁ W).hom) := by
  exact nestedThetaMap_eq_direct U D₁ D₂ h₁₂ W


end
end Hironaka.HironakaNativeCanonicalSupportRestriction
