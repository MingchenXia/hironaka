import Hironaka.Resolution.HironakaNativeCanonicalSupportRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! The SAME actual finite cyclic row on every original smaller open.
The first complete blueprint node is the bounded whole-module scope here.
The full old-before-all-opens prime join is preserved separately and remains unfinished.
Ordinary original delta, no preservation/FP/comparison packet. Root owns artifacts/gates.
-/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff BigOperators
namespace Hironaka.HironakaNativeCyclicCokernelRestriction
noncomputable section
open Hironaka.HolomorphicIdealSheaves
  HironakaNativeOpenSectionIdealTransport HironakaNativeCanonicalSupportRestriction
  HironakaChowNativePrimeSupportContinuation HironakaSingularModuleSheafStalk
  HironakaChowNativeModuleStalkExact HironakaChowNativeFiniteFreeStalk
  HironakaSmoothCentreRealDomainActualSheafStalk

variable {n : ℕ}

abbrev OriginalModules (U : Opens (ComplexModel n)) :=
  SheafOfModules.{0} (forgetRing (originalOpenStructureSheaf U))

abbrev OriginalRingStalk (U : Opens (ComplexModel n)) (u : U) :=
  ↑((originalOpenStructureSheaf U).presheaf.stalk u)

abbrev OriginalModuleStalk (U : Opens (ComplexModel n))
    (M : OriginalModules U) (u : U) :=
  ↑((nativeStalkFunctor (originalOpenStructureSheaf U) u).obj M)

/-- The ACTUAL original inclusion, with the original native continuity. -/
def cyclicImageTopMap (U : Opens (ComplexModel n)) (D : Opens U) :
    TopCat.of (originalImageOpen U D) ⟶ TopCat.of U :=
  TopCat.ofHom ⟨originalImageInclusion U D,
    continuous_subtype_val.comp (originalImageCarrierIso U D).symm.contMDiff.continuous⟩

theorem cyclicImage_isOpenEmbedding
    (U : Opens (ComplexModel n)) (D : Opens U) :
    Topology.IsOpenEmbedding (cyclicImageTopMap U D).hom :=
  D.isOpenEmbedding'.comp (originalImageCarrierIso U D).symm.toHomeomorph.isOpenEmbedding

def cyclicImageFunctor (U : Opens (ComplexModel n)) (D : Opens U) :
    Opens (originalImageOpen U D) ⥤ Opens U :=
  (cyclicImage_isOpenEmbedding U D).functor

private instance cyclicImageFunctor_isContinuous
    (U : Opens (ComplexModel n)) (D : Opens U) :
    (cyclicImageFunctor U D).IsContinuous
      (Opens.grothendieckTopology (TopCat.of (originalImageOpen U D)))
      (Opens.grothendieckTopology (TopCat.of U)) :=
  (cyclicImage_isOpenEmbedding U D).functor_isContinuous

private instance cyclicImageFunctor_isCocontinuous
    (U : Opens (ComplexModel n)) (D : Opens U) :
    (cyclicImageFunctor U D).IsCocontinuous
      (Opens.grothendieckTopology (TopCat.of (originalImageOpen U D)))
      (Opens.grothendieckTopology (TopCat.of U)) :=
  ((cyclicImage_isOpenEmbedding U D).isOpenMap.adjunction.isCocontinuous_iff_coverPreserving
    (Opens.grothendieckTopology (TopCat.of (originalImageOpen U D)))
    (Opens.grothendieckTopology (TopCat.of U))).mpr
      (coverPreserving_opens_map (cyclicImageTopMap U D))

private instance cyclicImageFunctor_isLeftAdjoint
    (U : Opens (ComplexModel n)) (D : Opens U) :
    (cyclicImageFunctor U D).IsLeftAdjoint :=
  (cyclicImage_isOpenEmbedding U D).isOpenMap.adjunction.isLeftAdjoint

private def cyclicScalarPresheafIso (U : Opens (ComplexModel n)) (D : Opens U) :
    (cyclicImageFunctor U D).op ⋙ (forgetRing (originalOpenStructureSheaf U)).obj ≅
      (forgetRing (originalOpenStructureSheaf (originalImageOpen U D))).obj := by
  refine NatIso.ofComponents (fun A => (originalImageScalarEquiv U D A.unop).toRingCatIso) ?_
  intro A T f
  apply RingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (originalImageScalarEquiv_naturality U D A.unop T.unop (leOfHom f.unop) r).symm

private def cyclicRestrictionRingIso
    (U : Opens (ComplexModel n)) (D : Opens U) :
    forgetRing (originalOpenStructureSheaf (originalImageOpen U D)) ≅
      ((cyclicImageFunctor U D).sheafPushforwardContinuous RingCat.{0}
        (Opens.grothendieckTopology (TopCat.of (originalImageOpen U D)))
        (Opens.grothendieckTopology (TopCat.of U))).obj
          (forgetRing (originalOpenStructureSheaf U)) :=
  (fullyFaithfulSheafToPresheaf
    (Opens.grothendieckTopology (TopCat.of (originalImageOpen U D))) RingCat).preimageIso
      (cyclicScalarPresheafIso U D).symm

/-- The genuine inverse-ell morphism of sheaves of RINGS. -/
def cyclicRestrictionRingMap
    (U : Opens (ComplexModel n)) (D : Opens U) :
    forgetRing (originalOpenStructureSheaf (originalImageOpen U D)) ⟶
      ((cyclicImageFunctor U D).sheafPushforwardContinuous RingCat.{0}
        (Opens.grothendieckTopology (TopCat.of (originalImageOpen U D)))
        (Opens.grothendieckTopology (TopCat.of U))).obj
          (forgetRing (originalOpenStructureSheaf U)) :=
  (cyclicRestrictionRingIso U D).hom

theorem cyclicRestrictionRingMap_app
    (U : Opens (ComplexModel n)) (D : Opens U)
    (A : Opens (originalImageOpen U D))
    (a : (originalOpenStructureSheaf (originalImageOpen U D)).presheaf.obj (op A)) :
    (cyclicRestrictionRingMap U D).hom.app (op A) a =
      (originalImageScalarEquiv U D A).symm a := rfl

private instance cyclicRestrictionRingMap_isIso
    (U : Opens (ComplexModel n)) (D : Opens U) :
    IsIso (cyclicRestrictionRingMap U D) :=
  (cyclicRestrictionRingIso U D).isIso_hom

/-- The SAME original component modules and native actions, as a FULL functor Iso. -/
def originalRestrictionPushforwardIso
    (U : Opens (ComplexModel n)) (D : Opens U) :
    originalImageRestrictionFunctor U D ≅
      SheafOfModules.pushforward.{0} (cyclicRestrictionRingMap U D) := by
  exact NatIso.ofComponents (fun _ => Iso.refl _) (by intro M N f; rfl)

theorem originalRestrictionPushforwardIso_hom_app
    (U : Opens (ComplexModel n)) (D : Opens U)
    (M : OriginalModules U) (A : Opens (originalImageOpen U D))
    (s : ((originalImageRestrictionFunctor U D).obj M).val.obj (op A)) :
    ((originalRestrictionPushforwardIso U D).app M).hom.val.app (op A) s = s := rfl

theorem originalRestrictionPushforwardIso_inv_app
    (U : Opens (ComplexModel n)) (D : Opens U)
    (M : OriginalModules U) (A : Opens (originalImageOpen U D))
    (s : ((SheafOfModules.pushforward.{0} (cyclicRestrictionRingMap U D)).obj M).val.obj (op A)) :
    ((originalRestrictionPushforwardIso U D).app M).inv.val.app (op A) s = s := rfl


private instance originalRestriction_isLeftAdjoint
    (U : Opens (ComplexModel n)) (D : Opens U) :
    (originalImageRestrictionFunctor U D).IsLeftAdjoint := by
  have hφ : IsIso (cyclicRestrictionRingMap U D) :=
    (cyclicRestrictionRingIso U D).isIso_hom
  have hL : (SheafOfModules.pushforward.{0} (cyclicRestrictionRingMap U D)).IsLeftAdjoint :=
    @SheafOfModules.isLeftAdjoint_pushforward_of_isIso _ _ _ _ _ _
      (cyclicImageFunctor U D) _ _ _ (cyclicRestrictionRingMap U D)
      (cyclicImageFunctor_isCocontinuous U D) hφ (cyclicImageFunctor_isLeftAdjoint U D)
  exact @Functor.isLeftAdjoint_of_iso _ _ _ _ _ _
    (originalRestrictionPushforwardIso U D).symm hL

private instance originalRestriction_preservesZeroMorphisms
    (U : Opens (ComplexModel n)) (D : Opens U) :
    (originalImageRestrictionFunctor U D).PreservesZeroMorphisms where
  map_zero M N := by
    ext A s
    rfl

/-- Native free comparison, using the actual inverse unit comparison. -/
def originalCyclicRestrictionFreeIso
    (U : Opens (ComplexModel n)) (D : Opens U) (r : ℕ) :
    SheafOfModules.free
      (R := forgetRing (originalOpenStructureSheaf (originalImageOpen U D))) (Fin r) ≅
    (originalImageRestrictionFunctor U D).obj
      (SheafOfModules.free (R := forgetRing (originalOpenStructureSheaf U)) (Fin r)) :=
  SheafOfModules.mapFreeIso (originalImageRestrictionFunctor U D) (Fin r)
    (originalImageRestrictionUnitIso U D).symm

/-- The SAME original row, literally restricted via native free and unit comparisons. -/
def originalRestrictedCyclicRelation
    (U : Opens (ComplexModel n)) (D : Opens U) {r : ℕ}
    (δ : SheafOfModules.free (R := forgetRing (originalOpenStructureSheaf U)) (Fin r) ⟶
      SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U))) :
    SheafOfModules.free
      (R := forgetRing (originalOpenStructureSheaf (originalImageOpen U D))) (Fin r) ⟶
      SheafOfModules.unit (forgetRing (originalOpenStructureSheaf (originalImageOpen U D))) :=
  (originalCyclicRestrictionFreeIso U D r).hom ≫
    (originalImageRestrictionFunctor U D).map δ ≫
      (originalImageRestrictionUnitIso U D).hom

theorem originalRestrictedCyclicRelation_square
    (U : Opens (ComplexModel n)) (D : Opens U) {r : ℕ}
    (δ : SheafOfModules.free (R := forgetRing (originalOpenStructureSheaf U)) (Fin r) ⟶
      SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U))) :
    originalRestrictedCyclicRelation U D δ ≫ (originalImageRestrictionUnitIso U D).inv =
      (originalCyclicRestrictionFreeIso U D r).hom ≫
        (originalImageRestrictionFunctor U D).map δ := by
  simp only [originalRestrictedCyclicRelation, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- Genuine native cokernel comparison; preservation is derived, not an input. -/
def originalCyclicCokernelRestrictionIso
    (U : Opens (ComplexModel n)) (D : Opens U) {r : ℕ}
    (δ : SheafOfModules.free (R := forgetRing (originalOpenStructureSheaf U)) (Fin r) ⟶
      SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U))) :
    cokernel (originalRestrictedCyclicRelation U D δ) ≅
      (originalImageRestrictionFunctor U D).obj (cokernel δ) :=
  cokernel.mapIso (originalRestrictedCyclicRelation U D δ)
      ((originalImageRestrictionFunctor U D).map δ)
      (originalCyclicRestrictionFreeIso U D r)
      (originalImageRestrictionUnitIso U D).symm
      (originalRestrictedCyclicRelation_square U D δ) ≪≫
    asIso (cokernelComparison δ (originalImageRestrictionFunctor U D))

theorem originalCyclicCokernelRestrictionIso_quotient
    (U : Opens (ComplexModel n)) (D : Opens U) {r : ℕ}
    (δ : SheafOfModules.free (R := forgetRing (originalOpenStructureSheaf U)) (Fin r) ⟶
      SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U))) :
    cokernel.π (originalRestrictedCyclicRelation U D δ) ≫
      (originalCyclicCokernelRestrictionIso U D δ).hom =
    (originalImageRestrictionUnitIso U D).inv ≫
      (originalImageRestrictionFunctor U D).map (cokernel.π δ) := by
  simp [originalCyclicCokernelRestrictionIso, Category.assoc]

theorem originalCyclicCokernelRestrictionIso_inv_quotient
    (U : Opens (ComplexModel n)) (D : Opens U) {r : ℕ}
    (δ : SheafOfModules.free (R := forgetRing (originalOpenStructureSheaf U)) (Fin r) ⟶
      SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U))) :
    (originalImageRestrictionFunctor U D).map (cokernel.π δ) ≫
      (originalCyclicCokernelRestrictionIso U D δ).inv =
    (originalImageRestrictionUnitIso U D).hom ≫
      cokernel.π (originalRestrictedCyclicRelation U D δ) := by
  apply (cancel_mono (originalCyclicCokernelRestrictionIso U D δ).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [originalCyclicCokernelRestrictionIso_quotient]
  simp only [Iso.hom_inv_id_assoc]

theorem originalCyclicCokernelRestrictionIso_hom_numerator
    (U : Opens (ComplexModel n)) (D : Opens U) {r : ℕ}
    (δ : SheafOfModules.free (R := forgetRing (originalOpenStructureSheaf U)) (Fin r) ⟶
      SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U)))
    (A : Opens (originalImageOpen U D))
    (a : (originalOpenStructureSheaf (originalImageOpen U D)).presheaf.obj (op A)) :
    (originalCyclicCokernelRestrictionIso U D δ).hom.val.app (op A)
      ((cokernel.π (originalRestrictedCyclicRelation U D δ)).val.app (op A) a) =
    ((originalImageRestrictionFunctor U D).map (cokernel.π δ)).val.app (op A)
      ((originalImageScalarEquiv U D A).symm a) :=
  congrArg (fun f => f.val.app (op A) a)
    (originalCyclicCokernelRestrictionIso_quotient U D δ)

theorem originalCyclicCokernelRestrictionIso_inv_numerator
    (U : Opens (ComplexModel n)) (D : Opens U) {r : ℕ}
    (δ : SheafOfModules.free (R := forgetRing (originalOpenStructureSheaf U)) (Fin r) ⟶
      SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U)))
    (A : Opens (originalImageOpen U D))
    (a : (originalOpenStructureSheaf U).presheaf.obj
      (op ((cyclicImageFunctor U D).obj A))) :
    (originalCyclicCokernelRestrictionIso U D δ).inv.val.app (op A)
      (((originalImageRestrictionFunctor U D).map (cokernel.π δ)).val.app (op A) a) =
    (cokernel.π (originalRestrictedCyclicRelation U D δ)).val.app (op A)
      (originalImageScalarEquiv U D A a) :=
  congrArg (fun f => f.val.app (op A) a)
    (originalCyclicCokernelRestrictionIso_inv_quotient U D δ)


private def cyclicFreeOneUnitIso (U : Opens (ComplexModel n)) :
    SheafOfModules.free (R := forgetRing (originalOpenStructureSheaf U)) PUnit ≅
      SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U)) where
  hom := Sigma.desc (fun _ : PUnit => 𝟙 _)
  inv := SheafOfModules.ιFree PUnit.unit
  hom_inv_id := by
    apply Sigma.hom_ext
    intro i
    cases i
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ SheafOfModules.ιFree
        (R := forgetRing (originalOpenStructureSheaf U)) PUnit.unit)
        (Sigma.ι_desc (fun _ : PUnit => 𝟙
          (SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U)))) PUnit.unit)).trans
          ((Category.id_comp _).trans (Category.comp_id _).symm))
  inv_hom_id := Sigma.ι_desc (fun _ : PUnit => 𝟙 _) PUnit.unit

/-- The actual row gives a finite free presentation. No kernel-coherence input. -/
private theorem cyclicCokernel_isFinitePresentation
    (U : Opens (ComplexModel n)) {r : ℕ}
    (δ : SheafOfModules.free (R := forgetRing (originalOpenStructureSheaf U)) (Fin r) ⟶
      SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U))) :
    (cokernel δ).IsFinitePresentation := by
  let e := cyclicFreeOneUnitIso U
  let f := δ ≫ e.inv
  let g := e.hom ≫ cokernel.π δ
  have hfg : f ≫ g = 0 := by
    simp only [f, g, Category.assoc, Iso.inv_hom_id_assoc, cokernel.condition]
  have hc : IsColimit (CokernelCofork.ofπ g hfg) := by
    refine IsCokernel.ofIso δ (cokernelIsCokernel δ) _ (Iso.refl _) e.symm (Iso.refl _) ?_ ?_
    · simp only [f, Iso.refl_hom, Category.id_comp, Iso.symm_hom]
    · simp only [g, Iso.symm_hom, CokernelCofork.π_ofπ, Iso.inv_hom_id_assoc,
        Iso.refl_hom, Category.comp_id, Cofork.π_ofπ]
  let P := SheafOfModules.presentationOfIsCokernelFree f g hfg hc
  let q := P.quasicoherentData
  have hq : q.IsFinitePresentation := by
    constructor
    intro V
    exact
      { isFiniteType_generators := ⟨inferInstanceAs (Finite PUnit)⟩
        isFiniteType_relations := ⟨inferInstanceAs (Finite (Fin r))⟩ }
  exact ⟨q, hq⟩

theorem originalRestrictedCyclicCokernel_isFinitePresentation
    (U : Opens (ComplexModel n)) (D : Opens U) {r : ℕ}
    (δ : SheafOfModules.free (R := forgetRing (originalOpenStructureSheaf U)) (Fin r) ⟶
      SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U))) :
    (cokernel (originalRestrictedCyclicRelation U D δ)).IsFinitePresentation :=
  cyclicCokernel_isFinitePresentation (originalImageOpen U D)
    (originalRestrictedCyclicRelation U D δ)


/-- The ACTUAL coefficient of the fixed row; it is not a reselected old generator. -/
def relationCoefficient (U : Opens (ComplexModel n)) {r : ℕ}
    (δ : SheafOfModules.free (R := forgetRing (originalOpenStructureSheaf U)) (Fin r) ⟶
      SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U))) (i : Fin r) :
    (originalOpenStructureSheaf U).presheaf.obj (op ⊤) :=
  δ.val.app (op ⊤)
    ((SheafOfModules.freeSection (R := forgetRing (originalOpenStructureSheaf U)) i).val (op ⊤))

def restrictOriginalCoefficient (U : Opens (ComplexModel n)) (D : Opens U)
    (a : (originalOpenStructureSheaf U).presheaf.obj (op ⊤)) :
    (originalOpenStructureSheaf (originalImageOpen U D)).presheaf.obj (op ⊤) :=
  originalImageScalarEquiv U D ⊤
    ((originalOpenStructureSheaf U).presheaf.map
      (homOfLE (show (cyclicImageFunctor U D).obj ⊤ ≤ ⊤ from le_top)).op a)

private theorem cyclicFreeSection_ι (U : Opens (ComplexModel n)) {r : ℕ}
    (i : Fin r) (A : Opens U) :
    (SheafOfModules.freeSection (R := forgetRing (originalOpenStructureSheaf U)) i).val (op A) =
      (SheafOfModules.ιFree (R := forgetRing (originalOpenStructureSheaf U)) i).val.app
        (op A) (1 : (originalOpenStructureSheaf U).presheaf.obj (op A)) := rfl

private theorem relationCoefficient_app (U : Opens (ComplexModel n)) {r : ℕ}
    (δ : SheafOfModules.free (R := forgetRing (originalOpenStructureSheaf U)) (Fin r) ⟶
      SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U)))
    (i : Fin r) (A : Opens U) :
    δ.val.app (op A)
      ((SheafOfModules.freeSection (R := forgetRing (originalOpenStructureSheaf U)) i).val (op A)) =
    (originalOpenStructureSheaf U).presheaf.map (homOfLE (show A ≤ ⊤ from le_top)).op
      (relationCoefficient U δ i) :=
  (PresheafOfModules.sections_property
    (SheafOfModules.sectionsMap δ
      (SheafOfModules.freeSection (R := forgetRing (originalOpenStructureSheaf U)) i))
    (homOfLE (show A ≤ ⊤ from le_top)).op).symm

private theorem originalCyclicRestrictionFreeIso_basis
    (U : Opens (ComplexModel n)) (D : Opens U) (r : ℕ)
    (i : Fin r) (A : Opens (originalImageOpen U D)) :
    (originalCyclicRestrictionFreeIso U D r).hom.val.app (op A)
      ((SheafOfModules.freeSection
        (R := forgetRing (originalOpenStructureSheaf (originalImageOpen U D))) i).val (op A)) =
    (SheafOfModules.freeSection (R := forgetRing (originalOpenStructureSheaf U)) i).val
      (op ((cyclicImageFunctor U D).obj A)) := by
  have h := congrArg (fun f => f.val.app (op A)
      (1 : (originalOpenStructureSheaf (originalImageOpen U D)).presheaf.obj (op A)))
    (SheafOfModules.ιFree_mapFreeIso_hom (originalImageRestrictionFunctor U D) (Fin r)
      (originalImageRestrictionUnitIso U D).symm i)
  have hone : (originalImageRestrictionUnitIso U D).inv.val.app (op A)
      (1 : (originalOpenStructureSheaf (originalImageOpen U D)).presheaf.obj (op A)) =
      (1 : (originalOpenStructureSheaf U).presheaf.obj
        (op ((cyclicImageFunctor U D).obj A))) :=
    (originalImageScalarEquiv U D A).symm.map_one
  change (originalCyclicRestrictionFreeIso U D r).hom.val.app (op A)
      ((SheafOfModules.ιFree (R := forgetRing
        (originalOpenStructureSheaf (originalImageOpen U D))) i).val.app (op A)
          (1 : (originalOpenStructureSheaf (originalImageOpen U D)).presheaf.obj (op A))) =
    (SheafOfModules.ιFree (R := forgetRing (originalOpenStructureSheaf U)) i).val.app
      (op ((cyclicImageFunctor U D).obj A))
      ((originalImageRestrictionUnitIso U D).inv.val.app (op A)
        (1 : (originalOpenStructureSheaf (originalImageOpen U D)).presheaf.obj (op A))) at h
  rw [hone] at h
  exact (congrArg ((originalCyclicRestrictionFreeIso U D r).hom.val.app (op A))
    (cyclicFreeSection_ι (originalImageOpen U D) i A)).trans
      (h.trans (cyclicFreeSection_ι U i ((cyclicImageFunctor U D).obj A)).symm)

theorem originalRestrictedCyclicRelation_coefficient
    (U : Opens (ComplexModel n)) (D : Opens U) {r : ℕ}
    (δ : SheafOfModules.free (R := forgetRing (originalOpenStructureSheaf U)) (Fin r) ⟶
      SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U))) (i : Fin r) :
    relationCoefficient (originalImageOpen U D) (originalRestrictedCyclicRelation U D δ) i =
      restrictOriginalCoefficient U D (relationCoefficient U δ i) := by
  change originalImageScalarEquiv U D ⊤
      (δ.val.app (op ((cyclicImageFunctor U D).obj ⊤))
        ((originalCyclicRestrictionFreeIso U D r).hom.val.app (op ⊤)
          ((SheafOfModules.freeSection
            (R := forgetRing (originalOpenStructureSheaf (originalImageOpen U D))) i).val (op ⊤)))) = _
  rw [originalCyclicRestrictionFreeIso_basis, relationCoefficient_app]
  rfl

/-- The actual full native unit map on the literal original stalk. -/
def originalUnitDomainStalkMap
    (U : Opens (ComplexModel n)) {M : OriginalModules U}
    (κ : SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U)) ⟶ M) (u : U) :
    OriginalRingStalk U u →ₗ[OriginalRingStalk U u] OriginalModuleStalk U M u := by
  letI := nativeSheafStalkModule (originalOpenStructureSheaf U)
    (SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U))) u
  exact (stalkLinearMap (R := (originalOpenStructureSheaf U).presheaf) κ.val u).comp
    (unitStalkLinearEquiv (originalOpenStructureSheaf U) u).symm.toLinearMap

def originalGeneratorIdeal (U : Opens (ComplexModel n)) {r : ℕ}
    (g : Fin r → (originalOpenStructureSheaf U).presheaf.obj (op ⊤)) (u : U) :
    Ideal (OriginalRingStalk U u) :=
  Ideal.span (Set.range fun i =>
    (originalOpenStructureSheaf U).presheaf.germ ⊤ u (by trivial) (g i))

end
end Hironaka.HironakaNativeCyclicCokernelRestriction
