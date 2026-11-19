import Hironaka.Resolution.HironakaNativeCyclicCokernelRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! The fixed original prime target and its SAME finite cyclic row on every smaller open.
One complete daughter blueprint node FIRST; the genuine generic coker parent is accepted.
Old data are chosen ONCE before ALL D. No preservation/FP/comparison packet.
ROOT alone owns native artifacts, gates and readiness.
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

structure NativePrimePresentationData (p : ComplexModel n)
    (P : Ideal (actualComplexStructureStalk (n := n) p)) where
  U : Opens (ComplexModel n)
  hpU : p ∈ U
  r : ℕ
  g : Fin r → (originalOpenStructureSheaf U).presheaf.obj (op ⊤)
  W : Set U
  δ : SheafOfModules.free (R := forgetRing (originalOpenStructureSheaf U)) (Fin r) ⟶
    SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U))
  C : OriginalModules U
  κ : SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U)) ⟶ C
  e0 : cokernel δ ≅ C
  ν0 : C ≅ originalPrimeSupportModule U W
  analytic : IsComplexAnalyticSubset (n := n) W
  mem : (⟨p, hpU⟩ : U) ∈ W
  irreducible : IsComplexAnalyticallyIrreducible (n := n) W
  finitePresentation : C.IsFinitePresentation
  e0_quotient : cokernel.π δ ≫ e0.hom = κ
  ν0_quotient : κ ≫ ν0.hom = originalPrimeSupportQuotient U W
  whole : ∀ y : U,
    originalGeneratorIdeal U g y =
      Ideal.map (actualOpenLiteralStalkEquiv U y).toRingHom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) y)
  kernel : ∀ (y : U) (s : OriginalRingStalk U y),
    originalUnitDomainStalkMap U κ y s = 0 ↔ s ∈ originalGeneratorIdeal U g y
  quotient : ∀ y : U,
    ModuleCat.of (OriginalRingStalk U y)
      (OriginalRingStalk U y ⧸ (originalGeneratorIdeal U g y : Submodule _ _)) ≅
        (nativeStalkFunctor (originalOpenStructureSheaf U) y).obj C
  quotient_mk : ∀ (y : U) (s : OriginalRingStalk U y),
    (quotient y).hom (Submodule.Quotient.mk s) = originalUnitDomainStalkMap U κ y s
  prime_at_p : ∀ s : actualComplexStructureStalk (n := n) p,
    originalUnitDomainStalkMap U κ (⟨p, hpU⟩ : U)
      (originalRestrictionStalkEquiv U (⟨p, hpU⟩ : U) s) = 0 ↔ s ∈ P
  old_domain_continuation :
    ∀ (G : OriginalModules U) (_hG : G.IsFiniteType) (f : G ⟶ C),
      stalkLinearMap f.val (⟨p, hpU⟩ : U) = 0 → f = 0


private theorem exists_oldPrimePresentationData (p : ComplexModel n)
    (P : Ideal (actualComplexStructureStalk (n := n) p)) [P.IsPrime] :
    Nonempty (NativePrimePresentationData p P) := by
  classical
  obtain ⟨U, hpU, r, g, W, δ, C, κ, hW, hpW, hIrr, hFP,
    ⟨e0, he0⟩, ⟨ν0, hν0⟩, hAll, hP, hCont⟩ :=
    exists_native_prime_support_continuation p P
  choose Q hQ using fun y => (hAll y).2.2
  exact ⟨{
    U := U
    hpU := hpU
    r := r
    g := g
    W := W
    δ := δ
    C := C
    κ := κ
    e0 := e0
    ν0 := ν0
    analytic := hW
    mem := hpW
    irreducible := hIrr
    finitePresentation := hFP
    e0_quotient := he0
    ν0_quotient := hν0
    whole := fun y => (hAll y).1
    kernel := fun y => (hAll y).2.1
    quotient := Q
    quotient_mk := hQ
    prime_at_p := hP
    old_domain_continuation := hCont }⟩

private def primeRestrictedTarget {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (D : Opens A.U) : OriginalModules (originalImageOpen A.U D) :=
  cokernel (originalRestrictedCyclicRelation A.U D A.δ)

private def primeRestrictedQuotient {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (D : Opens A.U) :
    SheafOfModules.unit (forgetRing (originalOpenStructureSheaf (originalImageOpen A.U D))) ⟶
      primeRestrictedTarget A D :=
  cokernel.π (originalRestrictedCyclicRelation A.U D A.δ)

private def primeRestrictedCokernelIso {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (D : Opens A.U) :
    primeRestrictedTarget A D ≅ (originalImageRestrictionFunctor A.U D).obj A.C :=
  originalCyclicCokernelRestrictionIso A.U D A.δ ≪≫
    (originalImageRestrictionFunctor A.U D).mapIso A.e0

private def primeRestrictedSupportIso {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (D : Opens A.U) :
    primeRestrictedTarget A D ≅
      originalPrimeSupportModule (originalImageOpen A.U D)
        ((originalImageInclusion A.U D) ⁻¹' A.W) :=
  primeRestrictedCokernelIso A D ≪≫
    (originalImageRestrictionFunctor A.U D).mapIso A.ν0 ≪≫
      canonicalSupportOpenRestrictionIso A.U D A.W

private def primeRestrictedGenerators {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (D : Opens A.U) :
    Fin A.r → (originalOpenStructureSheaf (originalImageOpen A.U D)).presheaf.obj (op ⊤) :=
  fun i => restrictOriginalCoefficient A.U D (A.g i)

private def primeOriginalStalkReadback {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (D : Opens A.U) (b : originalImageOpen A.U D) :
    OriginalModuleStalk A.U A.C (originalImageInclusion A.U D b) ≃+
      OriginalModuleStalk (originalImageOpen A.U D) (primeRestrictedTarget A D) b :=
  (((nativeStalkFunctor (originalOpenStructureSheaf A.U)
      (originalImageInclusion A.U D b)).mapIso A.ν0).toLinearEquiv.toAddEquiv).trans
    ((canonicalSupportRestrictionStalkEquiv A.U D A.W b).trans
      (((nativeStalkFunctor (originalOpenStructureSheaf (originalImageOpen A.U D)) b).mapIso
        (primeRestrictedSupportIso A D)).toLinearEquiv.toAddEquiv.symm))

private def coefficientPreimageOpen (U : Opens (ComplexModel n)) (D : Opens U)
    (O : Opens U) : Opens (originalImageOpen U D) :=
  (Opens.map (cyclicImageTopMap U D)).obj O

private theorem coefficientImagePreimage_le
    (U : Opens (ComplexModel n)) (D : Opens U) (O : Opens U) :
    (cyclicImageFunctor U D).obj (coefficientPreimageOpen U D O) ≤ O := by
  rintro u ⟨b, hb, rfl⟩
  exact hb

structure NativeRestrictedPrimeCokernelData {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (D : Opens A.U) where
  finitePresentation : (primeRestrictedTarget A D).IsFinitePresentation
  restrictedOld_finitePresentation :
    ((originalImageRestrictionFunctor A.U D).obj A.C).IsFinitePresentation
  support_finitePresentation :
    (originalPrimeSupportModule (originalImageOpen A.U D)
      ((originalImageInclusion A.U D) ⁻¹' A.W)).IsFinitePresentation
  quotient_readback :
    primeRestrictedQuotient A D ≫ (primeRestrictedCokernelIso A D).hom =
      (originalImageRestrictionUnitIso A.U D).inv ≫
        (originalImageRestrictionFunctor A.U D).map A.κ
  quotient_readback_inv :
    (originalImageRestrictionFunctor A.U D).map A.κ ≫ (primeRestrictedCokernelIso A D).inv =
      (originalImageRestrictionUnitIso A.U D).hom ≫ primeRestrictedQuotient A D
  quotient_support :
    primeRestrictedQuotient A D ≫ (primeRestrictedSupportIso A D).hom =
      originalPrimeSupportQuotient (originalImageOpen A.U D)
        ((originalImageInclusion A.U D) ⁻¹' A.W)
  quotient_support_inv :
    originalPrimeSupportQuotient (originalImageOpen A.U D)
        ((originalImageInclusion A.U D) ⁻¹' A.W) ≫ (primeRestrictedSupportIso A D).inv =
      primeRestrictedQuotient A D
  whole : ∀ b : originalImageOpen A.U D,
    originalGeneratorIdeal (originalImageOpen A.U D) (primeRestrictedGenerators A D) b =
      Ideal.map (actualOpenLiteralStalkEquiv (originalImageOpen A.U D) b).toRingHom
        (actualWholeSheafStalkIdeal
          (vanishingIdeal (n := n) ((originalImageInclusion A.U D) ⁻¹' A.W)) b)
  ideal_map : ∀ b : originalImageOpen A.U D,
    originalGeneratorIdeal (originalImageOpen A.U D) (primeRestrictedGenerators A D) b =
      Ideal.map (originalImageStalkRingEquiv A.U D b).toRingHom
        (originalGeneratorIdeal A.U A.g (originalImageInclusion A.U D b))
  kernel : ∀ (b : originalImageOpen A.U D)
    (s : OriginalRingStalk (originalImageOpen A.U D) b),
    originalUnitDomainStalkMap (originalImageOpen A.U D) (primeRestrictedQuotient A D) b s = 0 ↔
      s ∈ originalGeneratorIdeal (originalImageOpen A.U D) (primeRestrictedGenerators A D) b
  quotient : ∀ b : originalImageOpen A.U D,
    ModuleCat.of (OriginalRingStalk (originalImageOpen A.U D) b)
      (OriginalRingStalk (originalImageOpen A.U D) b ⧸
        (originalGeneratorIdeal (originalImageOpen A.U D) (primeRestrictedGenerators A D) b :
          Submodule _ _)) ≅
      (nativeStalkFunctor (originalOpenStructureSheaf (originalImageOpen A.U D)) b).obj
        (primeRestrictedTarget A D)
  quotient_mk : ∀ (b : originalImageOpen A.U D)
    (s : OriginalRingStalk (originalImageOpen A.U D) b),
    (quotient b).hom (Submodule.Quotient.mk s) =
      originalUnitDomainStalkMap (originalImageOpen A.U D) (primeRestrictedQuotient A D) b s
  quotient_inv_numerator : ∀ (b : originalImageOpen A.U D)
    (s : OriginalRingStalk (originalImageOpen A.U D) b),
    (quotient b).inv
      (originalUnitDomainStalkMap (originalImageOpen A.U D) (primeRestrictedQuotient A D) b s) =
      Submodule.Quotient.mk s
  readback_smul : ∀ (b : originalImageOpen A.U D)
    (r : OriginalRingStalk A.U (originalImageInclusion A.U D b))
    (m : OriginalModuleStalk A.U A.C (originalImageInclusion A.U D b)),
    primeOriginalStalkReadback A D b (r • m) =
      (originalImageStalkRingEquiv A.U D b r) • primeOriginalStalkReadback A D b m
  readback_inv_smul : ∀ (b : originalImageOpen A.U D)
    (r : OriginalRingStalk (originalImageOpen A.U D) b)
    (m : OriginalModuleStalk (originalImageOpen A.U D) (primeRestrictedTarget A D) b),
    (primeOriginalStalkReadback A D b).symm (r • m) =
      (originalImageStalkRingEquiv A.U D b).symm r •
        (primeOriginalStalkReadback A D b).symm m
  readback_numerator : ∀ (b : originalImageOpen A.U D)
    (r : OriginalRingStalk A.U (originalImageInclusion A.U D b)),
    primeOriginalStalkReadback A D b
      (originalUnitDomainStalkMap A.U A.κ (originalImageInclusion A.U D b) r) =
    originalUnitDomainStalkMap (originalImageOpen A.U D) (primeRestrictedQuotient A D) b
      (originalImageStalkRingEquiv A.U D b r)
  readback_inv_numerator : ∀ (b : originalImageOpen A.U D)
    (r : OriginalRingStalk (originalImageOpen A.U D) b),
    (primeOriginalStalkReadback A D b).symm
      (originalUnitDomainStalkMap (originalImageOpen A.U D) (primeRestrictedQuotient A D) b r) =
    originalUnitDomainStalkMap A.U A.κ (originalImageInclusion A.U D b)
      ((originalImageStalkRingEquiv A.U D b).symm r)

  readback_germ : ∀ (b : originalImageOpen A.U D) (O : Opens A.U)
    (hu : originalImageInclusion A.U D b ∈ O) (s : A.C.val.obj (op O)),
    primeOriginalStalkReadback A D b
      (TopCat.Presheaf.germ A.C.val.presheaf O (originalImageInclusion A.U D b) hu s) =
    TopCat.Presheaf.germ (primeRestrictedTarget A D).val.presheaf
      (coefficientPreimageOpen A.U D O) b hu
      ((primeRestrictedSupportIso A D).inv.val.app (op (coefficientPreimageOpen A.U D O))
        ((canonicalSupportOpenRestrictionIso A.U D A.W).hom.val.app
          (op (coefficientPreimageOpen A.U D O))
          (A.ν0.hom.val.app
            (op ((cyclicImageFunctor A.U D).obj (coefficientPreimageOpen A.U D O)))
            (A.C.val.map (homOfLE (coefficientImagePreimage_le A.U D O)).op s))))
  readback_symm_germ : ∀ (b : originalImageOpen A.U D)
    (T : Opens (originalImageOpen A.U D)) (hb : b ∈ T)
    (t : (primeRestrictedTarget A D).val.obj (op T)),
    (primeOriginalStalkReadback A D b).symm
      (TopCat.Presheaf.germ (primeRestrictedTarget A D).val.presheaf T b hb t) =
    TopCat.Presheaf.germ A.C.val.presheaf ((cyclicImageFunctor A.U D).obj T)
      (originalImageInclusion A.U D b) ⟨b, hb, rfl⟩
      (A.ν0.inv.val.app (op ((cyclicImageFunctor A.U D).obj T))
        ((canonicalSupportOpenRestrictionIso A.U D A.W).inv.val.app (op T)
          ((primeRestrictedSupportIso A D).hom.val.app (op T) t)))

-- Complete type-valued OUTPUT, not a hypothesis. Old g is retained and actual
-- delta columns are related ONLY by WHOLE span equality, not a false coefficient equality.
structure NativePrimeAllOpenCokernelData (p : ComplexModel n)
    (P : Ideal (actualComplexStructureStalk (n := n) p)) where
  old : NativePrimePresentationData p P
  actual_delta_span : ∀ y : old.U,
    originalGeneratorIdeal old.U (relationCoefficient old.U old.δ) y =
      originalGeneratorIdeal old.U old.g y
  all_opens : ∀ D : Opens old.U, NativeRestrictedPrimeCokernelData old D


private theorem primeRestricted_quotient_readback {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (D : Opens A.U) :
    primeRestrictedQuotient A D ≫ (primeRestrictedCokernelIso A D).hom =
      (originalImageRestrictionUnitIso A.U D).inv ≫
        (originalImageRestrictionFunctor A.U D).map A.κ := by
  change cokernel.π (originalRestrictedCyclicRelation A.U D A.δ) ≫
      ((originalCyclicCokernelRestrictionIso A.U D A.δ).hom ≫
        (originalImageRestrictionFunctor A.U D).map A.e0.hom) = _
  rw [← Category.assoc, originalCyclicCokernelRestrictionIso_quotient,
    Category.assoc, ← Functor.map_comp, A.e0_quotient]

private theorem primeRestricted_quotient_readback_inv {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (D : Opens A.U) :
    (originalImageRestrictionFunctor A.U D).map A.κ ≫ (primeRestrictedCokernelIso A D).inv =
      (originalImageRestrictionUnitIso A.U D).hom ≫ primeRestrictedQuotient A D := by
  apply (cancel_mono (primeRestrictedCokernelIso A D).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [primeRestricted_quotient_readback]
  simp only [Iso.hom_inv_id_assoc]

private theorem primeRestricted_quotient_support {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (D : Opens A.U) :
    primeRestrictedQuotient A D ≫ (primeRestrictedSupportIso A D).hom =
      originalPrimeSupportQuotient (originalImageOpen A.U D)
        ((originalImageInclusion A.U D) ⁻¹' A.W) := by
  let R := originalImageRestrictionFunctor A.U D
  have hold : R.map A.κ ≫ R.map A.ν0.hom =
      R.map (originalPrimeSupportQuotient A.U A.W) := by
    rw [← R.map_comp, A.ν0_quotient]
  calc
    _ = ((primeRestrictedQuotient A D ≫ (primeRestrictedCokernelIso A D).hom) ≫
        R.map A.ν0.hom) ≫ (canonicalSupportOpenRestrictionIso A.U D A.W).hom := by
      simp only [primeRestrictedSupportIso, Iso.trans_hom, Functor.mapIso_hom,
        Category.assoc, R]
    _ = (((originalImageRestrictionUnitIso A.U D).inv ≫ R.map A.κ) ≫
        R.map A.ν0.hom) ≫ (canonicalSupportOpenRestrictionIso A.U D A.W).hom := by
      rw [primeRestricted_quotient_readback]
    _ = (originalImageRestrictionUnitIso A.U D).inv ≫
        ((R.map A.κ ≫ R.map A.ν0.hom) ≫
          (canonicalSupportOpenRestrictionIso A.U D A.W).hom) := by
      simp only [Category.assoc]
    _ = (originalImageRestrictionUnitIso A.U D).inv ≫
        (R.map (originalPrimeSupportQuotient A.U A.W) ≫
          (canonicalSupportOpenRestrictionIso A.U D A.W).hom) := by rw [hold]
    _ = (originalImageRestrictionUnitIso A.U D).inv ≫
        ((originalImageRestrictionUnitIso A.U D).hom ≫
          originalPrimeSupportQuotient (originalImageOpen A.U D)
            ((originalImageInclusion A.U D) ⁻¹' A.W)) := by
      rw [canonicalSupportOpenRestrictionIso_quotient]
    _ = _ := by simp only [Iso.inv_hom_id_assoc]

private theorem primeRestricted_quotient_support_inv {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (D : Opens A.U) :
    originalPrimeSupportQuotient (originalImageOpen A.U D)
        ((originalImageInclusion A.U D) ⁻¹' A.W) ≫ (primeRestrictedSupportIso A D).inv =
      primeRestrictedQuotient A D := by
  rw [← primeRestricted_quotient_support A D, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem primeRestricted_finitePresentation {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (D : Opens A.U) :
    (primeRestrictedTarget A D).IsFinitePresentation :=
  originalRestrictedCyclicCokernel_isFinitePresentation A.U D A.δ

private theorem primeRestricted_old_finitePresentation {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (D : Opens A.U) :
    ((originalImageRestrictionFunctor A.U D).obj A.C).IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation _).prop_of_iso (primeRestrictedCokernelIso A D)
    (primeRestricted_finitePresentation A D)

private theorem primeRestricted_support_finitePresentation {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (D : Opens A.U) :
    (originalPrimeSupportModule (originalImageOpen A.U D)
      ((originalImageInclusion A.U D) ⁻¹' A.W)).IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation _).prop_of_iso (primeRestrictedSupportIso A D)
    (primeRestricted_finitePresentation A D)



/-- The ordinary old-prime producer is chosen ONCE, independently of every later open. -/
private def chosenNativePrimePresentation (p : ComplexModel n)
    (P : Ideal (actualComplexStructureStalk (n := n) p)) [P.IsPrime] :
    NativePrimePresentationData p P :=
  Classical.choice (exists_oldPrimePresentationData p P)

/-- The actual reduced-support application of the SAME native old finite row.
The ordinary prime input selects all old data before ALL D; no comparison packet is input. -/
theorem exists_native_prime_support_cokernel_restrictions
    (p : ComplexModel n) (P : Ideal (actualComplexStructureStalk (n := n) p)) [P.IsPrime] :
    ∃ A : NativePrimePresentationData p P, ∀ D : Opens A.U,
      let B := originalImageOpen A.U D
      let δD := originalRestrictedCyclicRelation A.U D A.δ
      let E : cokernel δD ≅ originalPrimeSupportModule B
          ((originalImageInclusion A.U D) ⁻¹' A.W) :=
        (originalCyclicCokernelRestrictionIso A.U D A.δ ≪≫
          (originalImageRestrictionFunctor A.U D).mapIso A.e0) ≪≫
          (originalImageRestrictionFunctor A.U D).mapIso A.ν0 ≪≫
            canonicalSupportOpenRestrictionIso A.U D A.W
      (cokernel δD).IsFinitePresentation ∧
      (originalPrimeSupportModule B ((originalImageInclusion A.U D) ⁻¹' A.W)).IsFinitePresentation ∧
      cokernel.π δD ≫ E.hom =
        originalPrimeSupportQuotient B ((originalImageInclusion A.U D) ⁻¹' A.W) ∧
      originalPrimeSupportQuotient B ((originalImageInclusion A.U D) ⁻¹' A.W) ≫ E.inv =
        cokernel.π δD ∧
      (∀ (T : Opens B) (a : (originalOpenStructureSheaf B).presheaf.obj (op T)),
        E.hom.val.app (op T) ((cokernel.π δD).val.app (op T) a) =
          (originalPrimeSupportQuotient B ((originalImageInclusion A.U D) ⁻¹' A.W)).val.app
            (op T) a) ∧
      (∀ (T : Opens B) (a : (originalOpenStructureSheaf B).presheaf.obj (op T)),
        E.inv.val.app (op T)
          ((originalPrimeSupportQuotient B ((originalImageInclusion A.U D) ⁻¹' A.W)).val.app
            (op T) a) =
          (cokernel.π δD).val.app (op T) a) := by
  let A := chosenNativePrimePresentation p P
  refine ⟨A, ?_⟩
  intro D
  change (primeRestrictedTarget A D).IsFinitePresentation ∧
    (originalPrimeSupportModule (originalImageOpen A.U D)
      ((originalImageInclusion A.U D) ⁻¹' A.W)).IsFinitePresentation ∧
    primeRestrictedQuotient A D ≫ (primeRestrictedSupportIso A D).hom =
      originalPrimeSupportQuotient (originalImageOpen A.U D)
        ((originalImageInclusion A.U D) ⁻¹' A.W) ∧
    originalPrimeSupportQuotient (originalImageOpen A.U D)
        ((originalImageInclusion A.U D) ⁻¹' A.W) ≫ (primeRestrictedSupportIso A D).inv =
      primeRestrictedQuotient A D ∧ _ ∧ _
  refine ⟨primeRestricted_finitePresentation A D, primeRestricted_support_finitePresentation A D,
    primeRestricted_quotient_support A D, primeRestricted_quotient_support_inv A D, ?_, ?_⟩
  · intro T a
    exact congrArg (fun f => f.val.app (op T) a) (primeRestricted_quotient_support A D)
  · intro T a
    exact congrArg (fun f => f.val.app (op T) a) (primeRestricted_quotient_support_inv A D)

private theorem originalUnitDomainStalkMap_comp (U : Opens (ComplexModel n))
    {M N : OriginalModules U}
    (κ : SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U)) ⟶ M)
    (f : M ⟶ N) (u : U) (s : OriginalRingStalk U u) :
    originalUnitDomainStalkMap U (κ ≫ f) u s =
      ((nativeStalkFunctor (originalOpenStructureSheaf U) u).map f)
        (originalUnitDomainStalkMap U κ u s) :=
  DFunLike.congr_fun (stalkLinearMap_comp κ.val f.val u)
    ((unitStalkLinearEquiv (originalOpenStructureSheaf U) u).symm s)

/-- Forward the EXISTING native stalk action at an explicit original-sheaf type boundary. -/
private instance originalNativeStalkModule (U : Opens (ComplexModel n))
    (M : OriginalModules U) (u : U) :
    Module (OriginalRingStalk U u) ↑(TopCat.Presheaf.stalk M.val.presheaf u) :=
  nativeSheafStalkModule (originalOpenStructureSheaf U) M u

private theorem originalRelation_stalk_basis (U : Opens (ComplexModel n)) {r : ℕ}
    (δ : SheafOfModules.free (R := forgetRing (originalOpenStructureSheaf U)) (Fin r) ⟶
      SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U))) (u : U) (i : Fin r) :
    stalkInclusionLinearMap (originalOpenStructureSheaf U)
      (SheafOfModules.free (R := forgetRing (originalOpenStructureSheaf U)) (Fin r)) δ u
        ((finiteFreeStalkLinearEquiv (originalOpenStructureSheaf U) (Fin r) u).symm
          (Pi.single i 1)) =
      (originalOpenStructureSheaf U).presheaf.germ ⊤ u (by trivial) (relationCoefficient U δ i) := by
  have hm := (finiteFreeStalkLinearEquiv (originalOpenStructureSheaf U) (Fin r) u).symm_apply_eq.mpr
    (finiteFreeStalkLinearEquiv_freeSection_germ (originalOpenStructureSheaf U) (Fin r)
      u ⊤ (by trivial) i).symm
  exact (congrArg (stalkInclusionLinearMap (originalOpenStructureSheaf U)
    (SheafOfModules.free (R := forgetRing (originalOpenStructureSheaf U)) (Fin r)) δ u) hm).trans
      (stalkInclusionLinearMap_germ (originalOpenStructureSheaf U)
        (SheafOfModules.free (R := forgetRing (originalOpenStructureSheaf U)) (Fin r)) δ u ⊤
          (by trivial) ((SheafOfModules.freeSection
            (R := forgetRing (originalOpenStructureSheaf U)) i).val (op ⊤)))

/-- Only the genuine finite FREE STALK is decomposed; no global projectivity. -/
private theorem originalRelation_stalk_range (U : Opens (ComplexModel n)) {r : ℕ}
    (δ : SheafOfModules.free (R := forgetRing (originalOpenStructureSheaf U)) (Fin r) ⟶
      SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U))) (u : U) :
    LinearMap.range (stalkInclusionLinearMap (originalOpenStructureSheaf U)
      (SheafOfModules.free (R := forgetRing (originalOpenStructureSheaf U)) (Fin r)) δ u) =
        originalGeneratorIdeal U (relationCoefficient U δ) u := by
  classical
  let e := finiteFreeStalkLinearEquiv (originalOpenStructureSheaf U) (Fin r) u
  let L := stalkInclusionLinearMap (originalOpenStructureSheaf U)
    (SheafOfModules.free (R := forgetRing (originalOpenStructureSheaf U)) (Fin r)) δ u
  apply le_antisymm
  · rintro z ⟨v, rfl⟩
    have hv : v = ∑ i : Fin r, (e v i) • e.symm (Pi.single i 1) := by
      apply e.injective
      simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply]
      simpa only [Pi.basisFun_repr, Pi.basisFun_apply] using
        ((Pi.basisFun (OriginalRingStalk U u) (Fin r)).sum_repr (e v)).symm
    change L v ∈ _
    rw [hv, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul]
    apply Submodule.smul_mem
    exact (originalRelation_stalk_basis U δ u i) ▸ Ideal.subset_span (mem_range_self i)
  · apply Ideal.span_le.mpr
    rintro z ⟨i, rfl⟩
    exact ⟨e.symm (Pi.single i 1), originalRelation_stalk_basis U δ u i⟩

private instance originalStalk_preservesZeroMorphisms (U : Opens (ComplexModel n)) (u : U) :
    (nativeStalkFunctor (originalOpenStructureSheaf U) u).PreservesZeroMorphisms where
  map_zero _M _N := ModuleCat.hom_ext (stalkLinearMap_zero (R₀ := (originalOpenStructureSheaf U).presheaf) u)

private theorem originalCokernel_stalk_lift (U : Opens (ComplexModel n)) {r : ℕ}
    (δ : SheafOfModules.free (R := forgetRing (originalOpenStructureSheaf U)) (Fin r) ⟶
      SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U))) (u : U)
    (w : OriginalModuleStalk U (SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U))) u)
    (hw : stalkLinearMap (cokernel.π δ).val u w = 0) :
    ∃ v, stalkLinearMap δ.val u v = w := by
  let F := nativeStalkFunctor (originalOpenStructureSheaf U) u
  let S := ShortComplex.cokernelSequence δ
  have hepi : Epi S.g := by
    change Epi (cokernel.π δ)
    infer_instance
  have hfin : PreservesFiniteColimits F :=
    nativeStalkFunctor_preservesFiniteColimits (originalOpenStructureSheaf U) u
  have hshape : PreservesColimitsOfShape WalkingParallelPair F :=
    hfin.preservesFiniteColimits WalkingParallelPair
  have hpres : PreservesColimit (parallelPair δ 0) F := hshape.preservesColimit
  have hex : (S.map F).Exact :=
    (ShortComplex.cokernelSequence_exact δ).map_of_epi_of_preservesCokernel F hepi hpres
  exact ((S.map F).moduleCat_exact_iff.mp hex) w hw

private theorem originalCokernel_stalk_comp_zero (U : Opens (ComplexModel n)) {r : ℕ}
    (δ : SheafOfModules.free (R := forgetRing (originalOpenStructureSheaf U)) (Fin r) ⟶
      SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U))) (u : U)
    (v : OriginalModuleStalk U
      (SheafOfModules.free (R := forgetRing (originalOpenStructureSheaf U)) (Fin r)) u) :
    stalkLinearMap (cokernel.π δ).val u (stalkLinearMap δ.val u v) = 0 := by
  let F := nativeStalkFunctor (originalOpenStructureSheaf U) u
  let S := ShortComplex.cokernelSequence δ
  exact (S.map F).moduleCat_zero_apply v

private theorem originalCokernel_stalk_zero_iff (U : Opens (ComplexModel n)) {r : ℕ}
    (δ : SheafOfModules.free (R := forgetRing (originalOpenStructureSheaf U)) (Fin r) ⟶
      SheafOfModules.unit (forgetRing (originalOpenStructureSheaf U))) (u : U)
    (s : OriginalRingStalk U u) :
    originalUnitDomainStalkMap U (cokernel.π δ) u s = 0 ↔
      s ∈ originalGeneratorIdeal U (relationCoefficient U δ) u := by
  have hspan := originalRelation_stalk_range U δ u
  constructor
  · intro hs
    obtain ⟨v, hv⟩ := originalCokernel_stalk_lift U δ u
      ((unitStalkLinearEquiv (originalOpenStructureSheaf U) u).symm s) hs
    have hm : s ∈ LinearMap.range (stalkInclusionLinearMap (originalOpenStructureSheaf U)
        (SheafOfModules.free (R := forgetRing (originalOpenStructureSheaf U)) (Fin r)) δ u) :=
      ⟨v, (congrArg (unitStalkLinearEquiv (originalOpenStructureSheaf U) u) hv).trans
        ((unitStalkLinearEquiv (originalOpenStructureSheaf U) u).apply_symm_apply s)⟩
    exact Eq.mp (congrArg (fun T : Submodule (OriginalRingStalk U u) (OriginalRingStalk U u) =>
      s ∈ T) hspan) hm
  · intro hs
    have hm : s ∈ LinearMap.range (stalkInclusionLinearMap (originalOpenStructureSheaf U)
        (SheafOfModules.free (R := forgetRing (originalOpenStructureSheaf U)) (Fin r)) δ u) :=
      Eq.mpr (congrArg (fun T : Submodule (OriginalRingStalk U u) (OriginalRingStalk U u) =>
        s ∈ T) hspan) hs
    obtain ⟨v, rfl⟩ := hm
    have hunit := (unitStalkLinearEquiv (originalOpenStructureSheaf U) u).symm_apply_apply
      (stalkLinearMap δ.val u v)
    exact (congrArg (stalkLinearMap (cokernel.π δ).val u) hunit).trans
      (originalCokernel_stalk_comp_zero U δ u v)

private theorem primeActualDelta_span {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (u : A.U) :
    originalGeneratorIdeal A.U (relationCoefficient A.U A.δ) u =
      originalGeneratorIdeal A.U A.g u := by
  ext s
  have he : originalUnitDomainStalkMap A.U A.κ u s =
      ((nativeStalkFunctor (originalOpenStructureSheaf A.U) u).mapIso A.e0).toLinearEquiv
        (originalUnitDomainStalkMap A.U (cokernel.π A.δ) u s) := by
    have hκ := congrArg
      (fun f : SheafOfModules.unit (forgetRing (originalOpenStructureSheaf A.U)) ⟶ A.C =>
        originalUnitDomainStalkMap A.U f u s) A.e0_quotient
    exact hκ.symm.trans
      (originalUnitDomainStalkMap_comp A.U (cokernel.π A.δ) A.e0.hom u s)
  calc
    _ ↔ originalUnitDomainStalkMap A.U (cokernel.π A.δ) u s = 0 :=
      (originalCokernel_stalk_zero_iff A.U A.δ u s).symm
    _ ↔ ((nativeStalkFunctor (originalOpenStructureSheaf A.U) u).mapIso A.e0).toLinearEquiv
        (originalUnitDomainStalkMap A.U (cokernel.π A.δ) u s) = 0 :=
      (map_eq_zero_iff
        (((nativeStalkFunctor (originalOpenStructureSheaf A.U) u).mapIso A.e0).toLinearEquiv)
        (((nativeStalkFunctor (originalOpenStructureSheaf A.U) u).mapIso A.e0).toLinearEquiv.injective)).symm
    _ ↔ originalUnitDomainStalkMap A.U A.κ u s = 0 :=
      Iff.of_eq (congrArg (fun z : OriginalModuleStalk A.U A.C u => z = 0) he.symm)
    _ ↔ _ := A.kernel u s

private theorem originalCoefficient_stalk_restrict
    (U : Opens (ComplexModel n)) (D : Opens U)
    (a : (originalOpenStructureSheaf U).presheaf.obj (op ⊤))
    (b : originalImageOpen U D) :
    originalImageStalkRingEquiv U D b
      ((originalOpenStructureSheaf U).presheaf.germ ⊤ (originalImageInclusion U D b)
        (by trivial) a) =
    (originalOpenStructureSheaf (originalImageOpen U D)).presheaf.germ ⊤ b (by trivial)
      (restrictOriginalCoefficient U D a) := by
  have hres := (originalOpenStructureSheaf U).presheaf.germ_res_apply
    (homOfLE (show (cyclicImageFunctor U D).obj ⊤ ≤ ⊤ from le_top))
    (originalImageInclusion U D b) ⟨b, by trivial, rfl⟩ a
  exact (congrArg (originalImageStalkRingEquiv U D b) hres.symm).trans
    (originalImageStalkRingEquiv_germ U D b ⊤ (by trivial)
      ((originalOpenStructureSheaf U).presheaf.map
        (homOfLE (show (cyclicImageFunctor U D).obj ⊤ ≤ ⊤ from le_top)).op a))

private theorem primeRestricted_ideal_map {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (D : Opens A.U)
    (b : originalImageOpen A.U D) :
    originalGeneratorIdeal (originalImageOpen A.U D) (primeRestrictedGenerators A D) b =
      Ideal.map (originalImageStalkRingEquiv A.U D b).toRingHom
        (originalGeneratorIdeal A.U A.g (originalImageInclusion A.U D b)) := by
  rw [originalGeneratorIdeal, originalGeneratorIdeal, Ideal.map_span, ← Set.range_comp]
  exact congrArg Ideal.span (congrArg range
    (funext fun i => (originalCoefficient_stalk_restrict A.U D (A.g i) b).symm))


private def cyclicNormalizedBaseMap {T : TopCat.{0}} {F G : T.Presheaf CommRingCat.{0}}
    (f : PresheafedSpace.mk T F ⟶ PresheafedSpace.mk T G)
    (hf : f.base = 𝟙 T) : G ⟶ F :=
  f.c ≫ (TopCat.Presheaf.pushforwardEq hf F).hom ≫ (TopCat.Presheaf.Pushforward.id F).hom

private theorem cyclicNormalizedBaseMap_congr {T : TopCat.{0}} {F G : T.Presheaf CommRingCat.{0}}
    {f g : PresheafedSpace.mk T F ⟶ PresheafedSpace.mk T G} (h : f = g)
    (hf : f.base = 𝟙 T) (hg : g.base = 𝟙 T) :
    cyclicNormalizedBaseMap f hf = cyclicNormalizedBaseMap g hg := by
  cases h
  rfl

private theorem cyclicNormalizedBaseMap_id {T : TopCat.{0}} {F G : T.Presheaf CommRingCat.{0}}
    (c : G ⟶ F) :
    cyclicNormalizedBaseMap (⟨𝟙 T, c⟩ : PresheafedSpace.mk T F ⟶ PresheafedSpace.mk T G) rfl = c := by
  apply NatTrans.ext
  funext V
  change c.app V ≫ F.map (𝟙 V) ≫ 𝟙 (F.obj V) = c.app V
  rw [F.map_id, Category.comp_id, Category.comp_id]

private theorem cyclicNativeComparison_base (U : Opens (ComplexModel n)) :
    (ChartedSpace.restrictLocallyRingedSpaceIso (IM := 𝓘(ℂ, ComplexModel n)) U).hom.base =
      𝟙 (TopCat.of U) :=
  (congrArg (fun f => f.base) (actualLiteralStructureRingIso_native (n := n) U)).symm

/-- Reconstruct the public factory's SAME genuine native scalar Iso, with no private theorem call. -/
private def cyclicNativeLiteralIso (U : Opens (ComplexModel n)) :
    actualComplexStructureSheaf (n := n) U ≅ originalOpenStructureSheaf U := by
  let e := (LocallyRingedSpace.forgetToSheafedSpace ⋙
    SheafedSpace.forgetToPresheafedSpace).mapIso
      (ChartedSpace.restrictLocallyRingedSpaceIso (IM := 𝓘(ℂ, ComplexModel n)) U)
  let eP := PresheafedSpace.sheafIsoOfIso e
  let eQ := eP ≪≫ TopCat.Presheaf.pushforwardEq (cyclicNativeComparison_base U) _ ≪≫
    TopCat.Presheaf.Pushforward.id _
  exact (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology (TopCat.of U))
    CommRingCat).preimageIso eQ

private theorem cyclicNativeLiteralIso_eq (U : Opens (ComplexModel n)) :
    cyclicNativeLiteralIso U = (actualLiteralStructureRingIso (n := n) U).symm := by
  apply Iso.ext
  apply (sheafToPresheaf (Opens.grothendieckTopology (TopCat.of U)) CommRingCat).map_injective
  let f : PresheafedSpace.mk (TopCat.of U) (originalOpenStructureSheaf U).presheaf ⟶
      PresheafedSpace.mk (TopCat.of U) (actualComplexStructureSheaf (n := n) U).presheaf :=
    (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace).map
      (ChartedSpace.restrictLocallyRingedSpaceIso (IM := 𝓘(ℂ, ComplexModel n)) U).hom
  have hf : f.base = 𝟙 (TopCat.of U) := cyclicNativeComparison_base U
  change cyclicNormalizedBaseMap f hf = (actualLiteralStructureRingIso (n := n) U).inv.hom
  have h := cyclicNormalizedBaseMap_congr
    (show actualLiteralComparisonPresheafHom (n := n) U = f from
      actualLiteralStructureRingIso_native (n := n) U) rfl hf
  exact h.symm.trans (cyclicNormalizedBaseMap_id _)

private theorem originalLiteralStalk_eta (U : Opens (ComplexModel n)) (u : U) :
    actualOpenLiteralStalkEquiv U u = (actualLiteralStructureStalkEquiv (n := n) U u).symm := by
  change ((TopCat.Presheaf.stalkFunctor CommRingCat u).mapIso
      ((sheafToPresheaf (Opens.grothendieckTopology (TopCat.of U)) CommRingCat).mapIso
        (cyclicNativeLiteralIso U))).commRingCatIsoToRingEquiv = _
  rw [cyclicNativeLiteralIso_eq]
  rfl

private theorem originalLiteralStalk_beta (U : Opens (ComplexModel n)) (u : U)
    (r : actualComplexStructureStalk (n := n) u.val) :
    actualOpenLiteralStalkEquiv U u (actualOpenStalkRingEquiv (n := n) U u r) =
      actualOriginalRestrictionStalkEquiv (n := n) U u r := by
  have hη := actualLiteralStructureStalkEquiv_original (n := n) U u r
  have hv : (actualLiteralStructureStalkEquiv (n := n) U u).symm
      (actualOpenStalkRingEquiv (n := n) U u r) =
      actualOriginalRestrictionStalkEquiv (n := n) U u r :=
    (congrArg (actualLiteralStructureStalkEquiv (n := n) U u).symm hη.symm).trans
      ((actualLiteralStructureStalkEquiv (n := n) U u).symm_apply_apply _)
  exact (congrArg
    (fun e : actualComplexStructureStalk (n := n) u ≃+* OriginalRingStalk U u =>
      e (actualOpenStalkRingEquiv (n := n) U u r)) (originalLiteralStalk_eta U u)).trans hv

/-- Whole original ideals, via the actual ambient restriction square, for ANY subset. -/
private theorem originalWholeIdeal_restrict
    (U : Opens (ComplexModel n)) (D : Opens U) (W : Set U) (b : originalImageOpen U D) :
    Ideal.map (originalImageStalkRingEquiv U D b).toRingHom
      (Ideal.map (actualOpenLiteralStalkEquiv U (originalImageInclusion U D b)).toRingHom
        (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) (originalImageInclusion U D b))) =
    Ideal.map (actualOpenLiteralStalkEquiv (originalImageOpen U D) b).toRingHom
      (actualWholeSheafStalkIdeal
        (vanishingIdeal (n := n) ((originalImageInclusion U D) ⁻¹' W)) b) := by
  let B := originalImageOpen U D
  let u := originalImageInclusion U D b
  let T : Set (ComplexModel n) := (Subtype.val : U → ComplexModel n) '' W
  have hUW : (Subtype.val : U → ComplexModel n) ⁻¹' T = W := by
    ext v
    constructor
    · rintro ⟨w, hw, hwv⟩
      exact (Subtype.ext hwv : w = v) ▸ hw
    · intro hv
      exact ⟨v, hv, rfl⟩
  have hBW : (Subtype.val : B → ComplexModel n) ⁻¹' T =
      (originalImageInclusion U D) ⁻¹' W := by
    ext v
    constructor
    · rintro ⟨w, hw, hwv⟩
      change originalImageInclusion U D v ∈ W
      exact (Subtype.ext hwv : w = originalImageInclusion U D v) ▸ hw
    · intro hv
      exact ⟨originalImageInclusion U D v, hv, rfl⟩
  have hU : Ideal.map (actualOpenStalkRingEquiv (n := n) U u).toRingHom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) T) u.val) =
        actualWholeSheafStalkIdeal (vanishingIdeal (n := n) W) u := by
    simpa only [hUW] using map_actualOpenWholeStalkIdeal (n := n) U T u
  have hB : Ideal.map (actualOpenStalkRingEquiv (n := n) B b).toRingHom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) T) b.val) =
        actualWholeSheafStalkIdeal
          (vanishingIdeal (n := n) ((originalImageInclusion U D) ⁻¹' W)) b := by
    simpa only [hBW] using map_actualOpenWholeStalkIdeal (n := n) B T b
  have hcomp : (originalImageStalkRingEquiv U D b).toRingHom.comp
      ((actualOpenLiteralStalkEquiv U u).toRingHom.comp
        (actualOpenStalkRingEquiv (n := n) U u).toRingHom) =
      (actualOpenLiteralStalkEquiv B b).toRingHom.comp
        (actualOpenStalkRingEquiv (n := n) B b).toRingHom := by
    apply RingHom.ext
    intro r
    change originalImageStalkRingEquiv U D b
        (actualOpenLiteralStalkEquiv U u (actualOpenStalkRingEquiv (n := n) U u r)) =
      actualOpenLiteralStalkEquiv B b (actualOpenStalkRingEquiv (n := n) B b r)
    exact (congrArg (originalImageStalkRingEquiv U D b)
      (originalLiteralStalk_beta U u r)).trans
        ((originalImageStalkRingEquiv_original U D b
          (actualOriginalRestrictionStalkEquiv (n := n) U u r)).trans
          ((congrArg (actualOriginalRestrictionStalkEquiv (n := n) B b)
            ((actualOriginalRestrictionStalkEquiv (n := n) U u).symm_apply_apply r)).trans
              (originalLiteralStalk_beta B b r).symm))

  calc
    _ = Ideal.map (originalImageStalkRingEquiv U D b).toRingHom
        (Ideal.map (actualOpenLiteralStalkEquiv U u).toRingHom
          (Ideal.map (actualOpenStalkRingEquiv (n := n) U u).toRingHom
            (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) T) u.val))) := by rw [hU]
    _ = Ideal.map ((originalImageStalkRingEquiv U D b).toRingHom.comp
        ((actualOpenLiteralStalkEquiv U u).toRingHom.comp
          (actualOpenStalkRingEquiv (n := n) U u).toRingHom))
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) T) u.val) := by
      rw [Ideal.map_map, Ideal.map_map]
      rfl
    _ = Ideal.map ((actualOpenLiteralStalkEquiv B b).toRingHom.comp
        (actualOpenStalkRingEquiv (n := n) B b).toRingHom)
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) T) b.val) := by
      rw [hcomp]
      rfl
    _ = _ := by rw [← Ideal.map_map, hB]

private theorem primeRestricted_whole {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (D : Opens A.U) (b : originalImageOpen A.U D) :
    originalGeneratorIdeal (originalImageOpen A.U D) (primeRestrictedGenerators A D) b =
      Ideal.map (actualOpenLiteralStalkEquiv (originalImageOpen A.U D) b).toRingHom
        (actualWholeSheafStalkIdeal
          (vanishingIdeal (n := n) ((originalImageInclusion A.U D) ⁻¹' A.W)) b) := by
  rw [primeRestricted_ideal_map, A.whole]
  exact originalWholeIdeal_restrict A.U D A.W b


private theorem primeOldSupport_stalk_quotient {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (u : A.U) (r : OriginalRingStalk A.U u) :
    ((nativeStalkFunctor (originalOpenStructureSheaf A.U) u).mapIso A.ν0).toLinearEquiv
      (originalUnitDomainStalkMap A.U A.κ u r) =
      canonicalSupportQuotientStalkMap A.U A.W u r := by
  have h := originalUnitDomainStalkMap_comp A.U A.κ A.ν0.hom u r
  have hq := congrArg
    (fun f : SheafOfModules.unit (forgetRing (originalOpenStructureSheaf A.U)) ⟶
      originalPrimeSupportModule A.U A.W => originalUnitDomainStalkMap A.U f u r)
    A.ν0_quotient
  exact h.symm.trans hq

private theorem primeNewSupport_stalk_quotient {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (D : Opens A.U) (b : originalImageOpen A.U D)
    (r : OriginalRingStalk (originalImageOpen A.U D) b) :
    ((nativeStalkFunctor (originalOpenStructureSheaf (originalImageOpen A.U D)) b).mapIso
      (primeRestrictedSupportIso A D)).toLinearEquiv
        (originalUnitDomainStalkMap (originalImageOpen A.U D) (primeRestrictedQuotient A D) b r) =
      canonicalSupportQuotientStalkMap (originalImageOpen A.U D)
        ((originalImageInclusion A.U D) ⁻¹' A.W) b r := by
  have h := originalUnitDomainStalkMap_comp (originalImageOpen A.U D)
    (primeRestrictedQuotient A D) (primeRestrictedSupportIso A D).hom b r
  have hq := congrArg
    (fun f : SheafOfModules.unit (forgetRing (originalOpenStructureSheaf (originalImageOpen A.U D))) ⟶
      originalPrimeSupportModule (originalImageOpen A.U D)
        ((originalImageInclusion A.U D) ⁻¹' A.W) =>
      originalUnitDomainStalkMap (originalImageOpen A.U D) f b r)
    (primeRestricted_quotient_support A D)
  exact h.symm.trans hq

private theorem primeReadback_smul {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (D : Opens A.U) (b : originalImageOpen A.U D)
    (r : OriginalRingStalk A.U (originalImageInclusion A.U D b))
    (m : OriginalModuleStalk A.U A.C (originalImageInclusion A.U D b)) :
    primeOriginalStalkReadback A D b (r • m) =
      (originalImageStalkRingEquiv A.U D b r) • primeOriginalStalkReadback A D b m := by
  let eU := ((nativeStalkFunctor (originalOpenStructureSheaf A.U)
    (originalImageInclusion A.U D b)).mapIso A.ν0).toLinearEquiv
  let eB := ((nativeStalkFunctor (originalOpenStructureSheaf (originalImageOpen A.U D)) b).mapIso
    (primeRestrictedSupportIso A D)).toLinearEquiv
  change eB.symm (canonicalSupportRestrictionStalkEquiv A.U D A.W b (eU (r • m))) =
    (originalImageStalkRingEquiv A.U D b r) •
      eB.symm (canonicalSupportRestrictionStalkEquiv A.U D A.W b (eU m))
  exact (congrArg (fun z => eB.symm (canonicalSupportRestrictionStalkEquiv A.U D A.W b z))
    (eU.map_smul r m)).trans
      ((congrArg eB.symm (canonicalSupportRestrictionStalkEquiv_smul A.U D A.W b r (eU m))).trans
        (eB.symm.map_smul _ _))

private theorem primeReadback_inv_smul {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (D : Opens A.U) (b : originalImageOpen A.U D)
    (r : OriginalRingStalk (originalImageOpen A.U D) b)
    (m : OriginalModuleStalk (originalImageOpen A.U D) (primeRestrictedTarget A D) b) :
    (primeOriginalStalkReadback A D b).symm (r • m) =
      (originalImageStalkRingEquiv A.U D b).symm r •
        (primeOriginalStalkReadback A D b).symm m := by
  apply (primeOriginalStalkReadback A D b).injective
  rw [AddEquiv.apply_symm_apply, primeReadback_smul,
    AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

private theorem primeReadback_numerator {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (D : Opens A.U) (b : originalImageOpen A.U D)
    (r : OriginalRingStalk A.U (originalImageInclusion A.U D b)) :
    primeOriginalStalkReadback A D b
      (originalUnitDomainStalkMap A.U A.κ (originalImageInclusion A.U D b) r) =
    originalUnitDomainStalkMap (originalImageOpen A.U D) (primeRestrictedQuotient A D) b
      (originalImageStalkRingEquiv A.U D b r) := by
  let eB := ((nativeStalkFunctor (originalOpenStructureSheaf (originalImageOpen A.U D)) b).mapIso
    (primeRestrictedSupportIso A D)).toLinearEquiv
  change eB.symm (canonicalSupportRestrictionStalkEquiv A.U D A.W b
    (((nativeStalkFunctor (originalOpenStructureSheaf A.U) (originalImageInclusion A.U D b)).mapIso
      A.ν0).toLinearEquiv
        (originalUnitDomainStalkMap A.U A.κ (originalImageInclusion A.U D b) r))) = _
  exact (congrArg (fun z => eB.symm (canonicalSupportRestrictionStalkEquiv A.U D A.W b z))
    (primeOldSupport_stalk_quotient A (originalImageInclusion A.U D b) r)).trans
      ((congrArg eB.symm (canonicalSupportRestrictionStalkEquiv_quotient A.U D A.W b r)).trans
        (eB.symm_apply_eq.mpr
          (primeNewSupport_stalk_quotient A D b (originalImageStalkRingEquiv A.U D b r)).symm))

private theorem primeReadback_inv_numerator {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (D : Opens A.U) (b : originalImageOpen A.U D)
    (r : OriginalRingStalk (originalImageOpen A.U D) b) :
    (primeOriginalStalkReadback A D b).symm
      (originalUnitDomainStalkMap (originalImageOpen A.U D) (primeRestrictedQuotient A D) b r) =
    originalUnitDomainStalkMap A.U A.κ (originalImageInclusion A.U D b)
      ((originalImageStalkRingEquiv A.U D b).symm r) := by
  apply (primeOriginalStalkReadback A D b).injective
  rw [AddEquiv.apply_symm_apply, primeReadback_numerator, RingEquiv.apply_symm_apply]

private theorem primeRestricted_kernel {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (D : Opens A.U) (b : originalImageOpen A.U D)
    (s : OriginalRingStalk (originalImageOpen A.U D) b) :
    originalUnitDomainStalkMap (originalImageOpen A.U D) (primeRestrictedQuotient A D) b s = 0 ↔
      s ∈ originalGeneratorIdeal (originalImageOpen A.U D) (primeRestrictedGenerators A D) b := by
  obtain ⟨r, rfl⟩ := (originalImageStalkRingEquiv A.U D b).surjective s
  let lam := originalImageStalkRingEquiv A.U D b
  let τ := primeOriginalStalkReadback A D b
  let q := originalGeneratorIdeal A.U A.g (originalImageInclusion A.U D b)
  have hn := primeReadback_numerator A D b r
  have hz : originalUnitDomainStalkMap (originalImageOpen A.U D) (primeRestrictedQuotient A D) b
      (lam r) = 0 ↔ originalUnitDomainStalkMap A.U A.κ (originalImageInclusion A.U D b) r = 0 :=
    (Iff.of_eq (congrArg
      (fun z : OriginalModuleStalk (originalImageOpen A.U D) (primeRestrictedTarget A D) b => z = 0)
      hn.symm)).trans (map_eq_zero_iff τ τ.injective)
  have hm : lam r ∈ Ideal.map lam.toRingHom q ↔ r ∈ q := by
    change r ∈ Ideal.comap lam.toRingHom (Ideal.map lam.toRingHom q) ↔ r ∈ q
    exact Iff.of_eq (congrArg (fun I : Ideal (OriginalRingStalk A.U
      (originalImageInclusion A.U D b)) => r ∈ I)
      (q.comap_map_of_bijective lam.toRingHom lam.bijective))
  have hq := Iff.of_eq (congrArg
    (fun I : Ideal (OriginalRingStalk (originalImageOpen A.U D) b) => lam r ∈ I)
    (primeRestricted_ideal_map A D b))
  exact hz.trans ((A.kernel (originalImageInclusion A.U D b) r).trans (hm.symm.trans hq.symm))

private def primeRestricted_stalkQuotient {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (D : Opens A.U) (b : originalImageOpen A.U D) :
    ModuleCat.of (OriginalRingStalk (originalImageOpen A.U D) b)
      (OriginalRingStalk (originalImageOpen A.U D) b ⧸
        (originalGeneratorIdeal (originalImageOpen A.U D) (primeRestrictedGenerators A D) b :
          Submodule _ _)) ≅
      (nativeStalkFunctor (originalOpenStructureSheaf (originalImageOpen A.U D)) b).obj
        (primeRestrictedTarget A D) := by
  let B := originalImageOpen A.U D
  let f := originalUnitDomainStalkMap B (primeRestrictedQuotient A D) b
  let q := originalGeneratorIdeal B (primeRestrictedGenerators A D) b
  have hk : (q : Submodule (OriginalRingStalk B b) (OriginalRingStalk B b)) = LinearMap.ker f := by
    ext s
    exact (primeRestricted_kernel A D b s).symm
  letI : Epi (primeRestrictedQuotient A D) := by
    change Epi (cokernel.π (originalRestrictedCyclicRelation A.U D A.δ))
    infer_instance
  have hs : Function.Surjective f :=
    (stalkLinearMap_surjective_of_epi (originalOpenStructureSheaf B)
      (primeRestrictedQuotient A D) b).comp (unitStalkLinearEquiv (originalOpenStructureSheaf B) b).symm.surjective
  exact ((Submodule.quotEquivOfEq (q : Submodule _ _) (LinearMap.ker f) hk).trans
    (f.quotKerEquivOfSurjective hs)).toModuleIso

private theorem primeRestricted_stalkQuotient_mk {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (D : Opens A.U) (b : originalImageOpen A.U D)
    (s : OriginalRingStalk (originalImageOpen A.U D) b) :
    (primeRestricted_stalkQuotient A D b).hom (Submodule.Quotient.mk s) =
      originalUnitDomainStalkMap (originalImageOpen A.U D) (primeRestrictedQuotient A D) b s := rfl

private theorem primeRestricted_stalkQuotient_inv_numerator {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (D : Opens A.U) (b : originalImageOpen A.U D)
    (s : OriginalRingStalk (originalImageOpen A.U D) b) :
    (primeRestricted_stalkQuotient A D b).inv
      (originalUnitDomainStalkMap (originalImageOpen A.U D) (primeRestrictedQuotient A D) b s) =
      Submodule.Quotient.mk s :=
  (primeRestricted_stalkQuotient A D b).toLinearEquiv.symm_apply_eq.mpr
    (primeRestricted_stalkQuotient_mk A D b s).symm


private theorem originalModuleIso_stalk_germ (U : Opens (ComplexModel n))
    {M N : OriginalModules U} (e : M ≅ N) (u : U) (O : Opens U) (hu : u ∈ O)
    (s : M.val.obj (op O)) :
    ((nativeStalkFunctor (originalOpenStructureSheaf U) u).mapIso e).toLinearEquiv
      (TopCat.Presheaf.germ M.val.presheaf O u hu s) =
    TopCat.Presheaf.germ N.val.presheaf O u hu (e.hom.val.app (op O) s) :=
  stalkLinearMap_germ e.hom.val u O hu s

private theorem originalModuleIso_stalk_inv_germ (U : Opens (ComplexModel n))
    {M N : OriginalModules U} (e : M ≅ N) (u : U) (O : Opens U) (hu : u ∈ O)
    (s : N.val.obj (op O)) :
    ((nativeStalkFunctor (originalOpenStructureSheaf U) u).mapIso e).toLinearEquiv.symm
      (TopCat.Presheaf.germ N.val.presheaf O u hu s) =
    TopCat.Presheaf.germ M.val.presheaf O u hu (e.inv.val.app (op O) s) :=
  stalkLinearMap_germ e.inv.val u O hu s

private theorem primeReadback_germ {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (D : Opens A.U) : ∀ (b : originalImageOpen A.U D) (O : Opens A.U)
    (hu : originalImageInclusion A.U D b ∈ O) (s : A.C.val.obj (op O)),
    primeOriginalStalkReadback A D b
      (TopCat.Presheaf.germ A.C.val.presheaf O (originalImageInclusion A.U D b) hu s) =
    TopCat.Presheaf.germ (primeRestrictedTarget A D).val.presheaf
      (coefficientPreimageOpen A.U D O) b hu
      ((primeRestrictedSupportIso A D).inv.val.app (op (coefficientPreimageOpen A.U D O))
        ((canonicalSupportOpenRestrictionIso A.U D A.W).hom.val.app
          (op (coefficientPreimageOpen A.U D O))
          (A.ν0.hom.val.app
            (op ((cyclicImageFunctor A.U D).obj (coefficientPreimageOpen A.U D O)))
            (A.C.val.map (homOfLE (coefficientImagePreimage_le A.U D O)).op s)))) := by
  intro b O hu s
  let B := originalImageOpen A.U D
  let T := coefficientPreimageOpen A.U D O
  let eU := ((nativeStalkFunctor (originalOpenStructureSheaf A.U)
    (originalImageInclusion A.U D b)).mapIso A.ν0).toLinearEquiv
  let eB := ((nativeStalkFunctor (originalOpenStructureSheaf B) b).mapIso
    (primeRestrictedSupportIso A D)).toLinearEquiv
  let θ := canonicalSupportRestrictionStalkEquiv A.U D A.W b
  let v := (originalPrimeSupportModule A.U A.W).val.map
    (homOfLE (coefficientImagePreimage_le A.U D O)).op (A.ν0.hom.val.app (op O) s)
  let w := (canonicalSupportOpenRestrictionIso A.U D A.W).hom.val.app (op T) v
  have hU := originalModuleIso_stalk_germ A.U A.ν0 (originalImageInclusion A.U D b) O hu s
  have hθ := canonicalSupportRestrictionStalkEquiv_germ A.U D A.W b O hu
    (A.ν0.hom.val.app (op O) s)
  have hB := originalModuleIso_stalk_inv_germ B (primeRestrictedSupportIso A D) b T hu w
  have hn : v = A.ν0.hom.val.app (op ((cyclicImageFunctor A.U D).obj T))
      (A.C.val.map (homOfLE (coefficientImagePreimage_le A.U D O)).op s) :=
    (PresheafOfModules.naturality_apply A.ν0.hom.val
      (homOfLE (coefficientImagePreimage_le A.U D O)).op s).symm
  exact (congrArg (fun m => eB.symm (θ m)) hU).trans
    ((congrArg eB.symm hθ).trans (hB.trans
      (congrArg (fun m => TopCat.Presheaf.germ (primeRestrictedTarget A D).val.presheaf
        T b hu ((primeRestrictedSupportIso A D).inv.val.app (op T)
          ((canonicalSupportOpenRestrictionIso A.U D A.W).hom.val.app (op T) m))) hn)))

private theorem primeReadback_symm_germ {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (D : Opens A.U) : ∀ (b : originalImageOpen A.U D)
    (T : Opens (originalImageOpen A.U D)) (hb : b ∈ T)
    (t : (primeRestrictedTarget A D).val.obj (op T)),
    (primeOriginalStalkReadback A D b).symm
      (TopCat.Presheaf.germ (primeRestrictedTarget A D).val.presheaf T b hb t) =
    TopCat.Presheaf.germ A.C.val.presheaf ((cyclicImageFunctor A.U D).obj T)
      (originalImageInclusion A.U D b) ⟨b, hb, rfl⟩
      (A.ν0.inv.val.app (op ((cyclicImageFunctor A.U D).obj T))
        ((canonicalSupportOpenRestrictionIso A.U D A.W).inv.val.app (op T)
          ((primeRestrictedSupportIso A D).hom.val.app (op T) t))) := by
  intro b T hb t
  let B := originalImageOpen A.U D
  let eU := ((nativeStalkFunctor (originalOpenStructureSheaf A.U)
    (originalImageInclusion A.U D b)).mapIso A.ν0).toLinearEquiv
  let eB := ((nativeStalkFunctor (originalOpenStructureSheaf B) b).mapIso
    (primeRestrictedSupportIso A D)).toLinearEquiv
  let θ := canonicalSupportRestrictionStalkEquiv A.U D A.W b
  let v := (primeRestrictedSupportIso A D).hom.val.app (op T) t
  let w := (canonicalSupportOpenRestrictionIso A.U D A.W).inv.val.app (op T) v
  have hB := originalModuleIso_stalk_germ B (primeRestrictedSupportIso A D) b T hb t
  have hθ := canonicalSupportRestrictionStalkEquiv_symm_germ A.U D A.W b T hb v
  have hU := originalModuleIso_stalk_inv_germ A.U A.ν0 (originalImageInclusion A.U D b)
    ((cyclicImageFunctor A.U D).obj T) ⟨b, hb, rfl⟩ w
  exact (congrArg (fun m => eU.symm (θ.symm m)) hB).trans
    ((congrArg eU.symm hθ).trans hU)


/-- Every field is internally derived for the SAME previously chosen old data. -/
private def primeRestrictedData {p : ComplexModel n}
    {P : Ideal (actualComplexStructureStalk (n := n) p)}
    (A : NativePrimePresentationData p P) (D : Opens A.U) :
    NativeRestrictedPrimeCokernelData A D where
  finitePresentation := primeRestricted_finitePresentation A D
  restrictedOld_finitePresentation := primeRestricted_old_finitePresentation A D
  support_finitePresentation := primeRestricted_support_finitePresentation A D
  quotient_readback := primeRestricted_quotient_readback A D
  quotient_readback_inv := primeRestricted_quotient_readback_inv A D
  quotient_support := primeRestricted_quotient_support A D
  quotient_support_inv := primeRestricted_quotient_support_inv A D
  whole := primeRestricted_whole A D
  ideal_map := primeRestricted_ideal_map A D
  kernel := primeRestricted_kernel A D
  quotient := primeRestricted_stalkQuotient A D
  quotient_mk := primeRestricted_stalkQuotient_mk A D
  quotient_inv_numerator := primeRestricted_stalkQuotient_inv_numerator A D
  readback_smul := primeReadback_smul A D
  readback_inv_smul := primeReadback_inv_smul A D
  readback_numerator := primeReadback_numerator A D
  readback_inv_numerator := primeReadback_inv_numerator A D
  readback_germ := primeReadback_germ A D
  readback_symm_germ := primeReadback_symm_germ A D

/-- Ordinary prime P only. ONE old domain/row/target/both Isos precedes ALL smaller opens. -/
theorem exists_native_prime_support_with_all_open_cokernels
    (p : ComplexModel n) (P : Ideal (actualComplexStructureStalk (n := n) p)) [P.IsPrime] :
    Nonempty (NativePrimeAllOpenCokernelData p P) := by
  classical
  let A := chosenNativePrimePresentation p P
  exact ⟨{
    old := A
    actual_delta_span := primeActualDelta_span A
    all_opens := primeRestrictedData A }⟩

end
end Hironaka.HironakaNativeCyclicCokernelRestriction
