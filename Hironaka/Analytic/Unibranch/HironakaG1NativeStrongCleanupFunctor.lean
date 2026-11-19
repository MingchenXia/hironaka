import Hironaka.Analytic.Unibranch.HironakaG1NativeStrongCleanup
import Hironaka.Analytic.Unibranch.HironakaG1NativeSmoothCleanupLaws

/-! # Smooth arrows on the SAME chosen native strong-cleanup sources

The ordinary initial resolution and its lifted smooth diagrams remain inputs.
The actual existing strong source, projection and entire ideal are retained;
no assigned initial resolution or finite native history is inferred.
Blueprint precedes source. All frozen geometric mothers remain unchanged.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG1NativeStrongCleanupFunctor

open Hironaka Hironaka
  Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold
  HironakaSmoothSubmersionOriginalGlobalFunctor HironakaEmbeddedNativeMorphism
  HironakaNativePulledIdealSheaf HironakaNativePulledIdealComposition
  HironakaSingularModuleSheafStalk
  HironakaIntrinsicReducedCentreIdealSheaf HironakaIntrinsicComplexAnalyticRegularLocus
  SourceReducedComplexSpace OriginalNativeModification OriginalNativeSmoothLocalProduct
  OriginalNativeSmoothComposition HironakaG1NativeCleanupComponentModelIndependence


attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold

noncomputable section

variable {X Y X' Y' : SourceReducedComplexSpace}

/-- EXACTLY the already chosen strong component models; no new model engine. -/
def strongModels (p : Y ⟶ X) (hp : IsResolution p)
    (c : ConnectedComponents Y.obj.left) : ComponentModel hp.1 c where
  dimension := HironakaG1NativeStrongCleanup.componentDimension p hp c
  manifold := HironakaG1NativeStrongCleanup.componentManifold p hp c
  model := by
    let h := HironakaG1NoncompactSmoothComponentModel.exists_component_manifold_model hp.1 c
    exact Classical.choice (Classical.choose_spec (Classical.choose_spec h))

private def componentAlignment (p : Y ⟶ X) (hp : IsResolution p)
    (c : ConnectedComponents Y.obj.left) :
    HironakaG1NativeStrongCleanup.cleanupComponent p hp c ≃ₘ⟮𝓘(ℂ, ComplexModel (HironakaG1NativeStrongCleanup.componentDimension p hp c)),
      𝓘(ℂ, ComplexModel (HironakaG1NativeStrongCleanup.componentDimension p hp c))⟯
      componentTerminal p hp (strongModels p hp) c := by
  apply terminalRecordEquiv
  change (⟨univ, [], HironakaG1OriginalSingularCleanup.originalSingularGermIdeal X
    (HironakaG1NativeStrongCleanup.componentModelMap p hp c ≫ p), 1⟩ : MarkedIdeal _ _) =
      HironakaG1NativeCleanupModelIndependence.modelMarkedIdeal
        (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c ≫ p)
        (strongModels p hp c).model
  simp only [HironakaG1NativeCleanupModelIndependence.modelMarkedIdeal,
    HironakaG1NativeStrongCleanup.componentModelMap, Category.assoc]
  rfl

private theorem componentAlignment_proj (p : Y ⟶ X) (hp : IsResolution p)
    (c : ConnectedComponents Y.obj.left) (z : HironakaG1NativeStrongCleanup.cleanupComponent p hp c) :
    originalTerminalGluedProjection _ _ (componentAlignment p hp c z) =
      HironakaG1NativeStrongCleanup.cleanupComponentProjection p hp c z := by
  exact terminalRecordEquiv_proj _ _ _ _ _ z

private def nativeIso {n : ℕ} {M N : CMfd.{0} n}
    (e : M ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ N) :
    wholeModel (n := n) M ≅ wholeModel (n := n) N where
  hom := nativeMorphism e.contMDiff
  inv := nativeMorphism e.symm.contMDiff
  hom_inv_id := by
    apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
    intro z
    apply Subtype.ext
    exact e.symm_apply_apply z.val
  inv_hom_id := by
    apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
    intro z
    apply Subtype.ext
    exact e.apply_symm_apply z.val

private def oldFamily (p : Y ⟶ X) (hp : IsResolution p)
    (c : ConnectedComponents Y.obj.left) : SourceReducedComplexSpace :=
  wholeModel (n := HironakaG1NativeStrongCleanup.componentDimension p hp c) (HironakaG1NativeStrongCleanup.cleanupComponent p hp c)

private def newFamily (p : Y ⟶ X) (hp : IsResolution p)
    (c : ConnectedComponents Y.obj.left) : SourceReducedComplexSpace :=
  wholeModel (n := HironakaG1NativeStrongCleanup.componentDimension p hp c)
    (componentTerminal p hp (strongModels p hp) c)

private def componentIso (p : Y ⟶ X) (hp : IsResolution p)
    (c : ConnectedComponents Y.obj.left) : oldFamily p hp c ≅ newFamily p hp c :=
  nativeIso (componentAlignment p hp c)

/-- Actual coproduct alignment, on the literal existing strong source. -/
def alignment (p : Y ⟶ X) (hp : IsResolution p) :
    HironakaG1NativeStrongCleanup.strongSource p hp ≅ cleanupSource p hp (strongModels p hp) where
  hom := HironakaG1NativeDisjointCoproduct.desc (oldFamily p hp)
    (fun c => (componentIso p hp c).hom ≫ HironakaG1NativeDisjointCoproduct.inclusion (newFamily p hp) c)
  inv := HironakaG1NativeDisjointCoproduct.desc (newFamily p hp)
    (fun c => (componentIso p hp c).inv ≫ HironakaG1NativeDisjointCoproduct.inclusion (oldFamily p hp) c)
  hom_inv_id := by
    apply HironakaG1NativeDisjointCoproduct.hom_ext (oldFamily p hp)
    intro c
    rw [← Category.assoc, HironakaG1NativeDisjointCoproduct.inclusion_desc, Category.assoc,
      HironakaG1NativeDisjointCoproduct.inclusion_desc, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]
    exact (Category.comp_id _).symm
  inv_hom_id := by
    apply HironakaG1NativeDisjointCoproduct.hom_ext (newFamily p hp)
    intro c
    rw [← Category.assoc, HironakaG1NativeDisjointCoproduct.inclusion_desc, Category.assoc,
      HironakaG1NativeDisjointCoproduct.inclusion_desc, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
    exact (Category.comp_id _).symm

/-- Its FULL square with the existing strong projection. -/
theorem alignment_overY (p : Y ⟶ X) (hp : IsResolution p) :
    (alignment p hp).hom ≫ cleanupProjection p hp (strongModels p hp) =
      HironakaG1NativeStrongCleanup.strongRefinement p hp := by
  apply HironakaG1NativeDisjointCoproduct.hom_ext (oldFamily p hp)
  intro c
  change HironakaG1NativeDisjointCoproduct.inclusion (oldFamily p hp) c ≫
    (HironakaG1NativeDisjointCoproduct.desc (oldFamily p hp)
      (fun c => (componentIso p hp c).hom ≫ HironakaG1NativeDisjointCoproduct.inclusion (newFamily p hp) c) ≫
      cleanupProjection p hp (strongModels p hp)) = _
  rw [← Category.assoc, HironakaG1NativeDisjointCoproduct.inclusion_desc, Category.assoc]
  rw [show HironakaG1NativeDisjointCoproduct.inclusion (newFamily p hp) c ≫
      cleanupProjection p hp (strongModels p hp) = componentCleanupMap p hp (strongModels p hp) c from
    HironakaG1NativeDisjointCoproduct.inclusion_desc _ _ _]
  change (componentIso p hp c).hom ≫ componentCleanupMap p hp (strongModels p hp) c =
    HironakaG1NativeDisjointCoproduct.inclusion (oldFamily p hp) c ≫
      HironakaG1NativeDisjointCoproduct.desc (oldFamily p hp)
        (fun c => HironakaG1NativeStrongCleanup.cleanupComponentMap p hp c ≫
          HironakaG1NativeStrongCleanup.componentModelMap p hp c)
  rw [HironakaG1NativeDisjointCoproduct.inclusion_desc]
  change (componentIso p hp c).hom ≫ componentCleanupMap p hp (strongModels p hp) c =
    HironakaG1NativeStrongCleanup.cleanupComponentMap p hp c ≫ HironakaG1NativeStrongCleanup.componentModelMap p hp c
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro z
  exact congrArg (fun w : HironakaG1NativeStrongCleanup.componentManifold p hp c =>
    (HironakaG1NativeStrongCleanup.componentModelMap p hp c).hom.left.base ⟨w, mem_univ w⟩)
      (componentAlignment_proj p hp c z.val)

/-- The entire SAME original composite, including its scalar map. -/
theorem alignment_overX (p : Y ⟶ X) (hp : IsResolution p) :
    (alignment p hp).hom ≫ cleanupMorphism p hp (strongModels p hp) =
      HironakaG1NativeStrongCleanup.strongMorphism p hp := by
  change (alignment p hp).hom ≫ (cleanupProjection p hp (strongModels p hp) ≫ p) = _
  rw [← Category.assoc, alignment_overY]
  rfl

variable (p' : Y' ⟶ X') (p : Y ⟶ X) (hp' : IsResolution p') (hp : IsResolution p)
  (u : X' ⟶ X) (hu : IsSmoothMorphism u) (g : Y' ⟶ Y) (hg : IsSmoothMorphism g)
  (hdiag : p' ≫ u = g ≫ p)

/-- The HELD actual smooth cleanup arrow on the SAME chosen strong sources. -/
def strongMap : HironakaG1NativeStrongCleanup.strongSource p' hp' ⟶
    HironakaG1NativeStrongCleanup.strongSource p hp :=
  (alignment p' hp').hom ≫
    HironakaG1NativeSmoothCleanup.cleanupMap p' p hp' hp u hu g hg hdiag
      (strongModels p' hp') (strongModels p hp) ≫ (alignment p hp).inv

private theorem alignment_inv_overY (q : Y ⟶ X) (hq : IsResolution q) :
    (alignment q hq).inv ≫ HironakaG1NativeStrongCleanup.strongRefinement q hq =
      cleanupProjection q hq (strongModels q hq) := by
  rw [← alignment_overY q hq, Iso.inv_hom_id_assoc]

/-- Full original source square, with the existing strongRefinement. -/
theorem strongMap_overY :
    strongMap p' p hp' hp u hu g hg hdiag ≫ HironakaG1NativeStrongCleanup.strongRefinement p hp =
      HironakaG1NativeStrongCleanup.strongRefinement p' hp' ≫ g := by
  simp only [strongMap, Category.assoc]
  rw [alignment_inv_overY, HironakaG1NativeSmoothCleanup.cleanupMap_overY,
    ← Category.assoc, alignment_overY]

/-- Full original target square, with the existing strongMorphism. -/
theorem strongMap_overX :
    strongMap p' p hp' hp u hu g hg hdiag ≫ HironakaG1NativeStrongCleanup.strongMorphism p hp =
      HironakaG1NativeStrongCleanup.strongMorphism p' hp' ≫ u := by
  change strongMap p' p hp' hp u hu g hg hdiag ≫
    (HironakaG1NativeStrongCleanup.strongRefinement p hp ≫ p) = _
  rw [← Category.assoc, strongMap_overY, Category.assoc, ← hdiag, ← Category.assoc]
  rfl

/-- Genuine native smoothness, on the SAME full constructed arrow. -/
theorem strongMap_isSmooth : IsSmoothMorphism (strongMap p' p hp' hp u hu g hg hdiag) :=
  isSmoothMorphism_comp _ _ (HironakaG1NativeCleanupDiagramIso.nativeIso_smooth (alignment p' hp'))
    (isSmoothMorphism_comp _ _
      (HironakaG1NativeSmoothCleanup.cleanupMap_isSmooth p' p hp' hp u hu g hg hdiag _ _)
      (HironakaG1NativeCleanupDiagramIso.nativeIso_smooth (alignment p hp).symm))

/-- Exact inverse ORIGINAL Reg under that SAME full native arrow. -/
theorem strongMap_regularPreimage :
    (strongMap p' p hp' hp u hu g hg hdiag).hom.left.base ⁻¹'
        ((HironakaG1NativeStrongCleanup.strongMorphism p hp).hom.left.base ⁻¹' intrinsicRegularLocus X.obj) =
      (HironakaG1NativeStrongCleanup.strongMorphism p' hp').hom.left.base ⁻¹' intrinsicRegularLocus X'.obj := by
  ext z
  have hz := congrArg (fun f : HironakaG1NativeStrongCleanup.strongSource p' hp' ⟶ X => f.hom.left.base z)
    (strongMap_overX p' p hp' hp u hu g hg hdiag)
  change (HironakaG1NativeStrongCleanup.strongMorphism p hp).hom.left.base
    ((strongMap p' p hp' hp u hu g hg hdiag).hom.left.base z) =
      u.hom.left.base ((HironakaG1NativeStrongCleanup.strongMorphism p' hp').hom.left.base z) at hz
  change (HironakaG1NativeStrongCleanup.strongMorphism p hp).hom.left.base
    ((strongMap p' p hp' hp u hu g hg hdiag).hom.left.base z) ∈ intrinsicRegularLocus X.obj ↔ _
  rw [hz]
  exact Set.ext_iff.mp (OriginalNativeSmoothSingularLocus.preimage_intrinsicRegularLocus u hu) _

include hu hdiag in
/-- HELD ANY-lift uniqueness transferred through the actual alignments. -/
theorem strongLift_eq
    (f k : HironakaG1NativeStrongCleanup.strongSource p' hp' ⟶ HironakaG1NativeStrongCleanup.strongSource p hp)
    (hf : f ≫ HironakaG1NativeStrongCleanup.strongRefinement p hp =
      HironakaG1NativeStrongCleanup.strongRefinement p' hp' ≫ g)
    (hk : k ≫ HironakaG1NativeStrongCleanup.strongRefinement p hp =
      HironakaG1NativeStrongCleanup.strongRefinement p' hp' ≫ g) : f = k := by
  have hc (F : HironakaG1NativeStrongCleanup.strongSource p' hp' ⟶ HironakaG1NativeStrongCleanup.strongSource p hp)
      (hF : F ≫ HironakaG1NativeStrongCleanup.strongRefinement p hp =
        HironakaG1NativeStrongCleanup.strongRefinement p' hp' ≫ g) :
      ((alignment p' hp').inv ≫ F ≫ (alignment p hp).hom) ≫ cleanupProjection p hp (strongModels p hp) =
        cleanupProjection p' hp' (strongModels p' hp') ≫ g := by
    simp only [Category.assoc]
    rw [alignment_overY, hF, ← Category.assoc, alignment_inv_overY]
  have he := HironakaG1NativeSmoothCleanupLaws.lift_eq p' p hp' hp u hu g hdiag
    (strongModels p' hp') (strongModels p hp)
    ((alignment p' hp').inv ≫ f ≫ (alignment p hp).hom)
    ((alignment p' hp').inv ≫ k ≫ (alignment p hp).hom) (hc f hf) (hc k hk)
  apply (cancel_epi (alignment p' hp').inv).mp
  apply (cancel_mono (alignment p hp).hom).mp
  simpa only [Category.assoc] using he

/-- Exact identity on the literal original strong source. -/
theorem strongMap_identity (q : Y ⟶ X) (hq : IsResolution q) :
    strongMap q q hq hq (𝟙 X) (isSmoothMorphism_identity X)
        (𝟙 Y) (isSmoothMorphism_identity Y) (by simp) =
      𝟙 (HironakaG1NativeStrongCleanup.strongSource q hq) := by
  apply strongLift_eq q q hq hq (𝟙 X) (isSmoothMorphism_identity X) (𝟙 Y) (by simp)
  · exact strongMap_overY _ _ _ _ _ _ _ _ _
  · simp

/-- Actual composition/cocycle on SAME strong sources of three ordinary diagrams. -/
theorem strongMap_composition
    {X₀ X₁ X₂ Y₀ Y₁ Y₂ : SourceReducedComplexSpace}
    (p₀ : Y₀ ⟶ X₀) (p₁ : Y₁ ⟶ X₁) (p₂ : Y₂ ⟶ X₂)
    (hp₀ : IsResolution p₀) (hp₁ : IsResolution p₁) (hp₂ : IsResolution p₂)
    (u₀₁ : X₀ ⟶ X₁) (hu₀₁ : IsSmoothMorphism u₀₁) (g₀₁ : Y₀ ⟶ Y₁) (hg₀₁ : IsSmoothMorphism g₀₁)
    (u₁₂ : X₁ ⟶ X₂) (hu₁₂ : IsSmoothMorphism u₁₂) (g₁₂ : Y₁ ⟶ Y₂) (hg₁₂ : IsSmoothMorphism g₁₂)
    (h₀₁ : p₀ ≫ u₀₁ = g₀₁ ≫ p₁) (h₁₂ : p₁ ≫ u₁₂ = g₁₂ ≫ p₂) :
    strongMap p₀ p₁ hp₀ hp₁ u₀₁ hu₀₁ g₀₁ hg₀₁ h₀₁ ≫
        strongMap p₁ p₂ hp₁ hp₂ u₁₂ hu₁₂ g₁₂ hg₁₂ h₁₂ =
      strongMap p₀ p₂ hp₀ hp₂ (u₀₁ ≫ u₁₂) (isSmoothMorphism_comp _ _ hu₀₁ hu₁₂)
        (g₀₁ ≫ g₁₂) (isSmoothMorphism_comp _ _ hg₀₁ hg₁₂)
        (HironakaG1NativeSmoothCleanupLaws.composite_diagram_square p₀ p₁ p₂ u₀₁ g₀₁ u₁₂ g₁₂ h₀₁ h₁₂) := by
  apply strongLift_eq p₀ p₂ hp₀ hp₂ (u₀₁ ≫ u₁₂) (isSmoothMorphism_comp _ _ hu₀₁ hu₁₂)
    (g₀₁ ≫ g₁₂) (HironakaG1NativeSmoothCleanupLaws.composite_diagram_square p₀ p₁ p₂ u₀₁ g₀₁ u₁₂ g₁₂ h₀₁ h₁₂)
  · rw [Category.assoc, strongMap_overY, ← Category.assoc, strongMap_overY, Category.assoc]
  · exact strongMap_overY _ _ _ _ _ _ _ _ _

/-- ENTIRE original-Sing pullback on the literal old strong morphism. -/
def totalIdealModule (q : Y ⟶ X) (hq : IsResolution q) :
    SheafOfModules.{0} (forgetRing (HironakaG1NativeStrongCleanup.strongSource q hq).obj.left.toSheafedSpace.sheaf) :=
  nativePulledIdealModule (HironakaG1NativeStrongCleanup.strongMorphism q hq).hom.left
    (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
    (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj))

/-- Its literal original structure-unit inclusion. -/
def totalIdealInclusion (q : Y ⟶ X) (hq : IsResolution q) :
    totalIdealModule q hq ⟶
      SheafOfModules.unit (forgetRing (HironakaG1NativeStrongCleanup.strongSource q hq).obj.left.toSheafedSpace.sheaf) :=
  nativePulledIdealInclusion (HironakaG1NativeStrongCleanup.strongMorphism q hq).hom.left
    (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
    (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj))

private theorem pulledSubmodule_eq {Z Z' : SourceReducedComplexSpace}
    (r : Z ⟶ X) (r' : Z' ⟶ X') (v : X' ⟶ X) (hv : IsSmoothMorphism v)
    (F : Z' ⟶ Z) (hF : F ≫ r = r' ≫ v) :
    nativePulledIdealSubmodule F.hom.left
      (nativePulledIdealModule r.hom.left
        (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
        (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj)))
      (nativePulledIdealInclusion r.hom.left
        (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
        (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj))) =
    nativePulledIdealSubmodule r'.hom.left
      (intrinsicReducedCentreIdealModule X'.obj.left (intrinsicSingularLocus X'.obj))
      (intrinsicReducedCentreIdealInclusion X'.obj.left (intrinsicSingularLocus X'.obj)) := by
  have hs : F.hom.left ≫ r.hom.left = r'.hom.left ≫ v.hom.left :=
    congrArg (fun f : Z' ⟶ X => f.hom.left) hF
  rw [submodule_comp, hs]
  apply PresheafOfModules.Submodule.ext
  intro U
  ext t
  constructor
  · intro ht z hz
    rw [← HironakaG1NativeSmoothCleanupCore.smoothBase_stalkIdeal_eq v hv r'.hom.left z]
    exact ht z hz
  · intro ht z hz
    rw [HironakaG1NativeSmoothCleanupCore.smoothBase_stalkIdeal_eq v hv r'.hom.left z]
    exact ht z hz

private def pulledIdealIso {Z Z' : SourceReducedComplexSpace}
    (r : Z ⟶ X) (r' : Z' ⟶ X') (v : X' ⟶ X) (hv : IsSmoothMorphism v)
    (F : Z' ⟶ Z) (hF : F ≫ r = r' ≫ v) :
    nativePulledIdealModule F.hom.left
      (nativePulledIdealModule r.hom.left
        (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
        (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj)))
      (nativePulledIdealInclusion r.hom.left
        (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
        (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj))) ≅
    nativePulledIdealModule r'.hom.left
      (intrinsicReducedCentreIdealModule X'.obj.left (intrinsicSingularLocus X'.obj))
      (intrinsicReducedCentreIdealInclusion X'.obj.left (intrinsicSingularLocus X'.obj)) where
  hom := ⟨PresheafOfModules.Submodule.homOfLE (pulledSubmodule_eq r r' v hv F hF).le⟩
  inv := ⟨PresheafOfModules.Submodule.homOfLE (pulledSubmodule_eq r r' v hv F hF).ge⟩
  hom_inv_id := by ext U t; rfl
  inv_hom_id := by ext U t; rfl

/-- Alignment transports the ENTIRE ideal with the original scalar map. -/
def alignmentIdealIso (q : Y ⟶ X) (hq : IsResolution q) :
    nativePulledIdealModule (alignment q hq).hom.hom.left
      (HironakaG1NativeCleanupComponentModelIndependence.totalIdealModule q hq (strongModels q hq))
      (HironakaG1NativeCleanupComponentModelIndependence.totalIdealInclusion q hq (strongModels q hq)) ≅
      totalIdealModule q hq :=
  pulledIdealIso (cleanupMorphism q hq (strongModels q hq))
    (HironakaG1NativeStrongCleanup.strongMorphism q hq) (𝟙 X) (isSmoothMorphism_identity X)
    (alignment q hq).hom (by simpa using alignment_overX q hq)

/-- Forward alignment triangle with the literal original unit inclusion. -/
theorem alignmentIdealIso_hom_comp_inclusion (q : Y ⟶ X) (hq : IsResolution q) :
    (alignmentIdealIso q hq).hom ≫ totalIdealInclusion q hq =
      nativePulledIdealInclusion (alignment q hq).hom.hom.left
        (HironakaG1NativeCleanupComponentModelIndependence.totalIdealModule q hq (strongModels q hq))
        (HironakaG1NativeCleanupComponentModelIndependence.totalIdealInclusion q hq (strongModels q hq)) := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι (pulledSubmodule_eq
    (cleanupMorphism q hq (strongModels q hq)) (HironakaG1NativeStrongCleanup.strongMorphism q hq)
    (𝟙 X) (isSmoothMorphism_identity X) (alignment q hq).hom (by simpa using alignment_overX q hq)).le

/-- Inverse alignment triangle with that SAME original inclusion. -/
theorem alignmentIdealIso_inv_comp_inclusion (q : Y ⟶ X) (hq : IsResolution q) :
    (alignmentIdealIso q hq).inv ≫ nativePulledIdealInclusion (alignment q hq).hom.hom.left
        (HironakaG1NativeCleanupComponentModelIndependence.totalIdealModule q hq (strongModels q hq))
        (HironakaG1NativeCleanupComponentModelIndependence.totalIdealInclusion q hq (strongModels q hq)) =
      totalIdealInclusion q hq := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι (pulledSubmodule_eq
    (cleanupMorphism q hq (strongModels q hq)) (HironakaG1NativeStrongCleanup.strongMorphism q hq)
    (𝟙 X) (isSmoothMorphism_identity X) (alignment q hq).hom (by simpa using alignment_overX q hq)).ge

/-- The ENTIRE original-Sing totalideal along the SAME actual strong arrow. -/
def strongMapIdealIso :
    nativePulledIdealModule (strongMap p' p hp' hp u hu g hg hdiag).hom.left
      (totalIdealModule p hp) (totalIdealInclusion p hp) ≅ totalIdealModule p' hp' :=
  pulledIdealIso (HironakaG1NativeStrongCleanup.strongMorphism p hp)
    (HironakaG1NativeStrongCleanup.strongMorphism p' hp') u hu
    (strongMap p' p hp' hp u hu g hg hdiag) (strongMap_overX p' p hp' hp u hu g hg hdiag)

/-- Forward strong-map triangle with the literal original unit inclusion. -/
theorem strongMapIdealIso_hom_comp_inclusion :
    (strongMapIdealIso p' p hp' hp u hu g hg hdiag).hom ≫ totalIdealInclusion p' hp' =
      nativePulledIdealInclusion (strongMap p' p hp' hp u hu g hg hdiag).hom.left
        (totalIdealModule p hp) (totalIdealInclusion p hp) := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι (pulledSubmodule_eq
    (HironakaG1NativeStrongCleanup.strongMorphism p hp) (HironakaG1NativeStrongCleanup.strongMorphism p' hp')
    u hu (strongMap p' p hp' hp u hu g hg hdiag) (strongMap_overX p' p hp' hp u hu g hg hdiag)).le

/-- Inverse strong-map triangle, preserving the SAME full original scalars. -/
theorem strongMapIdealIso_inv_comp_inclusion :
    (strongMapIdealIso p' p hp' hp u hu g hg hdiag).inv ≫
        nativePulledIdealInclusion (strongMap p' p hp' hp u hu g hg hdiag).hom.left
          (totalIdealModule p hp) (totalIdealInclusion p hp) = totalIdealInclusion p' hp' := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι (pulledSubmodule_eq
    (HironakaG1NativeStrongCleanup.strongMorphism p hp) (HironakaG1NativeStrongCleanup.strongMorphism p' hp')
    u hu (strongMap p' p hp' hp u hu g hg hdiag) (strongMap_overX p' p hp' hp u hu g hg hdiag)).ge

end
end Hironaka.Analytic.Unibranch.HironakaG1NativeStrongCleanupFunctor
