import Hironaka.Analytic.Unibranch.HironakaG1NativeSmoothComponentMap
import Hironaka.Analytic.Unibranch.OriginalNativeSmoothAmbientConverse

/-! # Actual cleanup on ordinary native smooth resolution diagrams

The EXISTING cleanup sources are retained. Component assignment, actual
manifold submersions, whole-record alignment and every native terminal
arrow are internally constructed. No component-to-all-X resolution or
ideal/history/terminal correctness packet is an input. Blueprint first.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG1NativeSmoothCleanup

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal HironakaActualAnalyticSubspace
  HironakaEmbeddedNativeMorphism HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold
  HironakaSmoothSubmersionOriginalGlobalFunctor HironakaSmoothSubmersionOriginalTerminalSubmersion
  HironakaSmoothSubmersionComposition HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaIntrinsicReducedCentreIdealSheaf HironakaNativePulledIdealSheaf
  HironakaNativePulledIdealComposition HironakaSingularModuleSheafStalk
  SourceReducedComplexSpace OriginalNativeModification OriginalIntrinsicSingularLocus
  OriginalNativeSmoothLocalProduct OriginalNativeSmoothComposition
  HironakaG1NativeCleanupModelIndependence HironakaG1NativeCleanupComponentModelIndependence
  HironakaG1NativeSmoothComponentMap

attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold

noncomputable section

variable {X X' Y Y' : SourceReducedComplexSpace}

/-- The actual FULL original map from a genuine component manifold model. -/
def originalModelMap (p : Y ⟶ X) (hp : IsResolution p)
    (A : ∀ c, ComponentModel hp.1 c) (c : ConnectedComponents Y.obj.left) :
    wholeModel (n := (A c).dimension) (A c).manifold ⟶ X :=
  (A c).model.hom ≫ (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c ≫ p)

/-- Ordinary original resolution data derive thinness on this ACTUAL model. -/
theorem originalModelMap_thin (p : Y ⟶ X) (hp : IsResolution p)
    (A : ∀ c, ComponentModel hp.1 c) (c : ConnectedComponents Y.obj.left) :
    interior ((originalModelMap p hp A c).hom.left.base ⁻¹' intrinsicSingularLocus X.obj) = ∅ := by
  change interior ((isoHomeomorph (A c).model) ⁻¹'
    ((HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c ≫ p).hom.left.base ⁻¹'
      intrinsicSingularLocus X.obj)) = ∅
  rw [← (isoHomeomorph (A c).model).preimage_interior, componentThin p hp c, preimage_empty]

private theorem componentRecord_eq_core (p : Y ⟶ X) (hp : IsResolution p)
    (A : ∀ c, ComponentModel hp.1 c) (c : ConnectedComponents Y.obj.left) :
    modelMarkedIdeal (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c ≫ p)
        (A c).model = modelMarkedIdeal (originalModelMap p hp A c) (Iso.refl _) := by
  simp only [modelMarkedIdeal, originalModelMap, Iso.refl_hom, Category.id_comp]

/-- The whole record identity DERIVES the actual terminal alignment. -/
def componentRecordEquiv (p : Y ⟶ X) (hp : IsResolution p)
    (A : ∀ c, ComponentModel hp.1 c) (c : ConnectedComponents Y.obj.left)
    (ht : interior ((originalModelMap p hp A c).hom.left.base ⁻¹' intrinsicSingularLocus X.obj) = ∅) :
    componentTerminal p hp A c ≃ₘ⟮𝓘(ℂ, ComplexModel (A c).dimension),
      𝓘(ℂ, ComplexModel (A c).dimension)⟯ modelTerminal (originalModelMap p hp A c) ht (Iso.refl _) :=
  terminalRecordEquiv _ _ _ _ (componentRecord_eq_core p hp A c)

/-- The SAME actual original projection is retained by whole-record alignment. -/
theorem componentRecordEquiv_proj (p : Y ⟶ X) (hp : IsResolution p)
    (A : ∀ c, ComponentModel hp.1 c) (c : ConnectedComponents Y.obj.left)
    (ht : interior ((originalModelMap p hp A c).hom.left.base ⁻¹' intrinsicSingularLocus X.obj) = ∅)
    (z : componentTerminal p hp A c) :
    originalTerminalGluedProjection (modelMarkedIdeal (originalModelMap p hp A c) (Iso.refl _))
        (modelMarkedDomain (originalModelMap p hp A c) ht (Iso.refl _)) (componentRecordEquiv p hp A c ht z) =
      originalTerminalGluedProjection
        (modelMarkedIdeal (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c ≫ p) (A c).model)
        (modelMarkedDomain _ (componentThin p hp c) (A c).model) z :=
  terminalRecordEquiv_proj _ _ _ _ (componentRecord_eq_core p hp A c) z

private theorem componentRecordEquiv_symm_proj (p : Y ⟶ X) (hp : IsResolution p)
    (A : ∀ c, ComponentModel hp.1 c) (c : ConnectedComponents Y.obj.left)
    (ht : interior ((originalModelMap p hp A c).hom.left.base ⁻¹' intrinsicSingularLocus X.obj) = ∅)
    (z : modelTerminal (originalModelMap p hp A c) ht (Iso.refl _)) :
    originalTerminalGluedProjection
        (modelMarkedIdeal (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c ≫ p) (A c).model)
        (modelMarkedDomain _ (componentThin p hp c) (A c).model) ((componentRecordEquiv p hp A c ht).symm z) =
      originalTerminalGluedProjection (modelMarkedIdeal (originalModelMap p hp A c) (Iso.refl _))
        (modelMarkedDomain (originalModelMap p hp A c) ht (Iso.refl _)) z := by
  have H := componentRecordEquiv_proj p hp A c ht ((componentRecordEquiv p hp A c ht).symm z)
  rw [(componentRecordEquiv p hp A c ht).apply_symm_apply] at H
  exact H.symm

variable (p' : Y' ⟶ X') (p : Y ⟶ X) (hp' : IsResolution p') (hp : IsResolution p)
  (u : X' ⟶ X) (hu : IsSmoothMorphism u) (g : Y' ⟶ Y) (hg : IsSmoothMorphism g)
  (hdiag : p' ≫ u = g ≫ p)
  (A' : ∀ c, ComponentModel hp'.1 c) (A : ∀ c, ComponentModel hp.1 c)

include p' p hp' hp u hu g hg hdiag A' A

omit hu in
/-- The FULL actual original square for the INTERNALLY derived model submersion. -/
theorem component_original_square (c : ConnectedComponents Y'.obj.left) :
    nativeMorphism (modelPointMap_isSubmersion hp'.1 hp.1 g hg A' A c).contMDiff ≫
        originalModelMap p hp A (componentIndex g c) = originalModelMap p' hp' A' c ≫ u := by
  rw [nativeMorphism_modelPointMap hp'.1 hp.1 g hg A' A c]
  change modelMap hp'.1 hp.1 g A' A c ≫
    (((A (componentIndex g c)).model.hom ≫
      HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 (componentIndex g c)) ≫ p) =
    (((A' c).model.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hp'.1 c) ≫ p') ≫ u
  rw [← Category.assoc, modelMap_square, Category.assoc, ← hdiag, ← Category.assoc]

private theorem sourceModelThin (c : ConnectedComponents Y'.obj.left) :
    interior ((originalModelMap p' hp' A' c).hom.left.base ⁻¹' intrinsicSingularLocus X'.obj) = ∅ :=
  HironakaG1NativeSmoothCleanupCore.sourceThin u hu
    (modelPointMap hp'.1 hp.1 g A' A c) (modelPointMap_isSubmersion hp'.1 hp.1 g hg A' A c)
    (originalModelMap p' hp' A' c) (originalModelMap p hp A (componentIndex g c))
    (component_original_square p' p hp' hp u g hg hdiag A' A c)
    (originalModelMap_thin p hp A (componentIndex g c))

private def coreMap (c : ConnectedComponents Y'.obj.left) :=
  HironakaG1NativeSmoothCleanupCore.terminalMap u hu
    (modelPointMap hp'.1 hp.1 g A' A c) (modelPointMap_isSubmersion hp'.1 hp.1 g hg A' A c)
    (originalModelMap p' hp' A' c) (originalModelMap p hp A (componentIndex g c))
    (component_original_square p' p hp' hp u g hg hdiag A' A c)
    (originalModelMap_thin p hp A (componentIndex g c))

private theorem coreMap_isSubmersion (c : ConnectedComponents Y'.obj.left) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (A' c).dimension)
      𝓘(ℂ, ComplexModel (A (componentIndex g c)).dimension) ∞ (coreMap p' p hp' hp u hu g hg hdiag A' A c) :=
  HironakaG1NativeSmoothCleanupCore.terminalMap_isSubmersion u hu _ _ _ _ _ _

private theorem coreMap_proj (c : ConnectedComponents Y'.obj.left)
    (z : modelTerminal (originalModelMap p' hp' A' c)
      (sourceModelThin p' p hp' hp u hu g hg hdiag A' A c) (Iso.refl _)) :
    originalTerminalGluedProjection
        (modelMarkedIdeal (originalModelMap p hp A (componentIndex g c)) (Iso.refl _))
        (modelMarkedDomain _ (originalModelMap_thin p hp A (componentIndex g c)) (Iso.refl _))
        (coreMap p' p hp' hp u hu g hg hdiag A' A c z) =
      modelPointMap hp'.1 hp.1 g A' A c
        (originalTerminalGluedProjection (modelMarkedIdeal (originalModelMap p' hp' A' c) (Iso.refl _))
          (modelMarkedDomain _ (sourceModelThin p' p hp' hp u hu g hg hdiag A' A c) (Iso.refl _)) z) :=
  HironakaG1NativeSmoothCleanupCore.terminalMap_proj u hu _ _ _ _ _ _ z

/-- Actual terminal arrow on the EXISTING component cleanup sources. -/
def componentTerminalMap (c : ConnectedComponents Y'.obj.left) :
    componentTerminal p' hp' A' c → componentTerminal p hp A (componentIndex g c) :=
  (componentRecordEquiv p hp A (componentIndex g c) (originalModelMap_thin p hp A (componentIndex g c))).symm ∘
    coreMap p' p hp' hp u hu g hg hdiag A' A c ∘
      componentRecordEquiv p' hp' A' c (sourceModelThin p' p hp' hp u hu g hg hdiag A' A c)

/-- Genuine submersion, derived through the actual whole-record biholomorphisms. -/
theorem componentTerminalMap_isSubmersion (c : ConnectedComponents Y'.obj.left) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (A' c).dimension)
      𝓘(ℂ, ComplexModel (A (componentIndex g c)).dimension) ∞
      (componentTerminalMap p' p hp' hp u hu g hg hdiag A' A c) :=
  isSubmersion_composition
    (isSubmersion_precompose_biholomorphism
      (Manifold.IsSubmersion.id (I := 𝓘(ℂ, ComplexModel (A (componentIndex g c)).dimension))
        (M := componentTerminal p hp A (componentIndex g c)))
      (componentRecordEquiv p hp A (componentIndex g c)
        (originalModelMap_thin p hp A (componentIndex g c))).symm)
    (isSubmersion_precompose_biholomorphism (coreMap_isSubmersion p' p hp' hp u hu g hg hdiag A' A c)
      (componentRecordEquiv p' hp' A' c (sourceModelThin p' p hp' hp u hu g hg hdiag A' A c)))

/-- The actual original component projection formula. -/
theorem componentTerminalMap_proj (c : ConnectedComponents Y'.obj.left) (z : componentTerminal p' hp' A' c) :
    originalTerminalGluedProjection
        (modelMarkedIdeal (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 (componentIndex g c) ≫ p)
          (A (componentIndex g c)).model)
        (modelMarkedDomain _ (componentThin p hp (componentIndex g c)) (A (componentIndex g c)).model)
        (componentTerminalMap p' p hp' hp u hu g hg hdiag A' A c z) =
      modelPointMap hp'.1 hp.1 g A' A c
        (originalTerminalGluedProjection
          (modelMarkedIdeal (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp'.1 c ≫ p') (A' c).model)
          (modelMarkedDomain _ (componentThin p' hp' c) (A' c).model) z) := by
  unfold componentTerminalMap
  rw [Function.comp_apply, Function.comp_apply, componentRecordEquiv_symm_proj,
    coreMap_proj, componentRecordEquiv_proj]

/-- The SAME entire native component terminal map. -/
def componentNativeMap (c : ConnectedComponents Y'.obj.left) :
    wholeModel (n := (A' c).dimension) (componentTerminal p' hp' A' c) ⟶
      wholeModel (n := (A (componentIndex g c)).dimension) (componentTerminal p hp A (componentIndex g c)) :=
  nativeMorphism (componentTerminalMap_isSubmersion p' p hp' hp u hu g hg hdiag A' A c).contMDiff

/-- The SAME full native component cleanup square over the original g. -/
theorem componentNativeMap_square (c : ConnectedComponents Y'.obj.left) :
    componentNativeMap p' p hp' hp u hu g hg hdiag A' A c ≫
        componentCleanupMap p hp A (componentIndex g c) = componentCleanupMap p' hp' A' c ≫ g := by
  let q' := nativeMorphism (originalTerminalGluedProjection_contMDiff
    (modelMarkedIdeal (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp'.1 c ≫ p') (A' c).model)
    (modelMarkedDomain _ (componentThin p' hp' c) (A' c).model))
  let q := nativeMorphism (originalTerminalGluedProjection_contMDiff
    (modelMarkedIdeal (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 (componentIndex g c) ≫ p)
      (A (componentIndex g c)).model)
    (modelMarkedDomain _ (componentThin p hp (componentIndex g c)) (A (componentIndex g c)).model))
  have hmodel : componentNativeMap p' p hp' hp u hu g hg hdiag A' A c ≫ q =
      q' ≫ nativeMorphism (modelPointMap_isSubmersion hp'.1 hp.1 g hg A' A c).contMDiff := by
    apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
    intro z
    apply Subtype.ext
    exact componentTerminalMap_proj p' p hp' hp u hu g hg hdiag A' A c z.val
  have hYmodel : nativeMorphism (modelPointMap_isSubmersion hp'.1 hp.1 g hg A' A c).contMDiff ≫
      ((A (componentIndex g c)).model.hom ≫
        HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 (componentIndex g c)) =
      ((A' c).model.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hp'.1 c) ≫ g := by
    rw [nativeMorphism_modelPointMap hp'.1 hp.1 g hg A' A c]
    exact modelMap_square hp'.1 hp.1 g A' A c
  change componentNativeMap p' p hp' hp u hu g hg hdiag A' A c ≫
      ((q ≫ (A (componentIndex g c)).model.hom) ≫
        HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 (componentIndex g c)) =
    ((q' ≫ (A' c).model.hom) ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hp'.1 c) ≫ g
  simp only [Category.assoc]
  rw [← Category.assoc _ q _, hmodel, Category.assoc, hYmodel]
  simp only [Category.assoc]

/-- Actual ambient submersion on WHOLE models gives native smoothness of THAT map. -/
theorem componentNativeMap_isSmooth (c : ConnectedComponents Y'.obj.left) :
    IsSmoothMorphism (componentNativeMap p' p hp' hp u hu g hg hdiag A' A c) := by
  have H := OriginalNativeSmoothAmbientConverse.isSmoothMorphism_subspaceMorphism
    (componentTerminalMap_isSubmersion p' p hp' hp u hu g hg hdiag A' A c)
    (isComplexAnalyticSubset_univ (n := (A' c).dimension))
    (isComplexAnalyticSubset_univ (n := (A (componentIndex g c)).dimension))
    (by ext z; simp)
  exact H

private def sourceFamily (c : ConnectedComponents Y'.obj.left) : SourceReducedComplexSpace :=
  wholeModel (n := (A' c).dimension) (componentTerminal p' hp' A' c)

private def targetFamily (c : ConnectedComponents Y.obj.left) : SourceReducedComplexSpace :=
  wholeModel (n := (A c).dimension) (componentTerminal p hp A c)

omit p' p hp' hp u hu g hg hdiag A' A in
private theorem desc_square {ι κ : Type} {Z : ι → SourceReducedComplexSpace}
    {W : κ → SourceReducedComplexSpace} (s : ι → κ) (F : ∀ i, Z i ⟶ W (s i))
    (Q' : ∀ i, Z i ⟶ Y') (Q : ∀ j, W j ⟶ Y) (v : Y' ⟶ Y)
    (hF : ∀ i, F i ≫ Q (s i) = Q' i ≫ v) :
    HironakaG1NativeDisjointCoproduct.desc Z
        (fun i => F i ≫ HironakaG1NativeDisjointCoproduct.inclusion W (s i)) ≫
        HironakaG1NativeDisjointCoproduct.desc W Q =
      HironakaG1NativeDisjointCoproduct.desc Z Q' ≫ v := by
  apply HironakaG1NativeDisjointCoproduct.hom_ext
  intro i
  rw [← Category.assoc, HironakaG1NativeDisjointCoproduct.inclusion_desc, Category.assoc,
    HironakaG1NativeDisjointCoproduct.inclusion_desc, ← Category.assoc,
    HironakaG1NativeDisjointCoproduct.inclusion_desc]
  exact hF i

/-- The actual native smooth cleanup arrow on the SAME existing coproduct sources. -/
def cleanupMap : cleanupSource p' hp' A' ⟶ cleanupSource p hp A :=
  HironakaG1NativeDisjointCoproduct.desc (sourceFamily p' hp' A')
    (fun c => componentNativeMap p' p hp' hp u hu g hg hdiag A' A c ≫
      HironakaG1NativeDisjointCoproduct.inclusion (targetFamily p hp A) (componentIndex g c))

private theorem cleanupMap_inclusion (c : ConnectedComponents Y'.obj.left) :
    HironakaG1NativeDisjointCoproduct.inclusion (sourceFamily p' hp' A') c ≫
        cleanupMap p' p hp' hp u hu g hg hdiag A' A =
      componentNativeMap p' p hp' hp u hu g hg hdiag A' A c ≫
        HironakaG1NativeDisjointCoproduct.inclusion (targetFamily p hp A) (componentIndex g c) :=
  HironakaG1NativeDisjointCoproduct.inclusion_desc _ _ c

/-- FULL original native square over the ACTUAL smooth source arrow g. -/
theorem cleanupMap_overY :
    cleanupMap p' p hp' hp u hu g hg hdiag A' A ≫ cleanupProjection p hp A =
      cleanupProjection p' hp' A' ≫ g :=
  desc_square (Z := sourceFamily p' hp' A') (W := targetFamily p hp A) (componentIndex g)
    (componentNativeMap p' p hp' hp u hu g hg hdiag A' A)
    (componentCleanupMap p' hp' A') (componentCleanupMap p hp A) g
    (componentNativeMap_square p' p hp' hp u hu g hg hdiag A' A)

/-- FULL original native square over the ACTUAL smooth base arrow u. -/
theorem cleanupMap_overX :
    cleanupMap p' p hp' hp u hu g hg hdiag A' A ≫ cleanupMorphism p hp A =
      cleanupMorphism p' hp' A' ≫ u := by
  change cleanupMap p' p hp' hp u hu g hg hdiag A' A ≫ (cleanupProjection p hp A ≫ p) =
    (cleanupProjection p' hp' A' ≫ p') ≫ u
  rw [← Category.assoc, cleanupMap_overY, Category.assoc, ← hdiag, ← Category.assoc]

/-- Native smoothness is derived on the ACTUAL covering original source OIs. -/
theorem cleanupMap_isSmooth : IsSmoothMorphism (cleanupMap p' p hp' hp u hu g hg hdiag A' A) := by
  intro z
  obtain ⟨c, w, rfl⟩ := HironakaG1NativeDisjointCoproduct.inclusion_jointly_surjective (sourceFamily p' hp' A') z
  have hsm : IsSmoothMorphism
      (HironakaG1NativeDisjointCoproduct.inclusion (sourceFamily p' hp' A') c ≫
        cleanupMap p' p hp' hp u hu g hg hdiag A' A) := by
    rw [cleanupMap_inclusion]
    exact isSmoothMorphism_comp _ _ (componentNativeMap_isSmooth p' p hp' hp u hu g hg hdiag A' A c)
      (isSmoothMorphism_of_isOpenImmersion _
        (HironakaG1NativeDisjointCoproduct.inclusion_isOpenImmersion (targetFamily p hp A) (componentIndex g c)))
  exact isSmoothAt_of_precomp_openImmersion _ _
    (HironakaG1NativeDisjointCoproduct.inclusion_isOpenImmersion (sourceFamily p' hp' A') c) w (hsm w)

/-- Exact inverse ORIGINAL regular loci of the SAME actual native arrow. -/
theorem cleanupMap_regularPreimage :
    (cleanupMap p' p hp' hp u hu g hg hdiag A' A).hom.left.base ⁻¹'
        ((cleanupMorphism p hp A).hom.left.base ⁻¹' intrinsicRegularLocus X.obj) =
      (cleanupMorphism p' hp' A').hom.left.base ⁻¹' intrinsicRegularLocus X'.obj := by
  ext z
  have hz := congrArg (fun f : cleanupSource p' hp' A' ⟶ X => f.hom.left.base z)
    (cleanupMap_overX p' p hp' hp u hu g hg hdiag A' A)
  change (cleanupMorphism p hp A).hom.left.base ((cleanupMap p' p hp' hp u hu g hg hdiag A' A).hom.left.base z) =
    u.hom.left.base ((cleanupMorphism p' hp' A').hom.left.base z) at hz
  change (cleanupMorphism p hp A).hom.left.base ((cleanupMap p' p hp' hp u hu g hg hdiag A' A).hom.left.base z)
    ∈ intrinsicRegularLocus X.obj ↔ _
  rw [hz]
  exact Set.ext_iff.mp (OriginalNativeSmoothSingularLocus.preimage_intrinsicRegularLocus u hu) _

private theorem totalIdealSubmodule_eq :
    nativePulledIdealSubmodule (cleanupMap p' p hp' hp u hu g hg hdiag A' A).hom.left
        (totalIdealModule p hp A) (totalIdealInclusion p hp A) =
      nativePulledIdealSubmodule (cleanupMorphism p' hp' A').hom.left
        (intrinsicReducedCentreIdealModule X'.obj.left (intrinsicSingularLocus X'.obj))
        (intrinsicReducedCentreIdealInclusion X'.obj.left (intrinsicSingularLocus X'.obj)) := by
  have hF : (cleanupMap p' p hp' hp u hu g hg hdiag A' A).hom.left ≫ (cleanupMorphism p hp A).hom.left =
      (cleanupMorphism p' hp' A').hom.left ≫ u.hom.left :=
    congrArg (fun f : cleanupSource p' hp' A' ⟶ X => f.hom.left) (cleanupMap_overX p' p hp' hp u hu g hg hdiag A' A)
  change nativePulledIdealSubmodule (cleanupMap p' p hp' hp u hu g hg hdiag A' A).hom.left
    (nativePulledIdealModule (cleanupMorphism p hp A).hom.left _ _)
    (nativePulledIdealInclusion (cleanupMorphism p hp A).hom.left _ _) = _
  rw [submodule_comp, hF]
  apply PresheafOfModules.Submodule.ext
  intro U
  ext t
  constructor
  · intro ht z hz
    rw [← HironakaG1NativeSmoothCleanupCore.smoothBase_stalkIdeal_eq u hu (cleanupMorphism p' hp' A').hom.left z]
    exact ht z hz
  · intro ht z hz
    rw [HironakaG1NativeSmoothCleanupCore.smoothBase_stalkIdeal_eq u hu (cleanupMorphism p' hp' A').hom.left z]
    exact ht z hz

/-- ENTIRE native original-Sing totalideal along the SAME constructed global arrow. -/
def totalIdealIso :
    nativePulledIdealModule (cleanupMap p' p hp' hp u hu g hg hdiag A' A).hom.left
        (totalIdealModule p hp A) (totalIdealInclusion p hp A) ≅ totalIdealModule p' hp' A' where
  hom := ⟨PresheafOfModules.Submodule.homOfLE (totalIdealSubmodule_eq p' p hp' hp u hu g hg hdiag A' A).le⟩
  inv := ⟨PresheafOfModules.Submodule.homOfLE (totalIdealSubmodule_eq p' p hp' hp u hu g hg hdiag A' A).ge⟩
  hom_inv_id := by ext U t; rfl
  inv_hom_id := by ext U t; rfl

/-- Forward literal original unit-inclusion triangle. -/
theorem totalIdealIso_hom_comp_inclusion :
    (totalIdealIso p' p hp' hp u hu g hg hdiag A' A).hom ≫ totalIdealInclusion p' hp' A' =
      nativePulledIdealInclusion (cleanupMap p' p hp' hp u hu g hg hdiag A' A).hom.left
        (totalIdealModule p hp A) (totalIdealInclusion p hp A) := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι (totalIdealSubmodule_eq p' p hp' hp u hu g hg hdiag A' A).le

/-- Inverse literal original unit-inclusion triangle. -/
theorem totalIdealIso_inv_comp_inclusion :
    (totalIdealIso p' p hp' hp u hu g hg hdiag A' A).inv ≫
        nativePulledIdealInclusion (cleanupMap p' p hp' hp u hu g hg hdiag A' A).hom.left
          (totalIdealModule p hp A) (totalIdealInclusion p hp A) = totalIdealInclusion p' hp' A' := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι (totalIdealSubmodule_eq p' p hp' hp u hu g hg hdiag A' A).ge

end
end Hironaka.Analytic.Unibranch.HironakaG1NativeSmoothCleanup
