import Hironaka.Analytic.Unibranch.HironakaG1NativeCleanupDiagramLaws

/-! # Actual cleanup over an ordinary manifold submersion

The whole original singular-ideal/marked-record pullback and source
thinness are DERIVED. The terminal map is the HELD same-family global
smooth arrow after HELD whole-record transport. No C18 native-smooth
reflection code or desired ideal/history/terminal packet is introduced.
Blueprint precedes source.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG1NativeSmoothCleanupCore

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal HironakaActualAnalyticSubspace
  HironakaActualAnalyticSubspaceManifoldCharts HironakaEmbeddedNativeMorphism
  HironakaIntrinsicReducedCentreIdealSheaf HironakaIntrinsicReducedCentreOpenPullback
  HironakaNativePulledIdealSheaf HironakaNativePulledIdealStalk HironakaNativePulledIdealComposition
  HironakaSingularModuleSheafStalk HironakaG10ChowGermIdealDictionary
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionOriginalAmbientCanonical
  HironakaSmoothSubmersionOriginalGlobalMap HironakaSmoothSubmersionOriginalGlobalSubmersion
  HironakaSmoothSubmersionOriginalGlobalFunctor HironakaSmoothSubmersionOriginalTerminalSubmersion
  HironakaSmoothSubmersionOrderedChoiceImageTrace HironakaSmoothSubmersionOrderedImageTrace
  SourceReducedComplexSpace OriginalNativeModification OriginalIntrinsicSingularLocus
  OriginalNativeSmoothLocalProduct OriginalNativeSmoothReducedIdealPullback
  OriginalNativeSmoothSingularLocus HironakaG1OriginalSingularCleanup HironakaG1NativeModelIdealTransport
  HironakaG1NativeCleanupModelIndependence HironakaG1NativeCleanupDiagramIso

attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold

noncomputable section

variable {X X' : SourceReducedComplexSpace}

/-- Whole original singular stalk transport under ORDINARY native smooth base change. -/
theorem smoothBase_stalkIdeal_eq {Z : LocallyRingedSpace.{0}}
    (u : X' ⟶ X) (hu : IsSmoothMorphism u) (F : Z ⟶ X'.obj.left) (z : Z) :
    nativePulledIdealStalkIdeal (F ≫ u.hom.left)
      (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
      (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj)) z =
    nativePulledIdealStalkIdeal F
      (intrinsicReducedCentreIdealModule X'.obj.left (intrinsicSingularLocus X'.obj))
      (intrinsicReducedCentreIdealInclusion X'.obj.left (intrinsicSingularLocus X'.obj)) z := by
  let B := intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj)
  let b := intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj)
  have hK := smooth_pulled_stalkIdeal_eq u (F.base z) (hu (F.base z))
    (isAnalyticSubset_intrinsicSingularLocus X)
  rw [preimage_intrinsicSingularLocus u hu] at hK
  calc
    _ = nativePulledIdealStalkIdeal F (nativePulledIdealModule u.hom.left B b)
        (nativePulledIdealInclusion u.hom.left B b) z := (stalkIdeal_comp u.hom.left F B b z).symm
    _ = _ := congrArg (Ideal.map (F.stalkMap z).hom)
      ((nativePulledIdealStalkInclusion_range u.hom.left B b (F.base z)).trans hK)

/-- Existing model-germ membership and whole native composition give the
ENTIRE original singular germ-ideal base-change identity. -/
theorem originalSingularGermIdeal_smoothBase
    (u : X' ⟶ X) (hu : IsSmoothMorphism u) {m : ℕ} {M' : CMfd.{0} m}
    (a' : wholeModel (n := m) M' ⟶ X') :
    originalSingularGermIdeal X (a' ≫ u) = originalSingularGermIdeal X' a' := by
  apply GermIdeal.ext
  funext x g
  apply propext
  let F := (actualSubspaceUnivIso (n := m) (M := M')).inv ≫ a'.hom.left
  have hF := smoothBase_stalkIdeal_eq u hu F x
  change nativePulledIdealStalkIdeal
    (((actualSubspaceUnivIso (n := m) (M := M')).inv ≫ a'.hom.left) ≫ u.hom.left) _ _ x = _ at hF
  rw [Category.assoc] at hF
  change (∃ hg : HolomorphicAt m g x, actualOriginalFunctionGerm x g hg ∈
      nativePulledIdealStalkIdeal
        ((actualSubspaceUnivIso (n := m) (M := M')).inv ≫ (a' ≫ u).hom.left) _ _ x) ↔
    ∃ hg : HolomorphicAt m g x, actualOriginalFunctionGerm x g hg ∈
      nativePulledIdealStalkIdeal F _ _ x
  constructor
  · rintro ⟨hg, hm⟩
    exact ⟨hg, hF ▸ hm⟩
  · rintro ⟨hg, hm⟩
    exact ⟨hg, hF.symm ▸ hm⟩

variable {m n : ℕ} {M' : CMfd.{0} m} {M : CMfd.{0} n}
  (u : X' ⟶ X) (hu : IsSmoothMorphism u) (b : M' → M)
  (hb : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ b)
  (a' : wholeModel (n := m) M' ⟶ X') (a : wholeModel (n := n) M ⟶ X)
  (hdiag : nativeMorphism hb.contMDiff ≫ a = a' ≫ u)

include hb

/-- Coherence of the actual WHOLE original singular ideal pullback. -/
theorem originalSingularGermIdeal_pullback_coherent :
    (GermIdeal.pullback (m := m) b (originalSingularGermIdeal X a)).IsCoherent :=
  GermIdealPullbackCalculus.isCoherent_pullback hb.contMDiff (originalSingularGermIdeal_coherent X a)

include u hu hdiag

/-- The FULL ordinary diagram derives all fields of the actual marked pullback. -/
theorem wholeMarkedRecord_pullback :
    modelMarkedIdeal a' (Iso.refl _) =
      markedPullback (m := m) b (modelMarkedIdeal a (Iso.refl _)) := by
  let := IntrinsicAnalyticCentreFiniteType.intrinsicReducedCentreIdealModule_isFiniteType
    X (intrinsicSingularLocus X.obj) (isAnalyticSubset_intrinsicSingularLocus X)
  have hpull := modelGermIdeal_pullback
    (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
    (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj)) a.hom.left hb.contMDiff
  change GermIdeal.pullback (m := m) b (originalSingularGermIdeal X a) =
    originalSingularGermIdeal X (nativeMorphism hb.contMDiff ≫ a) at hpull
  rw [hdiag] at hpull
  have hI := (originalSingularGermIdeal_smoothBase u hu a').symm.trans hpull.symm
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · change univ = b ⁻¹' (univ : Set M)
    rw [preimage_univ]
  · rfl
  · change originalSingularGermIdeal X' (𝟙 _ ≫ a') =
      GermIdeal.pullback (m := m) b (originalSingularGermIdeal X (𝟙 _ ≫ a))
    simpa only [Category.id_comp] using hI
  · rfl

/-- Source thinness is DERIVED from ordinary target thinness and actual b/u. -/
theorem sourceThin (hthin : interior (a.hom.left.base ⁻¹' intrinsicSingularLocus X.obj) = ∅) :
    interior (a'.hom.left.base ⁻¹' intrinsicSingularLocus X'.obj) = ∅ := by
  let B := nativeMorphism hb.contMDiff
  have hopen : IsOpenMap B.hom.left.base := by
    change IsOpenMap ((Homeomorph.Set.univ M).symm ∘ b ∘ (Homeomorph.Set.univ M'))
    exact (Homeomorph.Set.univ M).symm.isOpenMap.comp
      ((isOpenMap_of_isSubmersion hb).comp (Homeomorph.Set.univ M').isOpenMap)
  have hset : a'.hom.left.base ⁻¹' intrinsicSingularLocus X'.obj =
      B.hom.left.base ⁻¹' (a.hom.left.base ⁻¹' intrinsicSingularLocus X.obj) := by
    ext z
    have hz := congrArg (fun f : wholeModel (n := m) M' ⟶ X => f.hom.left.base z) hdiag
    change a.hom.left.base (B.hom.left.base z) = u.hom.left.base (a'.hom.left.base z) at hz
    change a'.hom.left.base z ∈ intrinsicSingularLocus X'.obj ↔
      a.hom.left.base (B.hom.left.base z) ∈ intrinsicSingularLocus X.obj
    rw [hz]
    exact smoothAt_singular_iff u (a'.hom.left.base z) (hu _)
  rw [hset]
  exact (hopen.preimage_interior_eq_interior_preimage B.hom.left.base.hom.continuous
    (a.hom.left.base ⁻¹' intrinsicSingularLocus X.obj)).symm.trans
      (by rw [hthin, preimage_empty])

variable (hthin : interior (a.hom.left.base ⁻¹' intrinsicSingularLocus X.obj) = ∅)

/-- The HELD actual global smooth arrow after the DERIVED whole-record transport. -/
def terminalMap :
    modelTerminal a' (sourceThin u hu b hb a' a hdiag hthin) (Iso.refl _) →
      modelTerminal a hthin (Iso.refl _) :=
  let T := modelMarkedIdeal a (Iso.refl _)
  let T' := modelMarkedIdeal a' (Iso.refl _)
  let hT := modelMarkedDomain a hthin (Iso.refl _)
  let hT' := modelMarkedDomain a' (sourceThin u hu b hb a' a hdiag hthin) (Iso.refl _)
  originalGlobalSmoothMap hb T hT ∘ terminalRecordEquiv T' (markedPullback (m := m) b T) hT'
    (original_ambient_domain_pullback hb T hT) (wholeMarkedRecord_pullback u hu b hb a' a hdiag)

/-- Genuine terminal submersion is a conclusion of the SAME canonical construction. -/
theorem terminalMap_isSubmersion :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞
      (terminalMap u hu b hb a' a hdiag hthin) :=
  isSubmersion_precompose_biholomorphism
    (originalGlobalSmoothMap_isSubmersion hb (modelMarkedIdeal a (Iso.refl _))
      (modelMarkedDomain a hthin (Iso.refl _)))
    (terminalRecordEquiv _ _ _ _ (wholeMarkedRecord_pullback u hu b hb a' a hdiag))

/-- The actual terminal projection formula, retaining the original b. -/
theorem terminalMap_proj
    (z : modelTerminal a' (sourceThin u hu b hb a' a hdiag hthin) (Iso.refl _)) :
    originalTerminalGluedProjection (modelMarkedIdeal a (Iso.refl _))
        (modelMarkedDomain a hthin (Iso.refl _)) (terminalMap u hu b hb a' a hdiag hthin z) =
      b (originalTerminalGluedProjection (modelMarkedIdeal a' (Iso.refl _))
        (modelMarkedDomain a' (sourceThin u hu b hb a' a hdiag hthin) (Iso.refl _)) z) := by
  unfold terminalMap
  rw [Function.comp_apply, originalGlobalSmoothMap_proj, terminalRecordEquiv_proj]

/-- FULL native projection square over the SAME actual manifold b. -/
theorem terminalMap_native_overModels :
    nativeMorphism (terminalMap_isSubmersion u hu b hb a' a hdiag hthin).contMDiff ≫
        modelCleanupMap a hthin (Iso.refl _) =
      modelCleanupMap a' (sourceThin u hu b hb a' a hdiag hthin) (Iso.refl _) ≫ nativeMorphism hb.contMDiff := by
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro z
  apply Subtype.ext
  exact terminalMap_proj u hu b hb a' a hdiag hthin z.val

/-- FULL original native square over the SAME ordinary smooth base u. -/
theorem terminalMap_native_overX :
    nativeMorphism (terminalMap_isSubmersion u hu b hb a' a hdiag hthin).contMDiff ≫
        (modelCleanupMap a hthin (Iso.refl _) ≫ a) =
      (modelCleanupMap a' (sourceThin u hu b hb a' a hdiag hthin) (Iso.refl _) ≫ a') ≫ u := by
  rw [← Category.assoc, terminalMap_native_overModels, Category.assoc, hdiag, ← Category.assoc]

/-- ENTIRE original totalideal pullback, before radicals or support replacements. -/
theorem terminalMap_wholeIdeal :
    GermIdeal.pullback (m := m) (terminalMap u hu b hb a' a hdiag hthin)
        (modelTotalIdeal a hthin (Iso.refl _)) =
      modelTotalIdeal a' (sourceThin u hu b hb a' a hdiag hthin) (Iso.refl _) := by
  let T := modelMarkedIdeal a (Iso.refl _)
  let T' := modelMarkedIdeal a' (Iso.refl _)
  let hT := modelMarkedDomain a hthin (Iso.refl _)
  let hT' := modelMarkedDomain a' (sourceThin u hu b hb a' a hdiag hthin) (Iso.refl _)
  change GermIdeal.pullback (m := m) (terminalMap u hu b hb a' a hdiag hthin)
    (GermIdeal.pullback (m := n) (originalTerminalGluedProjection T hT) T.ideal) =
    GermIdeal.pullback (m := m) (originalTerminalGluedProjection T' hT') T'.ideal
  erw [← coherent_pullback_comp (originalTerminalGluedProjection_contMDiff T hT)
    (terminalMap_isSubmersion u hu b hb a' a hdiag hthin).contMDiff T.ideal hT.isWellFormed.isCoherent]
  have he : originalTerminalGluedProjection T hT ∘ terminalMap u hu b hb a' a hdiag hthin =
      b ∘ originalTerminalGluedProjection T' hT' := funext (terminalMap_proj u hu b hb a' a hdiag hthin)
  rw [he, coherent_pullback_comp hb.contMDiff (originalTerminalGluedProjection_contMDiff T' hT')
    T.ideal hT.isWellFormed.isCoherent]
  have hI : T'.ideal = GermIdeal.pullback (m := m) b T.ideal :=
    congrArg (fun R : MarkedIdeal m M' => R.ideal) (wholeMarkedRecord_pullback u hu b hb a' a hdiag)
  rw [← hI]

/-- An ACTUAL target resolution supplies the ordinary core thinness internally.
No component/source map is assumed to resolve all of its original target. -/
theorem exists_terminalMap_of_resolution (ha : IsResolution a) :
    let h := resolutionSingularPreimage_thin a ha
    ∃ (G : modelTerminal a' (sourceThin u hu b hb a' a hdiag h) (Iso.refl _) →
        modelTerminal a h (Iso.refl _))
      (hG : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ G),
      nativeMorphism hG.contMDiff ≫ (modelCleanupMap a h (Iso.refl _) ≫ a) =
          (modelCleanupMap a' (sourceThin u hu b hb a' a hdiag h) (Iso.refl _) ≫ a') ≫ u ∧
      GermIdeal.pullback (m := m) G (modelTotalIdeal a h (Iso.refl _)) =
        modelTotalIdeal a' (sourceThin u hu b hb a' a hdiag h) (Iso.refl _) := by
  dsimp only
  exact ⟨terminalMap u hu b hb a' a hdiag _, terminalMap_isSubmersion u hu b hb a' a hdiag _,
    terminalMap_native_overX u hu b hb a' a hdiag _, terminalMap_wholeIdeal u hu b hb a' a hdiag _⟩

end
end Hironaka.Analytic.Unibranch.HironakaG1NativeSmoothCleanupCore
