import Hironaka.Analytic.Unibranch.HironakaG1NativeCleanupComparisonLaws
import Hironaka.Analytic.Unibranch.OriginalNativeSmoothSingularLocus

/-! # Actual native resolution-diagram isomorphisms and cleanup

Whole original singular ideals and marked-record pullback identities are
DERIVED from actual native diagram isomorphisms. The SAME-family terminal
functor then gives the genuine cleanup isomorphism, full original squares,
inverse ORIGINAL Reg identity and whole total-ideal transport. This first
scope uses genuine full models of the nonempty sources; arbitrary component
reindexing and arbitrary smooth maps remain separate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG1NativeCleanupDiagramIso

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceManifoldCharts
  HironakaReducedComplexAnalyticSpaces HironakaEmbeddedNativeMorphism
  HironakaIntrinsicReducedCentreIdealSheaf HironakaIntrinsicReducedCentreOpenPullback
  HironakaNativePulledIdealSheaf HironakaNativePulledIdealStalk HironakaNativePulledIdealComposition
  HironakaSingularModuleSheafStalk HironakaG10ChowGermIdealDictionary
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold HironakaG1OriginalTerminalBaseIso
  HironakaSmoothSubmersionCoefficientIdeals HironakaIntrinsicComplexAnalyticRegularLocus
  SourceReducedComplexSpace OriginalNativeModification OriginalIntrinsicSingularLocus
  OriginalNativeSmoothLocalProduct OriginalNativeSmoothReducedIdealPullback
  OriginalNativeSmoothSingularLocus HironakaG1OriginalSingularCleanup
  HironakaG1NativeModelIdealTransport HironakaG1NativeCleanupModelIndependence

attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold

noncomputable section

variable {X X' Y Y' : SourceReducedComplexSpace}

/-- The ordinary actual native isomorphism is smooth by its genuine open immersion. -/
theorem nativeIso_smooth (u : X' ≅ X) : IsSmoothMorphism u.hom := by
  apply isSmoothMorphism_of_isOpenImmersion
  change LocallyRingedSpace.IsOpenImmersion (isoLeft u).hom
  infer_instance

/-- ENTIRE original singular model ideals commute with the actual base iso.
This uses the existing dictionary DEFINITION, not another faithfulness engine. -/
theorem originalSingularGermIdeal_baseIso (u : X' ≅ X)
    {n : ℕ} {M : CMfd.{0} n} (a : wholeModel (n := n) M ⟶ X') :
    originalSingularGermIdeal X (a ≫ u.hom) = originalSingularGermIdeal X' a := by
  let B := intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj)
  let b := intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj)
  let B' := intrinsicReducedCentreIdealModule X'.obj.left (intrinsicSingularLocus X'.obj)
  let b' := intrinsicReducedCentreIdealInclusion X'.obj.left (intrinsicSingularLocus X'.obj)
  have hK (y : X'.obj.left) : nativePulledIdealStalkIdeal u.hom.hom.left B b y =
      LinearMap.range (stalkInclusionLinearMap X'.obj.left.toSheafedSpace.sheaf B' b' y) := by
    have h := smooth_pulled_stalkIdeal_eq u.hom y (nativeIso_smooth u y)
      (isAnalyticSubset_intrinsicSingularLocus X)
    rw [preimage_intrinsicSingularLocus u.hom (nativeIso_smooth u)] at h
    exact h
  have hComp (F : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M ⟶ X'.obj.left) (x : M) :
      nativePulledIdealStalkIdeal (F ≫ u.hom.hom.left) B b x =
        nativePulledIdealStalkIdeal F B' b' x := by
    calc
      _ = nativePulledIdealStalkIdeal F (nativePulledIdealModule u.hom.hom.left B b)
          (nativePulledIdealInclusion u.hom.hom.left B b) x :=
        (stalkIdeal_comp u.hom.hom.left F B b x).symm
      _ = _ := congrArg (Ideal.map (F.stalkMap x).hom)
        ((nativePulledIdealStalkInclusion_range u.hom.hom.left B b (F.base x)).trans (hK (F.base x)))
  apply GermIdeal.ext
  funext x g
  apply propext
  let F := (actualSubspaceUnivIso (n := n) (M := M)).inv ≫ a.hom.left
  have hF := hComp F x
  change nativePulledIdealStalkIdeal
    (((actualSubspaceUnivIso (n := n) (M := M)).inv ≫ a.hom.left) ≫ u.hom.hom.left) B b x = _ at hF
  rw [Category.assoc] at hF
  change (∃ hg : HolomorphicAt n g x,
      actualOriginalFunctionGerm x g hg ∈ nativePulledIdealStalkIdeal
        ((actualSubspaceUnivIso (n := n) (M := M)).inv ≫ (a ≫ u.hom).hom.left) B b x) ↔
    ∃ hg : HolomorphicAt n g x,
      actualOriginalFunctionGerm x g hg ∈ nativePulledIdealStalkIdeal F B' b' x
  constructor
  · rintro ⟨hg, hm⟩
    exact ⟨hg, hF ▸ hm⟩
  · rintro ⟨hg, hm⟩
    exact ⟨hg, hF.symm ▸ hm⟩

/-- An ordinary actual resolution internally supplies inverse ORIGINAL-Sing thinness. -/
theorem resolutionSingularPreimage_thin {A B : SourceReducedComplexSpace}
    (p : A ⟶ B) (hp : IsResolution p) :
    interior (p.hom.left.base ⁻¹' intrinsicSingularLocus B.obj) = ∅ := by
  obtain ⟨_, Z, _, _, hpre, hiso⟩ := hp.2
  exact hiso.interior_preimage_eq_empty hpre (interior_intrinsicSingularLocus_eq_empty B)

private def nativeWholeIso {n₀ n₁ : ℕ} {D₀ : CMfd.{0} n₀} {D₁ : CMfd.{0} n₁}
    (η : D₀ ≃ₘ⟮𝓘(ℂ, ComplexModel n₀), 𝓘(ℂ, ComplexModel n₁)⟯ D₁) :
    wholeModel (n := n₀) D₀ ≅ wholeModel (n := n₁) D₁ where
  hom := nativeMorphism η.contMDiff
  inv := nativeMorphism η.symm.contMDiff
  hom_inv_id := by
    apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
    intro z
    apply Subtype.ext
    exact η.symm_apply_apply z.val
  inv_hom_id := by
    apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
    intro z
    apply Subtype.ext
    exact η.apply_symm_apply z.val

/-- ACTUAL native diagram isomorphisms derive the whole ideal/record identity
and SAME-family cleanup iso, without supplied ideal/terminal comparison data. -/
theorem exists_cleanup_diagram_iso_of_thin [Nonempty Y'.obj.left]
    (p' : Y' ⟶ X') (p : Y ⟶ X)
    (hthin' : interior (p'.hom.left.base ⁻¹' intrinsicSingularLocus X'.obj) = ∅)
    (hthin : interior (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj) = ∅)
    (u : X' ≅ X) (v : Y' ≅ Y) (hdiag : p' ≫ u.hom = v.hom ≫ p)
    {n' n : ℕ} {M' : CMfd.{0} n'} {M : CMfd.{0} n}
    (E' : wholeModel (n := n') M' ≅ Y') (E : wholeModel (n := n) M ≅ Y) :
    ∃ (η : modelTerminal p' hthin' E'
        ≃ₘ⟮𝓘(ℂ, ComplexModel n'), 𝓘(ℂ, ComplexModel n)⟯
          modelTerminal p hthin E)
      (e : wholeModel (n := n') (modelTerminal p' hthin' E') ≅
        wholeModel (n := n) (modelTerminal p hthin E)),
      e.hom = nativeMorphism η.contMDiff ∧
      e.hom ≫ modelCleanupMap p hthin E =
        modelCleanupMap p' hthin' E' ≫ v.hom ∧
      e.hom ≫ (modelCleanupMap p hthin E ≫ p) =
        (modelCleanupMap p' hthin' E' ≫ p') ≫ u.hom ∧
      e.hom.hom.left.base ⁻¹'
          ((modelCleanupMap p hthin E ≫ p).hom.left.base ⁻¹'
            intrinsicRegularLocus X.obj) =
        (modelCleanupMap p' hthin' E' ≫ p').hom.left.base ⁻¹'
          intrinsicRegularLocus X'.obj ∧
      GermIdeal.pullback (m := n') η (modelTotalIdeal p hthin E) =
        modelTotalIdeal p' hthin' E' := by
  have hn := nativeModel_dimension_eq (E.trans v.symm) E'
  subst n
  let eM := E'.trans (v.trans E.symm)
  let f := nativeDiffeomorph (isoLeft eM) (Over.w eM.hom.hom)
  let T' := modelMarkedIdeal p' E'
  let T := modelMarkedIdeal p E
  let hT' := modelMarkedDomain p' hthin' E'
  let hT := modelMarkedDomain p hthin E
  have htrace : (E'.hom ≫ p') ≫ u.hom = eM.hom ≫ (E.hom ≫ p) := by
    simp only [eM, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc, hdiag]
  have hbase := originalSingularGermIdeal_baseIso u (E'.hom ≫ p')
  rw [htrace] at hbase
  have hI := hbase.symm.trans (originalSingularGermIdeal_transport X eM (E.hom ≫ p))
  have hrecord : T' = markedPullback (m := n') f T := by
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · change univ = f ⁻¹' (univ : Set M)
      rw [preimage_univ]
    · rfl
    · exact hI
    · rfl
  let η := originalTerminalMarkedRecordIso f T hT T' hT' hrecord
  let e := nativeWholeIso η
  have hproj : nativeMorphism η.contMDiff ≫
      nativeMorphism (originalTerminalGluedProjection_contMDiff T hT) =
      nativeMorphism (originalTerminalGluedProjection_contMDiff T' hT') ≫ eM.hom := by
    apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
    intro z
    apply Subtype.ext
    exact originalTerminalMarkedRecordIso_proj f T hT T' hT' hrecord z.val
  have hY : e.hom ≫ modelCleanupMap p hthin E =
      modelCleanupMap p' hthin' E' ≫ v.hom := by
    change nativeMorphism η.contMDiff ≫
      (nativeMorphism (originalTerminalGluedProjection_contMDiff T hT) ≫ E.hom) =
      (nativeMorphism (originalTerminalGluedProjection_contMDiff T' hT') ≫ E'.hom) ≫ v.hom
    rw [← Category.assoc, hproj, Category.assoc]
    simp only [eM, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hX : e.hom ≫ (modelCleanupMap p hthin E ≫ p) =
      (modelCleanupMap p' hthin' E' ≫ p') ≫ u.hom := by
    rw [← Category.assoc, hY, Category.assoc, ← hdiag, ← Category.assoc]
  have hreg : e.hom.hom.left.base ⁻¹'
        ((modelCleanupMap p hthin E ≫ p).hom.left.base ⁻¹'
          intrinsicRegularLocus X.obj) =
      (modelCleanupMap p' hthin' E' ≫ p').hom.left.base ⁻¹'
        intrinsicRegularLocus X'.obj := by
    ext z
    have hz := congrArg
      (fun g : wholeModel (n := n') (modelTerminal p' hthin' E') ⟶ X =>
        g.hom.left.base z) hX
    change (modelCleanupMap p hthin E ≫ p).hom.left.base
        (e.hom.hom.left.base z) =
      u.hom.hom.left.base
        ((modelCleanupMap p' hthin' E' ≫ p').hom.left.base z) at hz
    change (modelCleanupMap p hthin E ≫ p).hom.left.base
        (e.hom.hom.left.base z) ∈ intrinsicRegularLocus X.obj ↔ _
    rw [hz]
    exact Set.ext_iff.mp (preimage_intrinsicRegularLocus u.hom (nativeIso_smooth u)) _
  refine ⟨η, e, rfl, hY, hX, hreg, ?_⟩
  exact originalTerminalMarkedRecordIso_wholeIdeal f T hT T' hT' hrecord


/-- Ordinary ACTUAL resolutions derive both thinness hypotheses internally. -/
theorem exists_cleanup_diagram_iso [Nonempty Y'.obj.left]
    (p' : Y' ⟶ X') (p : Y ⟶ X) (hp' : IsResolution p') (hp : IsResolution p)
    (u : X' ≅ X) (v : Y' ≅ Y) (hdiag : p' ≫ u.hom = v.hom ≫ p)
    {n' n : ℕ} {M' : CMfd.{0} n'} {M : CMfd.{0} n}
    (E' : wholeModel (n := n') M' ≅ Y') (E : wholeModel (n := n) M ≅ Y) :
    ∃ (η : modelTerminal p' (resolutionSingularPreimage_thin p' hp') E'
        ≃ₘ⟮𝓘(ℂ, ComplexModel n'), 𝓘(ℂ, ComplexModel n)⟯
          modelTerminal p (resolutionSingularPreimage_thin p hp) E)
      (e : wholeModel (n := n') (modelTerminal p' (resolutionSingularPreimage_thin p' hp') E') ≅
        wholeModel (n := n) (modelTerminal p (resolutionSingularPreimage_thin p hp) E)),
      e.hom = nativeMorphism η.contMDiff ∧
      e.hom ≫ modelCleanupMap p (resolutionSingularPreimage_thin p hp) E =
        modelCleanupMap p' (resolutionSingularPreimage_thin p' hp') E' ≫ v.hom ∧
      e.hom ≫ (modelCleanupMap p (resolutionSingularPreimage_thin p hp) E ≫ p) =
        (modelCleanupMap p' (resolutionSingularPreimage_thin p' hp') E' ≫ p') ≫ u.hom ∧
      e.hom.hom.left.base ⁻¹'
          ((modelCleanupMap p (resolutionSingularPreimage_thin p hp) E ≫ p).hom.left.base ⁻¹'
            intrinsicRegularLocus X.obj) =
        (modelCleanupMap p' (resolutionSingularPreimage_thin p' hp') E' ≫ p').hom.left.base ⁻¹'
          intrinsicRegularLocus X'.obj ∧
      GermIdeal.pullback (m := n') η (modelTotalIdeal p (resolutionSingularPreimage_thin p hp) E) =
        modelTotalIdeal p' (resolutionSingularPreimage_thin p' hp') E' := by
  exact exists_cleanup_diagram_iso_of_thin p' p
    (resolutionSingularPreimage_thin p' hp') (resolutionSingularPreimage_thin p hp) u v hdiag E' E

end
end Hironaka.Analytic.Unibranch.HironakaG1NativeCleanupDiagramIso
