import Hironaka.Analytic.Unibranch.HironakaG1NativeModelIdealTransport
import Hironaka.Analytic.Unibranch.OriginalSmoothDimension
import Hironaka.Analytic.Unibranch.EmbeddedCommonResolutionGeneral
import Hironaka.Resolution.HironakaG1OriginalTerminalBaseIso

/-! # Actual model-choice comparison for one nonempty native component

The two ordinary genuine native manifold-model witnesses may be arbitrary
outputs of the proved model factory. Their dimension, whole original singular
ideal comparison and whole marked-record comparison are internally derived.
The actual terminal comparison uses the HELD canonical-family forward arrow.
This is not the global arbitrary-component cleanup assignment.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG1NativeCleanupModelIndependence

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceManifoldCharts
  HironakaReducedComplexAnalyticSpaces HironakaEmbeddedNativeMorphism
  HironakaG10ChowGermIdealDictionary HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold
  HironakaG1OriginalTerminalBaseIso HironakaSmoothSubmersionCoefficientIdeals
  HironakaG1OriginalSingularCleanup HironakaG1NativeModelIdealTransport
  SourceReducedComplexSpace OriginalNativeModification OriginalIntrinsicSingularLocus
  HironakaIntrinsicComplexAnalyticRegularLocus
open Hironaka.ResolutionInvariantSpec (IsInvDomain)

attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold

noncomputable section

variable {X Y : SourceReducedComplexSpace}

/-- An actual point of the SAME native space derives equality of model
dimensions through the full native model isomorphism and scalar maps. -/
theorem nativeModel_dimension_eq [Nonempty Y.obj.left]
    {n₀ n₁ : ℕ} {M₀ : CMfd.{0} n₀} {M₁ : CMfd.{0} n₁}
    (E₀ : wholeModel (n := n₀) M₀ ≅ Y) (E₁ : wholeModel (n := n₁) M₁ ≅ Y) : n₀ = n₁ := by
  let e := E₀.trans E₁.symm
  let Q₀ := actualSubspaceUnivIso (n := n₀) (M := M₀)
  let Q₁ := actualSubspaceUnivIso (n := n₁) (M := M₁)
  let F := (Q₀.symm.trans (isoLeft e)).trans Q₁
  have hF : F.hom ≫ ambientPointMap n₁ M₁ = ambientPointMap n₀ M₀ := by
    change (Q₀.inv ≫ e.hom.hom.left ≫ Q₁.hom) ≫ ambientPointMap n₁ M₁ = _
    simp only [Category.assoc]
    rw [show Q₁.hom ≫ ambientPointMap n₁ M₁ = subspacePointMap (n := n₁) (univ : Set M₁) from rfl]
    erw [Over.w e.hom.hom, actualSubspaceUnivIso_inv_point]
  let y : Y.obj.left := Classical.choice (inferInstance : Nonempty Y.obj.left)
  exact OriginalSmoothDimension.native_iso_dimension_eq F hF ((isoHomeomorph E₀).symm y).val

variable (p : Y ⟶ X)

/-- The actual mark-one / empty-boundary / whole-space ORIGINAL singular input. -/
def modelMarkedIdeal {n : ℕ} {M : CMfd.{0} n} (E : wholeModel (n := n) M ≅ Y) : MarkedIdeal n M :=
  ⟨univ, [], originalSingularGermIdeal X (E.hom ≫ p), 1⟩

private theorem modelOriginalIdeal_thin
    (hthin : interior (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj) = ∅)
    {n : ℕ} {M : CMfd.{0} n} (E : wholeModel (n := n) M ≅ Y) :
    interior (originalSingularGermIdeal X (E.hom ≫ p)).zeroLocus = ∅ := by
  rw [originalSingularGermIdeal_zeroLocus]
  change interior ((Homeomorph.Set.univ M).symm ⁻¹'
    ((isoHomeomorph E) ⁻¹' (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj))) = ∅
  rw [← (Homeomorph.Set.univ M).symm.preimage_interior,
    ← (isoHomeomorph E).preimage_interior, hthin, preimage_empty, preimage_empty]

/-- Actual original thinness and coherence internally give BOTH marked domains. -/
theorem modelMarkedDomain
    (hthin : interior (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj) = ∅)
    {n : ℕ} {M : CMfd.{0} n} (E : wholeModel (n := n) M ≅ Y) :
    IsInvDomain n (modelMarkedIdeal p E) :=
  HironakaPrincipalizationBoundary.isInvDomain_univ_of_isSNCDivisor
    (originalSingularGermIdeal_coherent X (E.hom ≫ p))
    (PrescribedBlowupDomination.isNonzeroAlongAt_of_interior_zeroLocus_eq_empty
      (originalSingularGermIdeal_coherent X (E.hom ≫ p)) (modelOriginalIdeal_thin p hthin E))
    (isSNCDivisor_nil (n := n) (M := M))

/-- The same actual terminal construction of this precise model-marked input. -/
def modelTerminal
    (hthin : interior (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj) = ∅)
    {n : ℕ} {M : CMfd.{0} n} (E : wholeModel (n := n) M ≅ Y) : CMfd.{0} n :=
  originalTerminalManifold (modelMarkedIdeal p E) (modelMarkedDomain p hthin E)

/-- The ENTIRE literal original total ideal on the actual cleanup manifold. -/
def modelTotalIdeal
    (hthin : interior (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj) = ∅)
    {n : ℕ} {M : CMfd.{0} n} (E : wholeModel (n := n) M ≅ Y) :
    GermIdeal n (modelTerminal p hthin E) :=
  GermIdeal.pullback (m := n)
    (originalTerminalGluedProjection (modelMarkedIdeal p E) (modelMarkedDomain p hthin E))
    (originalSingularGermIdeal X (E.hom ≫ p))

/-- The FULL actual original native cleanup projection over the same Y. -/
def modelCleanupMap
    (hthin : interior (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj) = ∅)
    {n : ℕ} {M : CMfd.{0} n} (E : wholeModel (n := n) M ≅ Y) :
    wholeModel (n := n) (modelTerminal p hthin E) ⟶ Y :=
  nativeMorphism (originalTerminalGluedProjection_contMDiff
    (modelMarkedIdeal p E) (modelMarkedDomain p hthin E)) ≫ E.hom

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

/-- Both dimensions, the WHOLE ideal/marked-record transport, and the actual
native cleanup comparison over Y and original X are internally derived.
The terminal forward arrow is the held actual canonical-family arrow. -/
theorem exists_cleanup_model_comparison_of_thin [Nonempty Y.obj.left]
    (hthin : interior (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj) = ∅)
    {n₀ n₁ : ℕ} {M₀ : CMfd.{0} n₀} {M₁ : CMfd.{0} n₁}
    (E₀ : wholeModel (n := n₀) M₀ ≅ Y) (E₁ : wholeModel (n := n₁) M₁ ≅ Y) :
    ∃ (η : modelTerminal p hthin E₀
        ≃ₘ⟮𝓘(ℂ, ComplexModel n₀), 𝓘(ℂ, ComplexModel n₁)⟯ modelTerminal p hthin E₁)
      (e : wholeModel (n := n₀) (modelTerminal p hthin E₀) ≅
        wholeModel (n := n₁) (modelTerminal p hthin E₁)),
      e.hom = nativeMorphism η.contMDiff ∧
      e.hom ≫ modelCleanupMap p hthin E₁ = modelCleanupMap p hthin E₀ ∧
      e.hom ≫ (modelCleanupMap p hthin E₁ ≫ p) = modelCleanupMap p hthin E₀ ≫ p ∧
      e.hom.hom.left.base ⁻¹'
          ((modelCleanupMap p hthin E₁ ≫ p).hom.left.base ⁻¹' intrinsicRegularLocus X.obj) =
        (modelCleanupMap p hthin E₀ ≫ p).hom.left.base ⁻¹' intrinsicRegularLocus X.obj ∧
      GermIdeal.pullback (m := n₀) η (modelTotalIdeal p hthin E₁) =
        modelTotalIdeal p hthin E₀ := by
  have hn := nativeModel_dimension_eq E₀ E₁
  cases hn
  let eM := E₀.trans E₁.symm
  let f := nativeDiffeomorph (isoLeft eM) (Over.w eM.hom.hom)
  let A₀ := modelMarkedIdeal p E₀
  let A₁ := modelMarkedIdeal p E₁
  let hA₀ := modelMarkedDomain p hthin E₀
  let hA₁ := modelMarkedDomain p hthin E₁
  have ha : eM.hom ≫ (E₁.hom ≫ p) = E₀.hom ≫ p := by
    simp only [eM, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  have hI := originalSingularGermIdeal_transport X eM (E₁.hom ≫ p)
  rw [ha] at hI
  have hrecord : A₀ = markedPullback (m := n₀) f A₁ := by
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · change univ = f ⁻¹' (univ : Set M₁)
      rw [preimage_univ]
    · rfl
    · exact hI
    · rfl
  let η := originalTerminalMarkedRecordIso f A₁ hA₁ A₀ hA₀ hrecord
  let e := nativeWholeIso η
  have hproj : nativeMorphism η.contMDiff ≫
      nativeMorphism (originalTerminalGluedProjection_contMDiff A₁ hA₁) =
      nativeMorphism (originalTerminalGluedProjection_contMDiff A₀ hA₀) ≫ eM.hom := by
    apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
    intro z
    apply Subtype.ext
    exact originalTerminalMarkedRecordIso_proj f A₁ hA₁ A₀ hA₀ hrecord z.val
  have hY : e.hom ≫ modelCleanupMap p hthin E₁ = modelCleanupMap p hthin E₀ := by
    change nativeMorphism η.contMDiff ≫
      (nativeMorphism (originalTerminalGluedProjection_contMDiff A₁ hA₁) ≫ E₁.hom) =
        nativeMorphism (originalTerminalGluedProjection_contMDiff A₀ hA₀) ≫ E₀.hom
    rw [← Category.assoc, hproj, Category.assoc]
    simp only [eM, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  have hX : e.hom ≫ (modelCleanupMap p hthin E₁ ≫ p) = modelCleanupMap p hthin E₀ ≫ p := by
    rw [← Category.assoc, hY]
  have hreg : e.hom.hom.left.base ⁻¹'
        ((modelCleanupMap p hthin E₁ ≫ p).hom.left.base ⁻¹' intrinsicRegularLocus X.obj) =
      (modelCleanupMap p hthin E₀ ≫ p).hom.left.base ⁻¹' intrinsicRegularLocus X.obj := by
    ext z
    have hz := congrArg
      (fun g : wholeModel (n := n₀) (modelTerminal p hthin E₀) ⟶ X => g.hom.left.base z) hX
    change (modelCleanupMap p hthin E₁ ≫ p).hom.left.base (e.hom.hom.left.base z) =
      (modelCleanupMap p hthin E₀ ≫ p).hom.left.base z at hz
    exact iff_of_eq (congrArg (fun x => x ∈ intrinsicRegularLocus X.obj) hz)
  refine ⟨η, e, rfl, hY, hX, hreg, ?_⟩
  exact originalTerminalMarkedRecordIso_wholeIdeal f A₁ hA₁ A₀ hA₀ hrecord

/-- A genuine resolution supplies the needed thinness internally.  No model,
whole-record, whole-ideal or terminal-comparison equality is assumed. -/
theorem exists_cleanup_model_comparison [Nonempty Y.obj.left]
    (hp : IsResolution p)
    {n₀ n₁ : ℕ} {M₀ : CMfd.{0} n₀} {M₁ : CMfd.{0} n₁}
    (E₀ : wholeModel (n := n₀) M₀ ≅ Y) (E₁ : wholeModel (n := n₁) M₁ ≅ Y) :
    ∃ (hthin : interior (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj) = ∅)
      (η : modelTerminal p hthin E₀
        ≃ₘ⟮𝓘(ℂ, ComplexModel n₀), 𝓘(ℂ, ComplexModel n₁)⟯ modelTerminal p hthin E₁)
      (e : wholeModel (n := n₀) (modelTerminal p hthin E₀) ≅
        wholeModel (n := n₁) (modelTerminal p hthin E₁)),
      e.hom = nativeMorphism η.contMDiff ∧
      e.hom ≫ modelCleanupMap p hthin E₁ = modelCleanupMap p hthin E₀ ∧
      e.hom ≫ (modelCleanupMap p hthin E₁ ≫ p) = modelCleanupMap p hthin E₀ ≫ p ∧
      e.hom.hom.left.base ⁻¹'
          ((modelCleanupMap p hthin E₁ ≫ p).hom.left.base ⁻¹' intrinsicRegularLocus X.obj) =
        (modelCleanupMap p hthin E₀ ≫ p).hom.left.base ⁻¹' intrinsicRegularLocus X.obj ∧
      GermIdeal.pullback (m := n₀) η (modelTotalIdeal p hthin E₁) =
        modelTotalIdeal p hthin E₀ := by
  obtain ⟨_, Z, _, _, hpre, hiso⟩ := hp.2
  have hthin := hiso.interior_preimage_eq_empty hpre
    (interior_intrinsicSingularLocus_eq_empty X)
  exact ⟨hthin, exists_cleanup_model_comparison_of_thin p hthin E₀ E₁⟩

end
end Hironaka.Analytic.Unibranch.HironakaG1NativeCleanupModelIndependence
