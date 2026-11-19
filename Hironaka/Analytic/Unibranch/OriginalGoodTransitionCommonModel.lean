import Hironaka.Analytic.Unibranch.OriginalCommonResolution
import Hironaka.Analytic.Unibranch.OriginalNativeModification

/-!
# ORIGINAL common-model output from actual paired-component geometry

Component maps to the WHOLE target need not themselves be modifications.
Actual original E0/E1 and genuine native good data internally produce the
analytic sets, real common model, ORIGINAL modifications and full square.
Blueprint FIRST: `original-good-transition-common-model.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
  Hironaka.ProductComplexManifold

namespace Hironaka.Analytic.Unibranch.OriginalGoodTransitionCommonModel

open Hironaka Hironaka
  HironakaActualAnalyticSubspace HironakaReducedComplexAnalyticSpaces
  SourceReducedComplexSpace OriginalNativeModification OriginalSmoothSourceAnalytic

noncomputable section

variable {n : ℕ} {X : SourceReducedComplexSpace} {M₀ M₁ : Type}
  [TopologicalSpace M₀] [ChartedSpace (ComplexModel n) M₀] [IsComplexManifold n M₀]
  [TopologicalSpace M₁] [ChartedSpace (ComplexModel n) M₁] [IsComplexManifold n M₁]
  [CompactSpace M₀] [CompactSpace M₁] [ConnectedSpace M₁]

/-- Ordinary genuine native good data and actual ORIGINAL exceptional sets
derive real ORIGINAL output maps; no modification of component Fi assumed. -/
theorem exists_original_common_model_of_good_transition
    (F₀ : wholeModel (n := n) M₀ ⟶ X) (F₁ : wholeModel (n := n) M₁ ⟶ X)
    (E₀ E₁ : Set X.obj.left) (hE₀ : X.IsAnalyticSubset E₀) (hE₁ : X.IsAnalyticSubset E₁)
    (hthin₀ : interior (pointMap F₀ ⁻¹' (E₀ ∪ E₁)) = ∅)
    (hthin₁ : interior (pointMap F₁ ⁻¹' (E₀ ∪ E₁)) = ∅)
    (e : OriginalCommonResolution.goodOpen F₁ (E₀ ∪ E₁) (hE₀.isClosed.union hE₁.isClosed)
      ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
        OriginalCommonResolution.goodOpen F₀ (E₀ ∪ E₁) (hE₀.isClosed.union hE₁.isClosed))
    (he : ∀ y, pointMap F₀ (e y).val = pointMap F₁ y.val)
    (hinj : InjOn (pointMap F₀) (pointMap F₀ ⁻¹' (E₀ ∪ E₁)ᶜ)) :
    ∃ (Z : SourceReducedComplexSpace) (_ : CompactSpace Z.obj.left),
      Z.IsSmooth ∧ ∃ (g₀ : Z ⟶ wholeModel (n := n) M₀) (g₁ : Z ⟶ wholeModel (n := n) M₁),
        IsProperBimeromorphic g₀ ∧ IsProperBimeromorphic g₁ ∧ g₀ ≫ F₀ = g₁ ≫ F₁ := by
  have hBc : IsClosed (E₀ ∪ E₁) := hE₀.isClosed.union hE₁.isClosed
  have hA₀ : IsComplexAnalyticSubset (n := n) (pointMap F₀ ⁻¹' (E₀ ∪ E₁)) := by
    rw [preimage_union]
    exact ConstantRankImage.IsComplexAnalyticSubset.union
      (isComplexAnalyticSubset_preimage F₀ hE₀) (isComplexAnalyticSubset_preimage F₀ hE₁)
  have hA₁ : IsComplexAnalyticSubset (n := n) (pointMap F₁ ⁻¹' (E₀ ∪ E₁)) := by
    rw [preimage_union]
    exact ConstantRankImage.IsComplexAnalyticSubset.union
      (isComplexAnalyticSubset_preimage F₁ hE₀) (isComplexAnalyticSubset_preimage F₁ hE₁)
  obtain ⟨Z, instTop, instChart, instMfd, instConn, instCompact, g₀, g₁, hg₀, hg₁, hbase⟩ :=
    HironakaNativeTargetCommon.exists_compact_smooth_common_model
      (continuous_pointMap F₀) (continuous_pointMap F₁) hBc
      (isComplexAnalyticSubset_equalityLocus F₀ F₁) hA₀ hA₁ hthin₀ hthin₁ e he hinj
  let W := wholeModel (n := n) Z
  let G₀ : W ⟶ wholeModel (n := n) M₀ := nativeMorphism hg₀.1
  let G₁ : W ⟶ wholeModel (n := n) M₁ := nativeMorphism hg₁.1
  have hcpt : CompactSpace W.obj.left := isCompact_iff_compactSpace.mp isCompact_univ
  refine ⟨W, hcpt, isSmooth_wholeModel, G₀, G₁,
    nativeMorphism_isProperBimeromorphic hg₀, nativeMorphism_isProperBimeromorphic hg₁, ?_⟩
  exact SourceReducedComplexSpace.morphism_eq_of_pointwise_eq (G₀ ≫ F₀) (G₁ ≫ F₁)
    (fun z => congrFun hbase z.val)

end

end Hironaka.Analytic.Unibranch.OriginalGoodTransitionCommonModel
