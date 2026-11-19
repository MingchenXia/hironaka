import Hironaka.Analytic.Unibranch.EmbeddedBlowupOverlap

/-!
# Full ORIGINAL uniqueness of the actual overlap maps

The source is a literal original open of the given analytic strict transform.
Native charts are DERIVED on that concrete source open. The common original
complex space X has no added global countability or embedding hypothesis.
Blueprint: `embedded-blowup-overlap-unique.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace Topology CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.EmbeddedBlowupOverlapUnique

open Hironaka Hironaka.BlowupSequences
  Hironaka HironakaActualAnalyticSubspace
  HironakaReducedComplexAnalyticSpaces HironakaResolutionSpaceComplex
  HironakaSingularSubspaceBlowupLift HironakaIntrinsicMorphismGluingAnalytic
  HironakaSingularSubspaceBlowupCartierUniversalGlobal SourceReducedComplexSpace
  EmbeddedBlowup EmbeddedBlowupOpenRestriction EmbeddedBlowupOverlap

noncomputable section

variable {X : SourceReducedComplexSpace}

/-- The actual full over-X map is unique on ANY genuine open source of a
local strict-transform model. The source's native charts/density are DERIVED
from that original open immersion; no source chart/countability certificate. -/
theorem raw_hom_ext_of_original_projection_eq (e f : LocalEmbedding X)
    {Y₀ Y₁ : Type} [TopologicalSpace Y₀] [TopologicalSpace Y₁]
    [ChartedSpace (ComplexModel e.dim) Y₀] [IsComplexManifold e.dim Y₀]
    [ChartedSpace (ComplexModel f.dim) Y₁] [IsComplexManifold f.dim Y₁]
    {C : Set e.ambient} {D : Set f.ambient} {π₀ : Y₀ → e.ambient} {π₁ : Y₁ → f.ambient}
    (hπ₀ : IsBlowupAlong e.dim C π₀) (hπ₁ : IsBlowupAlong f.dim D π₁)
    (hd₀ : e.carrier ⊆ closure (e.carrier \ C)) {Z : Set X.obj.left}
    (hC : ∀ x : e.carrier, x.val ∈ C ↔ e.toPoint x ∈ Z)
    (hD : ∀ x : f.carrier, x.val ∈ D ↔ f.toPoint x ∈ Z)
    {A : LocallyRingedSpace}
    (r : A ⟶ actualSubspaceLocallyRingedSpace (n := e.dim)
      (strictTransform e.dim π₀ e.carrier)) [LocallyRingedSpace.IsOpenImmersion r]
    (L₁ L₂ : A ⟶ actualSubspaceLocallyRingedSpace (n := f.dim)
      (strictTransform f.dim π₁ f.carrier))
    (hL₁ : L₁ ≫ strictTransformProjection hπ₁ f.analytic.isClosed ≫ f.map =
      r ≫ strictTransformProjection hπ₀ e.analytic.isClosed ≫ e.map)
    (hL₂ : L₂ ≫ strictTransformProjection hπ₁ f.analytic.isClosed ≫ f.map =
      r ≫ strictTransformProjection hπ₀ e.analytic.isClosed ≫ e.map) : L₁ = L₂ := by
  let p₀ := strictTransformProjection hπ₀ e.analytic.isClosed
  let p₁ := strictTransformProjection hπ₁ f.analytic.isClosed
  let F := L₁ ≫ p₁
  have hproj : L₁ ≫ p₁ = L₂ ≫ p₁ := by
    let : LocallyRingedSpace.IsOpenImmersion f.map := f.isOpenImmersion
    apply (cancel_mono f.map).mp
    simpa only [Category.assoc] using hL₁.trans hL₂.symm
  have hdA : Dense {x : A | ((r ≫ p₀).base x).val ∉ C} :=
    (dense_preimage_compl_centre hπ₀ e.analytic.isClosed hd₀).preimage
      (inferInstance : LocallyRingedSpace.IsOpenImmersion r).base_open.isOpenMap
  have hset : {x : A | (F.base x).val ∉ D} =
      {x : A | ((r ≫ p₀).base x).val ∉ C} := by
    ext x
    have hp : f.toPoint (F.base x) = e.toPoint ((r ≫ p₀).base x) :=
      congrArg (fun H => H.base x) hL₁
    exact not_congr ((hD (F.base x)).trans
      ((iff_of_eq (congrArg (fun y => y ∈ Z) hp)).trans (hC ((r ≫ p₀).base x)).symm))
  have hdF : Dense {x : A | (F.base x).val ∉ D} := by
    rw [hset]
    exact hdA
  have hbase : L₁.base = L₂.base :=
    base_eq_of_dense_projection_eq hπ₁ f.analytic.isClosed F hdF L₁ L₂ rfl hproj.symm
  have hS := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
    hπ₀ e.analytic
  have hSc : hasAnalyticCharts (Over.mk (subspacePointMap (n := e.dim)
      (strictTransform e.dim π₀ e.carrier))) := by
    refine ⟨?_, ?_, fun x => ⟨e.dim, exists_model_chart hS x⟩⟩
    · change T2Space (strictTransform e.dim π₀ e.carrier)
      infer_instance
    · change SecondCountableTopology (strictTransform e.dim π₀ e.carrier)
      infer_instance
  let σA := r ≫ subspacePointMap (n := e.dim) (strictTransform e.dim π₀ e.carrier)
  have hAc : hasAnalyticCharts (Over.mk σA) :=
    hasAnalyticCharts_of_openImmersion _ _ hSc r rfl
  have hp₀ : p₀ ≫ e.map ≫ X.obj.hom =
      subspacePointMap (n := e.dim) (strictTransform e.dim π₀ e.carrier) := by
    rw [e.overPoint]
    exact strictTransformProjection_point hπ₀ e.analytic.isClosed
  have hp₁ : p₁ ≫ f.map ≫ X.obj.hom =
      subspacePointMap (n := f.dim) (strictTransform f.dim π₁ f.carrier) := by
    rw [f.overPoint]
    exact strictTransformProjection_point hπ₁ f.analytic.isClosed
  have hσ (L : A ⟶ actualSubspaceLocallyRingedSpace (n := f.dim)
      (strictTransform f.dim π₁ f.carrier))
      (hL : L ≫ p₁ ≫ f.map = r ≫ p₀ ≫ e.map) :
      L ≫ subspacePointMap (n := f.dim) (strictTransform f.dim π₁ f.carrier) = σA := by
    calc
      _ = L ≫ (p₁ ≫ f.map ≫ X.obj.hom) := congrArg (fun t => L ≫ t) hp₁.symm
      _ = (L ≫ p₁ ≫ f.map) ≫ X.obj.hom := by simp only [Category.assoc]
      _ = (r ≫ p₀ ≫ e.map) ≫ X.obj.hom := congrArg (fun t => t ≫ X.obj.hom) hL
      _ = r ≫ (p₀ ≫ e.map ≫ X.obj.hom) := by simp only [Category.assoc]
      _ = σA := congrArg (fun t => r ≫ t) hp₀
  exact morphism_eq_of_base_eq σA hAc L₁ L₂ (hσ L₁ hL₁) (hσ L₂ hL₂) hbase

/-- On a literal original source open, the SAME original projection to X
determines the ENTIRE map into any other local blowup model. Native source
charts/density and target off-centre injectivity are all internally derived. -/
theorem hom_ext_of_original_projection_eq (e f : LocalEmbedding X)
    {Y₀ Y₁ : Type} [TopologicalSpace Y₀] [TopologicalSpace Y₁]
    [ChartedSpace (ComplexModel e.dim) Y₀] [IsComplexManifold e.dim Y₀]
    [ChartedSpace (ComplexModel f.dim) Y₁] [IsComplexManifold f.dim Y₁]
    {C : Set e.ambient} {D : Set f.ambient} {π₀ : Y₀ → e.ambient} {π₁ : Y₁ → f.ambient}
    (hπ₀ : IsBlowupAlong e.dim C π₀) (hπ₁ : IsBlowupAlong f.dim D π₁)
    (hd₀ : e.carrier ⊆ closure (e.carrier \ C)) {Z : Set X.obj.left}
    (hC : ∀ x : e.carrier, x.val ∈ C ↔ e.toPoint x ∈ Z)
    (hD : ∀ x : f.carrier, x.val ∈ D ↔ f.toPoint x ∈ Z)
    (U : Opens (strictTransform e.dim π₀ e.carrier))
    (L₁ L₂ : restrictedClosedAnalytic
        (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
          hπ₀ e.analytic) U ⟶
      ofClosedAnalytic (strictTransform f.dim π₁ f.carrier)
        (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
          hπ₁ f.analytic))
    (hL₁ : L₁ ≫ strictTransformMorphism hπ₁ f.analytic ≫ chartMorphism f =
      restrictionInclusion
        (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
          hπ₀ e.analytic) U ≫ strictTransformMorphism hπ₀ e.analytic ≫ chartMorphism e)
    (hL₂ : L₂ ≫ strictTransformMorphism hπ₁ f.analytic ≫ chartMorphism f =
      restrictionInclusion
        (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
          hπ₀ e.analytic) U ≫ strictTransformMorphism hπ₀ e.analytic ≫ chartMorphism e) :
    L₁ = L₂ := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact raw_hom_ext_of_original_projection_eq e f hπ₀ hπ₁ hd₀ hC hD
    (restrictionInclusion
      (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
        hπ₀ e.analytic) U).hom.left L₁.hom.left L₂.hom.left
    (congrArg (fun H => H.hom.left) hL₁) (congrArg (fun H => H.hom.left) hL₂)

/-- Actual original chart geometry gives the UNIQUE original overlap iso
over X, not just an arbitrary chosen transition satisfying a supplied cocycle. -/
theorem exists_unique_overlap_transition (e f : LocalEmbedding X)
    {Y₀ Y₁ : Type} [TopologicalSpace Y₀] [TopologicalSpace Y₁]
    [ChartedSpace (ComplexModel e.dim) Y₀] [IsComplexManifold e.dim Y₀]
    [ChartedSpace (ComplexModel f.dim) Y₁] [IsComplexManifold f.dim Y₁]
    {C : Set e.ambient} {D : Set f.ambient} {π₀ : Y₀ → e.ambient} {π₁ : Y₁ → f.ambient}
    (hπ₀ : IsBlowupAlong e.dim C π₀) (hπ₁ : IsBlowupAlong f.dim D π₁)
    (hCW : C ⊆ e.carrier) (hDW : D ⊆ f.carrier)
    (hd₀ : e.carrier ⊆ closure (e.carrier \ C))
    (hd₁ : f.carrier ⊆ closure (f.carrier \ D)) {Z : Set X.obj.left}
    (hC : ∀ x : e.carrier, x.val ∈ C ↔ e.toPoint x ∈ Z)
    (hD : ∀ x : f.carrier, x.val ∈ D ↔ f.toPoint x ∈ Z) :
    ∃! T : restrictedClosedAnalytic
          (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
            hπ₀ e.analytic) (projectionOpen hπ₀ e.analytic (overlapOpen e f)) ≅
        restrictedClosedAnalytic
          (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
            hπ₁ f.analytic) (projectionOpen hπ₁ f.analytic (overlapOpen f e)),
      T.hom ≫ restrictionInclusion
          (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
            hπ₁ f.analytic) (projectionOpen hπ₁ f.analytic (overlapOpen f e)) ≫
            strictTransformMorphism hπ₁ f.analytic ≫ chartMorphism f =
        restrictionInclusion
          (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
            hπ₀ e.analytic) (projectionOpen hπ₀ e.analytic (overlapOpen e f)) ≫
            strictTransformMorphism hπ₀ e.analytic ≫ chartMorphism e := by
  obtain ⟨T, hT⟩ := exists_overlap_transition e f hπ₀ hπ₁ hCW hDW hd₀ hd₁ hC hD
  refine ⟨T, hT, ?_⟩
  intro T' hT'
  have heq := hom_ext_of_original_projection_eq e f hπ₀ hπ₁ hd₀ hC hD
    (projectionOpen hπ₀ e.analytic (overlapOpen e f))
    (T'.hom ≫ restrictionInclusion
      (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
        hπ₁ f.analytic) (projectionOpen hπ₁ f.analytic (overlapOpen f e)))
    (T.hom ≫ restrictionInclusion
      (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
        hπ₁ f.analytic) (projectionOpen hπ₁ f.analytic (overlapOpen f e)))
    (by simpa only [Category.assoc] using hT') (by simpa only [Category.assoc] using hT)
  apply Iso.ext
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_mono (restrictionInclusion
    (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
      hπ₁ f.analytic) (projectionOpen hπ₁ f.analytic (overlapOpen f e))).hom.left).mp
  exact congrArg (fun H => H.hom.left) heq

end

end Hironaka.Analytic.Unibranch.EmbeddedBlowupOverlapUnique
