import Hironaka.Analytic.Unibranch.HironakaG10GlFlattenerAssembly
import Hironaka.Analytic.Unibranch.HironakaG10GlCanonicalBaseSquare
import Hironaka.Analytic.Unibranch.HironakaG10NfTargetChart

/-!
# N3 + N4 on the canonical charts: `isFlattenerIdeal_canonical` and `flat_base_canonical`

Lane G10N34, run 0081 (G10GL's split-off N3+N4; exact statements of `G10GL/STATUS.md`, "Splittable — N3+N4" and
"DELIVERED FORM of `flat_base`").  Canonical setting of `HironakaG10SbCanonicalStrictTorsion`.

* `target_square` — the target pivot strict chart of `Bl_B Y` over the graph chart of `Y`, read in the target product
  coordinates (from `TargetExplicitMapLaws.projection`);
* `source_square` — the source graph chart of `X` over the graph chart of `Y` (`CanonicalCompatibleSourceGraph.graph_square`);
* `canonical_core` — at a source chart point `w` of the fibre-product locus over a source graph point `γ`
  (`γ = π(χ w)`) and an old point `x₁ = c.chart γ`: every flattener of `F` at `x₁` is carried by `σ^♯` to the
  flattener of the joint base map, and flatness base-changes (`HironakaG10GlFlattenerAssembly.flattener_of_chart_data`
  with the coordinate inputs of `HironakaG10GlChartCoordinates`);
* **`isFlattenerIdeal_canonical`** — (for G10GL's `hpres`) at points on the strict transform;
* **`flat_base_canonical`** — (for G10H3) at the chart origin `w₀` over `c.point`.

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold

namespace Hironaka.Analytic.Unibranch.HironakaG10GlCanonicalFlattener

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaFiniteSectionProductGraph
  BlowupConstruction BlowupStrictSubmanifold
  Hironaka.Analytic.Unibranch.SourceReducedComplexSpace Hironaka.Analytic.Unibranch.OriginalFiniteIdealGraphChart
  Hironaka.Analytic.Unibranch.EmbeddedGeometricBlowup
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupSquareCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupNormalSections
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotOpenRanges
  Hironaka.Analytic.Unibranch.HironakaG10GlChartCoordinates

noncomputable section

/-- Actual subspace maps of equal maps agree. -/
theorem actualSubspaceMap_congr {n m : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N] {f₁ f₂ : M → N} (h : f₁ = f₂)
    (hf₁ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f₁)
    (hf₂ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f₂)
    {C : Set M} {D : Set N} (h₁ : ∀ x ∈ C, f₁ x ∈ D) (h₂ : ∀ x ∈ C, f₂ x ∈ D) :
    actualSubspaceMap hf₁ h₁ = actualSubspaceMap hf₂ h₂ := by
  subst h
  rfl

/-! ### The target side -/

section Target

variable {X : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
  {y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left}
  (t : CanonicalTargetGraph B b y) (e : TargetExplicitGeometry B b t) (j : Fin t.rank)

/-- The target strict chart read in the target product coordinates. -/
abbrev strictCoord : Set (productCoordinateOpen e.charts j) :=
  (productChartDiffeomorph e.charts j).symm ⁻¹' strictChartCarrier e.charts (HironakaG10NfTargetChart.graph B b t) j

theorem mem_strictCoord_iff (z : productChartOpen e.charts j) :
    z ∈ strictChartCarrier e.charts (HironakaG10NfTargetChart.graph B b t) j ↔
      productChartDiffeomorph e.charts j z ∈ strictCoord B b t e j := by
  simp only [strictCoord, Set.mem_preimage, Diffeomorph.symm_apply_apply]

theorem strictCoord_analytic :
    IsComplexAnalyticSubset (n := t.embedding.dim+t.rank) (strictCoord B b t e j) :=
  AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (productChartDiffeomorph e.charts j).symm.contMDiff
    (CompatibleCanonicalIdealBlowupOriginalPivotObjects.strict_chart_analytic e.charts t.positive
      (HironakaG10NfTargetChart.graph B b t) t.analytic j)

theorem coordProj_mem (p : productCoordinateOpen e.charts j) (hp : p ∈ strictCoord B b t e j) :
    coordProj e.charts j p ∈ HironakaG10NfTargetChart.graph B b t :=
  geoStrictTransform_subset_preimage contMDiff_blowupProj.continuous t.analytic.isClosed hp

/-- **The target chart square**: the pivot strict chart of `Bl_B Y` over the graph chart of `Y`, through the
product coordinates. -/
theorem target_square (d : CanonicalTargetNormalSectionData B b t) (hmap : TargetExplicitMapLaws B b t d e) :
    actualSubspaceMap ((coordProj_contMDiff e.charts j).comp (productChartDiffeomorph e.charts j).contMDiff)
        (fun z hz => coordProj_mem B b t e j _ ((mem_strictCoord_iff B b t e j z).mp hz)) ≫
      chartGraphMap t.embedding t.domain t.functions t.holomorphic =
    HironakaG10NfTargetChart.chartMap B b t e j ≫ (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left := by
  have hproj : HironakaG10NfTargetChart.nativeMap B b t e ≫
      (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left =
      geometricProjection (explicitProductPredicate (n := t.embedding.dim) (P := t.domain) t.positive)
          t.analytic.isClosed ≫ chartGraphMap t.embedding t.domain t.functions t.holomorphic :=
    congrArg (fun φ => φ.hom.left) hmap.projection
  have h1 : actualSubspaceMap ((coordProj_contMDiff e.charts j).comp (productChartDiffeomorph e.charts j).contMDiff)
      (fun z hz => coordProj_mem B b t e j _ ((mem_strictCoord_iff B b t e j z).mp hz)) =
      strictChartInclusion e.charts (HironakaG10NfTargetChart.graph B b t) j ≫
        geometricProjection (explicitProductPredicate (n := t.embedding.dim) (P := t.domain) t.positive)
          t.analytic.isClosed := by
    change _ = actualSubspaceMap _ _ ≫ actualSubspaceMap _ _
    rw [← actualSubspaceMap_comp]
    apply actualSubspaceMap_congr
    funext z
    change blowupProj (t.embedding.dim+t.rank) {q : t.domain × ComplexModel t.rank | q.2 = 0}
        ((productChartDiffeomorph e.charts j).symm (productChartDiffeomorph e.charts j z)).val = _
    rw [Diffeomorph.symm_apply_apply]
    rfl
  rw [h1, Category.assoc, ← hproj]
  rfl

end Target

/-! ### The source side -/

section Source

variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType] (F : X ⟶ Y) (x : X.obj.left)
  {y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left}
  (t : CanonicalTargetGraph B b y) (c : CanonicalCompatibleSourceGraph B b F x t)

theorem srcGraph_maps : ∀ p ∈ sourceGraphSet B b F x t c,
    Prod.map c.baseMap id p ∈ targetGraphSet B b t := by
  rintro ⟨u, q⟩ ⟨hu, hq⟩
  exact ⟨c.landing hu, hq⟩

theorem srcGraph_holomorphic :
    ContMDiff 𝓘(ℂ, ComplexModel (c.embedding.dim+t.rank)) 𝓘(ℂ, ComplexModel (t.embedding.dim+t.rank)) ∞
      (Prod.map c.baseMap (id : ComplexModel t.rank → ComplexModel t.rank)) :=
  ProductComplexManifold.contMDiff_prodMap c.holomorphic contMDiff_id

/-- **The source chart square**: the source graph chart of `X` over the graph chart of `Y`. -/
theorem source_square :
    actualSubspaceMap (srcGraph_holomorphic B b F x t c) (srcGraph_maps B b F x t c) ≫
        chartGraphMap t.embedding t.domain t.functions t.holomorphic =
      c.chart.hom.left ≫ F.hom.left :=
  congrArg (fun φ => φ.hom.left) c.graph_square

end Source

/-- Whole chart stalk ideals at equal points agree. -/
theorem wholeChartStalkIdeal_congr {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] (A : HolomorphicIdealSheaves.GermIdeal n M) {p₁ p₂ : M} (h : p₁ = p₂) :
    HironakaHolomorphicJetRankLoci.wholeChartStalkIdeal A p₁ p₁ (mem_chart_source _ p₁) =
      HironakaHolomorphicJetRankLoci.wholeChartStalkIdeal A p₂ p₂ (mem_chart_source _ p₂) := by
  subst h
  rfl

/-! ### The monomial-lift level -/

section MonomialLevel

open HironakaG10ArbitraryBaseRecenter HironakaG10ArbitraryBaseStrict HironakaRealOpenGeometricStrictSaturation
  HironakaG10JointStrictTorsion HironakaG10JointNativeScalar HironakaActualWholeStalkHolomorphicPullback
  HironakaG10HirFlatQuotient HironakaActualCentreJointJets
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalRecenteredChart Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryBaseChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalCoordinateStrict Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryStrictConjugacy
  Hironaka.Analytic.Unibranch.HironakaG10GlChartPresentation Hironaka.Analytic.Unibranch.HironakaG10GlFlattenerTransfer
  Hironaka.Analytic.Unibranch.HironakaG10GlFlattenerAssembly

variable {n m r : ℕ} {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
  [ChartedSpace (ComplexModel n) P] [IsComplexManifold n P]
  [ChartedSpace (ComplexModel m) Q] [IsComplexManifold m Q]
  (a : ProductNormalCharts n r P) (b : ProductNormalCharts m r Q) {f : P → Q}
  (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
  (L : BlowupSpace (n+r) {q : P × ComplexModel r | q.2 = 0} → BlowupSpace (m+r) {q : Q × ComplexModel r | q.2 = 0})
  (hL : ContMDiff 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel (m+r)) ∞ L)
  (hπ : blowupProj (m+r) {q : Q × ComplexModel r | q.2 = 0} ∘ L =
    Prod.map f id ∘ blowupProj (n+r) {q : P × ComplexModel r | q.2 = 0})
  (M : MonomialLiftLaws a b hf L hL hπ) (j : Fin r) (v : ComplexModel (n+r)) (hvj : v (j.natAdd n) = 0)

theorem coordProj_chart (z : productChartOpen b j) :
    coordProj b j (productChartDiffeomorph b j z) = blowupProj (m+r) {q : Q × ComplexModel r | q.2 = 0} z.val := by
  unfold coordProj
  rw [Diffeomorph.symm_apply_apply]

/-- The strict chart, read in the product coordinates. -/
abbrev strictCoord' (DY : Set (Q × ComplexModel r)) : Set (productCoordinateOpen b j) :=
  (productChartDiffeomorph b j).symm ⁻¹' strictChartCarrier b DY j

theorem mem_strictCoord'_iff (DY : Set (Q × ComplexModel r)) (z : productChartOpen b j) :
    z ∈ strictChartCarrier b DY j ↔ productChartDiffeomorph b j z ∈ strictCoord' b j DY := by
  simp only [strictCoord', Set.mem_preimage, Diffeomorph.symm_apply_apply]

theorem coordProj_mem' {DY : Set (Q × ComplexModel r)} (hDY : IsClosed DY) (p : productCoordinateOpen b j)
    (hp : p ∈ strictCoord' b j DY) : coordProj b j p ∈ DY :=
  geoStrictTransform_subset_preimage contMDiff_blowupProj.continuous hDY hp

variable (hP : ∀ p p' : P, chartAt (ComplexModel n) p = chartAt (ComplexModel n) p')
  (hQ : ∀ q q' : Q, chartAt (ComplexModel m) q = chartAt (ComplexModel m) q')
  {CX : Set (P × ComplexModel r)} (hCX : IsComplexAnalyticSubset (n := n+r) CX)
  {DY : Set (Q × ComplexModel r)} (hDY : IsComplexAnalyticSubset (n := m+r) DY) (hr : 0 < r)
  (hCD : ∀ p ∈ CX, Prod.map f id p ∈ DY)
  {Xs Ys Bl : LocallyRingedSpace.{0}}
  (iC : actualSubspaceLocallyRingedSpace (n := n+r) CX ⟶ Xs) [LocallyRingedSpace.IsOpenImmersion iC]
  (iD : actualSubspaceLocallyRingedSpace (n := m+r) DY ⟶ Ys) [LocallyRingedSpace.IsOpenImmersion iD]
  (Fm : Xs ⟶ Ys)
  (hsqX : actualSubspaceMap (ProductComplexManifold.contMDiff_prodMap hf contMDiff_id) hCD ≫ iD = iC ≫ Fm)
  (tcm : actualSubspaceLocallyRingedSpace (n := m+r) (strictChartCarrier b DY j) ⟶ Bl)
  [LocallyRingedSpace.IsOpenImmersion tcm] (σm : Bl ⟶ Ys)
  (hsqT : actualSubspaceMap ((coordProj_contMDiff b j).comp (productChartDiffeomorph b j).contMDiff)
      (fun z hz => coordProj_mem' b j hDY.isClosed _ ((mem_strictCoord'_iff b j DY z).mp hz)) ≫ iD = tcm ≫ σm)
  (w : realOpenChartDomain n r j (fun i => v i) (recenteredTargetOpen n r j v (canonicalTargetOpen a j)))
  (hwV : (monomialLiftOnChart a b hf L hL hπ j ∘ arbitraryCanonicalRecenteredChart a j v hvj) w ∈
    strictChartCarrier b DY j)
  (γ : CX) (hγ : γ.val = blowupProj (n+r) {q : P × ComplexModel r | q.2 = 0}
    (arbitraryCanonicalRecenteredChart a j v hvj w).val)
  (x₁ : Xs) (hx₁ : iC.base γ = x₁)
  (hbase : Fm.base x₁ = σm.base (tcm.base ⟨(monomialLiftOnChart a b hf L hL hπ j ∘
    arbitraryCanonicalRecenteredChart a j v hvj) w, hwV⟩))

include M hP hQ hCX hr hsqX hsqT hγ hx₁ in
/-- **N3+N4 at the monomial-lift level**: the flattener transport for the joint chart family of a monomial lift. -/
theorem flattener_of_monomial_lift :
    (∀ P₀ : Ideal (Ys.presheaf.stalk (Fm.base x₁)), IsFlattenerIdeal (lrsFibreMap Fm (Fm.base x₁) x₁ rfl) P₀ →
      IsFlattenerIdeal ((targetStalkToJoint (n := m+r) n r j (fun i => v i)
          (recenteredTargetOpen n r j v (canonicalTargetOpen a j))
          ((arbitraryBaseTargetMap n r j v (canonicalTargetOpen a j)) ⁻¹' coordinateSubset a j CX)
          (monomialLiftOnChart a b hf L hL hπ j ∘ arbitraryCanonicalRecenteredChart a j v hvj)
          (strictChartCarrier b DY j)
          ((M.restricted_holomorphic j).comp (arbitraryCanonicalRecenteredChart a j v hvj).contMDiff)
          (CompatibleCanonicalIdealBlowupOriginalPivotObjects.strict_chart_analytic b hr DY hDY j) w hwV).comp
          (tcm.stalkMap ⟨_, hwV⟩).hom)
        (P₀.map (lrsFibreMap σm (Fm.base x₁) (tcm.base ⟨_, hwV⟩) hbase.symm))) ∧
    (∀ J₀ : Ideal (Ys.presheaf.stalk (Fm.base x₁)), (quotMap (lrsFibreMap Fm (Fm.base x₁) x₁ rfl) J₀).Flat →
      (quotMap ((targetStalkToJoint (n := m+r) n r j (fun i => v i)
          (recenteredTargetOpen n r j v (canonicalTargetOpen a j))
          ((arbitraryBaseTargetMap n r j v (canonicalTargetOpen a j)) ⁻¹' coordinateSubset a j CX)
          (monomialLiftOnChart a b hf L hL hπ j ∘ arbitraryCanonicalRecenteredChart a j v hvj)
          (strictChartCarrier b DY j)
          ((M.restricted_holomorphic j).comp (arbitraryCanonicalRecenteredChart a j v hvj).contMDiff)
          (CompatibleCanonicalIdealBlowupOriginalPivotObjects.strict_chart_analytic b hr DY hDY j) w hwV).comp
          (tcm.stalkMap ⟨_, hwV⟩).hom)
        (J₀.map (lrsFibreMap σm (Fm.base x₁) (tcm.base ⟨_, hwV⟩) hbase.symm))).Flat) := by
  have hbaseγ : (arbitraryCanonicalRecenteredChart a j v hvj w).val.base = γ.val := hγ.symm
  have hdq : (actualSubspaceMap (coordProj_contMDiff b j)
        (fun p hp => coordProj_mem' b j hDY.isClosed p hp)).base
        ((biholoMap (productChartDiffeomorph b j) (strictChartCarrier b DY j) (strictCoord' b j DY)
          (mem_strictCoord'_iff b j DY)).base ⟨_, hwV⟩) =
      (actualSubspaceMap (ProductComplexManifold.contMDiff_prodMap hf contMDiff_id) hCD).base γ := by
    apply Subtype.ext
    change coordProj b j (productChartDiffeomorph b j
      (monomialLiftOnChart a b hf L hL hπ j (arbitraryCanonicalRecenteredChart a j v hvj w))) = Prod.map f id γ.val
    rw [coordProj_chart, hγ]
    exact congrFun hπ (arbitraryCanonicalRecenteredChart a j v hvj w).val
  have hPsi := translated_liftMap a b hf L hL hπ M j v hvj hP hQ w
  rw [hbaseγ] at hPsi
  have hnp : actualJointNormalProjection m r
      (productChartDiffeomorph b j ((monomialLiftOnChart a b hf L hL hπ j ∘
        arbitraryCanonicalRecenteredChart a j v hvj) w)).val =
      actualJointNormalProjection n r (w.val + v) := by
    have h := liftMap_val a b hf L hL hπ M j v hvj w
    change actualJointNormalProjection m r (liftMap a b hf L hL hπ j v hvj w).val = _
    rw [h, ← prodModelEquiv_symm_snd', ContinuousLinearEquiv.symm_apply_apply]
  have hφ := translated_coordProj b j hQ (productChartDiffeomorph b j ((monomialLiftOnChart a b hf L hL hπ j ∘
    arbitraryCanonicalRecenteredChart a j v hvj) w))
  rw [hnp] at hφ
  have hJ : sourceIdealAt n r j (fun i => v i) (recenteredTargetOpen n r j v (canonicalTargetOpen a j))
      ((arbitraryBaseTargetMap n r j v (canonicalTargetOpen a j)) ⁻¹' coordinateSubset a j CX) w =
      chartIdealAt (k := n+r) CX γ := by
    refine (stalkIdeal_originalGraph a j v CX hP
      (realOpenProjection n r j (fun i => v i) (recenteredTargetOpen n r j v (canonicalTargetOpen a j)) w)).trans ?_
    apply wholeChartStalkIdeal_congr
    have h1 := recentered_projection_arbitrary_tangent n r j v hvj w.val
    have h2 := recentredChart_base a j v hvj w
    change (chartAt (ComplexModel (n+r)) ((a.base, 0) : P × ComplexModel r)).symm
      (HironakaActualAnalyticBlowupTaylor.actualAnalyticBlowupMap
        (HironakaActualCoefficientPresentationCentrePower.actualTangentCentreVariables n r)
        (j.natAdd n) (fun i => v i) w.val + BlowupMonomialCharts.monomial n (j.natAdd n) v) = γ.val
    rw [← h1, ← h2, hbaseγ]
  exact flattener_of_chart_data (ProductComplexManifold.contMDiff_prodMap hf contMDiff_id) hCD iC iD Fm hsqX
    (productChartDiffeomorph b j) (strictChartCarrier b DY j) (strictCoord' b j DY) (mem_strictCoord'_iff b j DY)
    (coordProj_contMDiff b j) (fun p hp => coordProj_mem' b j hDY.isClosed p hp) tcm σm hsqT j (fun i => v i)
    (recenteredTargetOpen n r j v (canonicalTargetOpen a j))
    ((arbitraryBaseTargetMap n r j v (canonicalTargetOpen a j)) ⁻¹' coordinateSubset a j CX)
    (monomialLiftOnChart a b hf L hL hπ j ∘ arbitraryCanonicalRecenteredChart a j v hvj)
    ((M.restricted_holomorphic j).comp (arbitraryCanonicalRecenteredChart a j v hvj).contMDiff)
    (Hironaka.Analytic.Unibranch.HironakaG10CanonicalCoordinateAnalytic.recenteredCoordinateSubset_analytic a j v CX hCX)
    (CompatibleCanonicalIdealBlowupOriginalPivotObjects.strict_chart_analytic b hr DY hDY j)
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (productChartDiffeomorph b j).symm.contMDiff
      (CompatibleCanonicalIdealBlowupOriginalPivotObjects.strict_chart_analytic b hr DY hDY j))
    w hwV γ x₁ hx₁ hbase hdq
    (actualTranslatedMap (n := m) (m := n) f γ.val.1) (actualTranslatedMap_holomorphic hf γ.val.1)
    (actualTranslatedMap_zero f γ.val.1)
    (blowGerm r j (actualJointNormalProjection n r (w.val + v))) (blowGerm_differentiable r j _) (blowGerm_zero r j _)
    (translated_realOpenProjection n r j v hvj (recenteredTargetOpen n r j v (canonicalTargetOpen a j)) w)
    hPsi hφ (Filter.EventuallyEq.of_eq (funext fun z => actualTranslatedMap_prodMap f γ.val z)) hJ

/-- The source graph point under a chart point of the fibre-product locus is determined by its base point. -/
theorem graphPoint_eq {SX : Set P} {SY : Set Q} {gY : Q → ComplexModel r}
    (hwV : (monomialLiftOnChart a b hf L hL hπ j ∘ arbitraryCanonicalRecenteredChart a j v hvj) w ∈
      strictChartCarrier b (HironakaFiniteSectionProductGraph.productGraph SY gY) j)
    (hSY : IsClosed (HironakaFiniteSectionProductGraph.productGraph SY gY))
    (γ : HironakaFiniteSectionProductGraph.productGraph SX (gY ∘ f))
    (h1 : (blowupProj (n+r) {q : P × ComplexModel r | q.2 = 0}
      (arbitraryCanonicalRecenteredChart a j v hvj w).val).1 = γ.val.1) :
    γ.val = blowupProj (n+r) {q : P × ComplexModel r | q.2 = 0} (arbitraryCanonicalRecenteredChart a j v hvj w).val := by
  have hmem := geoStrictTransform_subset_preimage contMDiff_blowupProj.continuous hSY hwV
  change blowupProj (m+r) {q : Q × ComplexModel r | q.2 = 0}
      (L (arbitraryCanonicalRecenteredChart a j v hvj w).val) ∈
        HironakaFiniteSectionProductGraph.productGraph SY gY at hmem
  rw [show blowupProj (m+r) {q : Q × ComplexModel r | q.2 = 0} (L (arbitraryCanonicalRecenteredChart a j v hvj w).val) =
    Prod.map f id (blowupProj (n+r) {q : P × ComplexModel r | q.2 = 0} (arbitraryCanonicalRecenteredChart a j v hvj w).val)
    from congrFun hπ _] at hmem
  apply Prod.ext h1.symm
  rw [γ.property.2, ← h1]
  exact hmem.2.symm

end MonomialLevel

/-! ### The source chart point -/

section SourcePoint

variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType] (F : X ⟶ Y) (x : X.obj.left)
  {y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left}

local instance : (nativePulledIdealModule F.hom.left B b).IsFiniteType :=
  HironakaNativePulledIdealFiniteType.nativePulledIdealModule_isFiniteType F.hom.left B b

variable (t : CanonicalTargetGraph B b y) (c : CanonicalCompatibleSourceGraph B b F x t)
  (g : CanonicalSquareGeometry B b F x t c) (e : SourceExplicitGeometry B b F x t c g)

/-- **The old point of a source strict chart point** is the chart image of its source graph point. -/
theorem source_chart_point (hsmap : SourceExplicitMapLaws B b F x t c g e) (j : Fin t.rank)
    (z : strictChartCarrier e.charts (sourceGraphSet B b F x t c) j)
    (hz : blowupProj (c.embedding.dim+t.rank) {q : c.subdomain × ComplexModel t.rank | q.2 = 0} z.val.val ∈
      sourceGraphSet B b F x t c) :
    (OriginalFiniteIdealGeometricBlowup.projectionMorphism (nativePulledIdealModule F.hom.left B b)
        (nativePulledIdealInclusion F.hom.left B b)).hom.left.base
      ((strictChartTo e.charts (sourceGraphSet B b F x t c) (sourceCanonicalMap B b F x t c g e).hom.left j).base z) =
    c.chart.hom.left.base ⟨_, hz⟩ :=
  congrArg (fun φ => φ.hom.left.base ((strictChartInclusion e.charts (sourceGraphSet B b F x t c) j).base z))
    hsmap.projection

end SourcePoint

/-! ### The canonical statements -/

section Canonical

open HironakaG10ArbitraryBaseRecenter HironakaG10ArbitraryBaseStrict HironakaRealOpenGeometricStrictSaturation
  HironakaG10JointStrictTorsion HironakaG10JointNativeScalar HironakaG10HirFlatQuotient
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialStrictRestriction
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalRecenteredChart Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryBaseChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalCoordinateStrict Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryStrictConjugacy
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalJointSaturation Hironaka.Analytic.Unibranch.HironakaG10SbCanonicalStrictTorsion
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease Hironaka.Analytic.Unibranch.HironakaG10GlChartPresentation

variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType] (F : X ⟶ Y) (x : X.obj.left)
  {y : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left}

local instance : (nativePulledIdealModule F.hom.left B b).IsFiniteType :=
  HironakaNativePulledIdealFiniteType.nativePulledIdealModule_isFiniteType F.hom.left B b

variable (t : CanonicalTargetGraph B b y)
  (c : CanonicalCompatibleSourceGraph B b F x t)
  (g : CanonicalSquareGeometry B b F x t c)
  (d : CanonicalNormalSectionData B b F x t c g)
  (E : SameCanonicalExplicitProductModels B b F x t c g d)
  (M : AllAmbientMonomialLiftData B b F x t c g d E)
  (j : Fin t.rank) (v : ComplexModel (c.embedding.dim+t.rank))
  (hvj : v (j.natAdd c.embedding.dim) = 0)

instance chart_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion c.chart.hom.left := c.chart_open

instance targetChartMap_isOpenImmersion' :
    LocallyRingedSpace.IsOpenImmersion (targetChartMap B b F x t c g d E j) := by
  have := E.target_maps.open_immersion
  exact HironakaG10NfTargetChart.chartMap_isOpenImmersion B b t E.target j

include M in
/-- **N3+N4 for `hpres`** (G10GL's exact statement): at a canonical chart point `w` on the strict transform, the
image of every pointed flattener `P` of `F` at the old point `π_S(np)` under the blowup stalk map is the flattener of
the joint base map `ψ`. -/
theorem isFlattenerIdeal_canonical (w : sourceDomain B b F x t c g d E j v)
    (hwS : w ∈ realOpenStrictTransform c.embedding.dim t.rank j (fun i => v i)
      (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v))
    (hbase : F.hom.left.base ((OriginalFiniteIdealGeometricBlowup.projectionMorphism
        (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base
          (nativePoint B b F x t c g d E j v hvj w hwS)) =
      (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base
        ((targetChartMap B b F x t c g d E j).base
          ⟨actualMap B b F x t c g d E j v hvj w, actual_landing B b F x t c g d E M j v hvj hwS⟩))
    (P : Ideal (Y.obj.left.presheaf.stalk (F.hom.left.base ((OriginalFiniteIdealGeometricBlowup.projectionMorphism
        (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base
          (nativePoint B b F x t c g d E j v hvj w hwS)))))
    (hP : IsPointFlattenerAt F (F.hom.left.base ((OriginalFiniteIdealGeometricBlowup.projectionMorphism
        (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base
          (nativePoint B b F x t c g d E j v hvj w hwS)))
      ((OriginalFiniteIdealGeometricBlowup.projectionMorphism
        (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base
          (nativePoint B b F x t c g d E j v hvj w hwS)) rfl P) :
    IsFlattenerIdeal
      ((targetStalkToJoint (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
          (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
          (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j)
          (actualMap_holomorphic B b F x t c g d E M j v hvj) (targetStrict_analytic B b F x t c g d E j) w
          (actual_landing B b F x t c g d E M j v hvj hwS)).comp
        ((targetChartMap B b F x t c g d E j).stalkMap
          ⟨actualMap B b F x t c g d E j v hvj w, actual_landing B b F x t c g d E M j v hvj hwS⟩).hom)
      (Ideal.map (((OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.stalkMap
          ((targetChartMap B b F x t c g d E j).base
            ⟨actualMap B b F x t c g d E j v hvj w, actual_landing B b F x t c g d E M j v hvj hwS⟩)).hom.comp
        (eqToHom (congrArg Y.obj.left.presheaf.stalk hbase)).hom) P) := by
  have hzS := (mem_strict_iff_chart B b F x t c g d E j v hvj w).mp hwS
  have hγmem : blowupProj (c.embedding.dim+t.rank) {q : c.subdomain × ComplexModel t.rank | q.2 = 0}
      (arbitraryCanonicalRecenteredChart E.source.charts j v hvj w).val ∈ sourceGraphSet B b F x t c :=
    geoStrictTransform_subset_preimage contMDiff_blowupProj.continuous c.analytic.isClosed hzS
  have hx₁ := (source_chart_point B b F x t c g E.source E.source_maps j
    ⟨arbitraryCanonicalRecenteredChart E.source.charts j v hvj w, hzS⟩ hγmem).symm
  exact (flattener_of_monomial_lift E.source.charts E.target.charts c.holomorphic
    (explicitAmbientLift B b F x t c g E.target E.source) E.square.holomorphic E.square.ambient_projection M j v hvj
    (fun _ _ => rfl) (fun _ _ => rfl) c.analytic t.analytic t.positive (srcGraph_maps B b F x t c)
    c.chart.hom.left (chartGraphMap t.embedding t.domain t.functions t.holomorphic) F.hom.left
    (source_square B b F x t c) (targetChartMap B b F x t c g d E j)
    (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left
    (target_square B b t E.target j d.target E.target_maps) w (actual_landing B b F x t c g d E M j v hvj hwS)
    ⟨_, hγmem⟩ rfl _ hx₁ hbase).1 P hP

include M in
/-- **N3+N4 for G10H3** (G10GL's exact delivered form of `flat_base`): at the chart origin `w₀` over `c.point`
(not assumed on the strict transform), flatness of `F` at `x` over `V(J)` base-changes to flatness of the joint base
map over `V(σ^♯ J)`. -/
theorem flat_base_canonical (w₀ : sourceDomain B b F x t c g d E j v)
    (hV₀ : actualMap B b F x t c g d E j v hvj w₀ ∈ targetStrict B b F x t c g d E j)
    (hsrc : (blowupProj (c.embedding.dim+t.rank) {q : c.subdomain × ComplexModel t.rank | q.2 = 0}
      (arbitraryCanonicalRecenteredChart E.source.charts j v hvj w₀).val).1 = c.point.val.1)
    (hbase : F.hom.left.base x = (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base
      ((targetChartMap B b F x t c g d E j).base ⟨actualMap B b F x t c g d E j v hvj w₀, hV₀⟩))
    (J : Ideal (Y.obj.left.presheaf.stalk (F.hom.left.base x)))
    (hJ : ∀ h : F.hom.left.base x = F.hom.left.base x, (quotMap (fibreStalkMap F _ x h) J).Flat) :
    (quotMap ((targetStalkToJoint (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
          (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
          (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j)
          (actualMap_holomorphic B b F x t c g d E M j v hvj) (targetStrict_analytic B b F x t c g d E j) w₀ hV₀).comp
        ((targetChartMap B b F x t c g d E j).stalkMap ⟨actualMap B b F x t c g d E j v hvj w₀, hV₀⟩).hom)
      (Ideal.map (((OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.stalkMap
          ((targetChartMap B b F x t c g d E j).base ⟨actualMap B b F x t c g d E j v hvj w₀, hV₀⟩)).hom.comp
        (eqToHom (congrArg Y.obj.left.presheaf.stalk hbase)).hom) J)).Flat := by
  have hγ := graphPoint_eq E.source.charts E.target.charts c.holomorphic
    (explicitAmbientLift B b F x t c g E.target E.source) E.square.holomorphic E.square.ambient_projection j v hvj w₀
    hV₀ t.analytic.isClosed c.point hsrc
  exact (flattener_of_monomial_lift E.source.charts E.target.charts c.holomorphic
    (explicitAmbientLift B b F x t c g E.target E.source) E.square.holomorphic E.square.ambient_projection M j v hvj
    (fun _ _ => rfl) (fun _ _ => rfl) c.analytic t.analytic t.positive (srcGraph_maps B b F x t c)
    c.chart.hom.left (chartGraphMap t.embedding t.domain t.functions t.holomorphic) F.hom.left
    (source_square B b F x t c) (targetChartMap B b F x t c g d E j)
    (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left
    (target_square B b t E.target j d.target E.target_maps) w₀ hV₀
    c.point hγ x c.point_over hbase).2 J (hJ rfl)

end Canonical





end

end Hironaka.Analytic.Unibranch.HironakaG10GlCanonicalFlattener
