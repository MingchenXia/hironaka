import Hironaka.Analytic.Unibranch.HironakaG10GlCanonicalBaseSquare
import Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotCoordinateRatios

/-!
# N2(d): the canonical base map sends the canonical centre generator to the pivot class

Lane G10HP, run 0081 (continuing lane G10GL, item GL-3b/N2(d)).  Setting of `HironakaG10SbCanonicalStrictTorsion` /
`HironakaG10GlCanonicalBaseSquare`.  At a source chart point `w` of the fibre-product locus
(`actualMap w ∈ targetStrict`):

* `canonicalGenerator` — the prescribed normal section `d.target.sections j` of the pulled centre on `Bl_B Y`, at the
  target chart point `⟨actualMap w, _⟩` (`CompatibleCanonicalIdealBlowupPivotOpenRanges.targetSectionGerm j j`);
* `span_canonicalGenerator` — it generates the pulled centre ideal there (the target chart lies in the pivot
  generator locus, `PivotChartRangeData.target_range`);
* `normal_actualMap` — the target pivot normal coordinate pulls back along `actualMap` to the source pivot
  coordinate (monomial lift laws `chart_square`, `normal_slots`; the recentring has zero pivot coordinate);
* **`canonicalPsi_generator`** — `canonicalPsi … w hV (canonicalGenerator …) = pivotClass … w`
  (`target_original_section_factor`, `targetStalkToJoint_inclusion`).

Consequently the exceptional torsion of the joint quotient (`pivotTorsion`) is the `ψ g`-power torsion of the pulled
torsion presentation (Hironaka 1975, (4.3.1), p. 535; Lemma 4.4.5, p. 537).

No named input.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold

namespace Hironaka.Analytic.Unibranch.HironakaG10GlPresentationPivot

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualWholeStalkHolomorphicPullback
  HironakaActualAnalyticSubspaceOpenRestriction
  HironakaG10ArbitraryBaseRecenter HironakaG10ArbitraryBaseStrict
  HironakaRealOpenGeometricStrictSaturation HironakaG10RealOpenStrictTorsionKernel
  HironakaG10JointStrictTorsion HironakaG10JointNativeIdealMap HironakaG10JointNativeScalar
  Hironaka.Analytic.Unibranch.SourceReducedComplexSpace Hironaka.Analytic.Unibranch.OriginalFiniteIdealGraphChart
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupSquareCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupNormalSections
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotOpenRanges
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialStrictRestriction
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupProductNormalFactors
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotCoordinateRatios
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalRecenteredChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryBaseChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalCoordinateStrict
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalJointSaturation
  Hironaka.Analytic.Unibranch.HironakaG10SbCanonicalStrictTorsion
  Hironaka.Analytic.Unibranch.HironakaG10GlCanonicalBaseSquare

/-! ### Germs of original functions (copies of private helpers of `…ProductNormalFactors`) -/

theorem native_original_function {a b : ℕ} {S T : Type}
    [TopologicalSpace S] [TopologicalSpace T]
    [ChartedSpace (ComplexModel a) S] [IsComplexManifold a S]
    [ChartedSpace (ComplexModel b) T] [IsComplexManifold b T]
    {f : S → T} (hf : ContMDiff 𝓘(ℂ,ComplexModel a) 𝓘(ℂ,ComplexModel b) ∞ f)
    (z : S) (g : T → ℂ) (hg : HolomorphicAt b g (f z)) :
    (ChartedSpace.locallyRingedSpaceMap f hf).stalkMap z
        (actualOriginalFunctionGerm (f z) g hg) =
      actualOriginalFunctionGerm z (g ∘ f)
        (hg.comp_contMDiff (Eventually.of_forall fun _ => hf.contMDiffAt)) := by
  apply (actualStalkChartEquiv (n := a) z).injective
  rw [actualNativeStalk_chart_pullback,actualOriginalFunctionGerm_chart,
    actualHolomorphicGermPullback_original_function,actualOriginalFunctionGerm_chart]

theorem original_germ_congr {n : ℕ} {S : Type}
    [TopologicalSpace S] [ChartedSpace (ComplexModel n) S] [IsComplexManifold n S]
    (z : S) (f g : S → ℂ) (hf : HolomorphicAt n f z) (hg : HolomorphicAt n g z)
    (hfg : f =ᶠ[𝓝 z] g) :
    actualOriginalFunctionGerm z f hf = actualOriginalFunctionGerm z g hg := by
  apply (actualStalkChartEquiv (n := n) z).injective
  rw [actualOriginalFunctionGerm_chart,actualOriginalFunctionGerm_chart]
  exact chartTranslatedGerm_congr_original z f g hf hg hfg

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
  (w : sourceDomain B b F x t c g d E j v)

include M in
/-- The target pivot normal coordinate of the monomial lift is the source pivot normal coordinate (a copy of the
private `monomial_normal_coordinate`). -/
theorem monomial_normal (z : productChartOpen E.source.charts j) :
    productNormalFunction E.target.charts j j (monomialAmbientFunction B b F x t c g d E j z) =
      productNormalFunction E.source.charts j j z := by
  have hs := congrArg (fun k => k.base z) (M.chart_square j)
  have hn := M.normal_slots j j (productChartDiffeomorph E.source.charts j z)
  exact (congrArg (fun w => w.val (j.natAdd t.embedding.dim)) hs).trans hn

include M hvj in
/-- **The target pivot normal coordinate pulls back along the canonical actual map to the source pivot coordinate.** -/
theorem normal_actualMap (p : sourceDomain B b F x t c g d E j v) :
    productNormalFunction E.target.charts j j (actualMap B b F x t c g d E j v hvj p) =
      p.val (j.natAdd c.embedding.dim) := by
  refine (monomial_normal B b F x t c g d E M j
    (arbitraryCanonicalRecenteredChart E.source.charts j v hvj p)).trans ?_
  have h := congrArg (fun u : ComplexModel (c.embedding.dim+t.rank) => u (j.natAdd c.embedding.dim))
    (arbitrary_canonical_recentered_coordinates E.source.charts j v hvj p)
  refine h.trans ?_
  change p.val (j.natAdd c.embedding.dim) + v (j.natAdd c.embedding.dim) = _
  rw [hvj, add_zero]

/-- **The canonical generator of the pulled centre** at the target chart point of `w`: the prescribed normal section
`d.target.sections j`. -/
abbrev canonicalGenerator
    (hV : actualMap B b F x t c g d E j v hvj w ∈ targetStrict B b F x t c g d E j) :=
  targetSectionGerm B b F x t c g d E j j ⟨actualMap B b F x t c g d E j v hvj w, hV⟩

/-- **The canonical generator generates the pulled centre** at the target chart point. -/
theorem span_canonicalGenerator
    (hV : actualMap B b F x t c g d E j v hvj w ∈ targetStrict B b F x t c g d E j) :
    nativePulledIdealStalkIdeal (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left B b
        ((targetChartMap B b F x t c g d E j).base ⟨actualMap B b F x t c g d E j v hvj w, hV⟩) =
      Ideal.span {canonicalGenerator B b F x t c g d E j v hvj w hV} := by
  refine (pivot_chart_ranges_of_models B b F x t c g d E).elim fun P => ?_
  have hmem : (targetChartMap B b F x t c g d E j).base ⟨actualMap B b F x t c g d E j v hvj w, hV⟩ ∈
      (targetPivotOpen B b F x t c g d E j).1 := by
    rw [← P.target_range j]
    exact ⟨_, rfl⟩
  exact hmem.2

/-- **N2(d): the canonical base map sends the canonical generator to the pivot class.** -/
theorem canonicalPsi_generator
    (hV : actualMap B b F x t c g d E j v hvj w ∈ targetStrict B b F x t c g d E j) :
    canonicalPsi B b F x t c g d E M j v hvj w hV (canonicalGenerator B b F x t c g d E j v hvj w hV) =
      pivotClass (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j (fun i => v i)
        (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
        (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j) w := by
  have h0 := target_original_section_factor B b F x t c g d E j j
    ⟨actualMap B b F x t c g d E j v hvj w, hV⟩
  have h1 := h0.trans ((congrArg (fun u => strictNormalClass E.target.charts (targetGraphSet B b t) j j
    ⟨actualMap B b F x t c g d E j v hvj w, hV⟩ * u) (if_pos rfl)).trans (mul_one _))
  have h2 := targetStalkToJoint_inclusion (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j
    (fun i => v i) (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
    (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j)
    (actualMap_holomorphic B b F x t c g d E M j v hvj) (targetStrict_analytic B b F x t c g d E j) w hV
    (actualOriginalFunctionGerm (actualMap B b F x t c g d E j v hvj w)
      (productNormalFunction E.target.charts j j)
      (normal_function_holomorphic E.target.charts j j _))
  have h3 := native_original_function (actualMap_holomorphic B b F x t c g d E M j v hvj) w
    (productNormalFunction E.target.charts j j) (normal_function_holomorphic E.target.charts j j _)
  have h4 : actualOriginalFunctionGerm w
      (productNormalFunction E.target.charts j j ∘ actualMap B b F x t c g d E j v hvj)
      ((normal_function_holomorphic E.target.charts j j _).comp_contMDiff
        (Eventually.of_forall fun _ => (actualMap_holomorphic B b F x t c g d E M j v hvj).contMDiffAt)) =
      exceptionalGerm c.embedding.dim t.rank j (fun i => v i) (targetOpen B b F x t c g d E j v) w :=
    original_germ_congr _ _ _ _ _
      (Eventually.of_forall (normal_actualMap B b F x t c g d E M j v hvj))
  refine (congrArg (targetStalkToJoint (n := t.embedding.dim+t.rank) c.embedding.dim t.rank j
    (fun i => v i) (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)
    (actualMap B b F x t c g d E j v hvj) (targetStrict B b F x t c g d E j)
    (actualMap_holomorphic B b F x t c g d E M j v hvj) (targetStrict_analytic B b F x t c g d E j) w hV)
      h1).trans ?_
  refine h2.trans ?_
  exact congrArg (Ideal.Quotient.mk _) (h3.trans h4)

end

end Hironaka.Analytic.Unibranch.HironakaG10GlPresentationPivot
