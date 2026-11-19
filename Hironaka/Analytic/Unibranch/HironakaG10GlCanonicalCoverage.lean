import Hironaka.Analytic.Unibranch.HironakaG10SbCanonicalStrictTorsion
import Hironaka.Analytic.Unibranch.HironakaG10CanonicalExceptionalOrigin

/-!
# N1: every point of the strict transform over the centre is a canonical chart point

Lane G10GL, run 0081, item GL-3b / N1 (`work/hironaka-run0081-20261117/G10GL/GL-3b-4-route.md`).  Setting of
`HironakaG10SbCanonicalStrictTorsion`: `F : X ⟶ Y`, a finite-type ideal `b : B ⟶ 𝒪_Y`, the native geometric
blowup `Bl_B Y` and the strict transform `Bl_{F*B} X`, canonical chart data `t c g d E` at a source point `x` and a
target point `y` (`CompatibleCanonicalIdealBlowupMonomialLift.exists_same_canonical_allambient_monomial_lift`).

* `mem_sourceModelOpen` — every point of `Bl_{F*B} X` over `x` lies in the source canonical model open;
* `exists_sourceChartMap_eq` — it is the image of a point of some pivot strict chart;
* `strictCentreStalkIdeal_ne_top` — over the centre (pulled ideal proper), the strict centre ideal of the chart point
  is proper;
* `pivot_coordinate_eq_zero` — and its pivot coordinate vanishes (the pivot coordinate class generates the strict
  centre ideal on its chart and evaluates to the pivot coordinate);
* `exists_nativePoint_eq` — **N1**: such a point is `nativePoint … w hwS` for a pivot `j`, a recentring `v` with zero
  pivot coordinate and the recentred origin `w` (in the local saturation domain, on the strict transform), so
  `HironakaG10SbCanonicalStrictTorsion.nativeStrictStalkTorsionEquiv` applies at it.

No named input.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold

namespace Hironaka.Analytic.Unibranch.HironakaG10GlCanonicalCoverage

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspaceResidue
  HironakaActualAnalyticSubspaceLocalFunctions
  HironakaG10ArbitraryBaseRecenter HironakaG10ArbitraryBaseStrict
  HironakaRealOpenGeometricStrictSaturation HironakaG10RealOpenStrictTorsionKernel
  HironakaG10JointStrictTorsion HironakaG10JointNativeIdealMap
  BlowupConstruction BlowupConstruction.FlatChart BlowupFlatCoordinates BlowupStrictSubmanifold
  Hironaka.BlowupSequences
  Hironaka.Analytic.Unibranch.SourceReducedComplexSpace Hironaka.Analytic.Unibranch.OriginalFiniteIdealGraphChart
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupSquareCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupNormalSections
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotOpenRanges
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalRecenteredChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryBaseChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalCoordinateStrict
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryStrictConjugacy
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalJointSaturation
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalExceptionalOrigin Hironaka.Analytic.Unibranch.HironakaG10CanonicalRealStrictLanding
  Hironaka.Analytic.Unibranch.HironakaG10SbCanonicalStrictTorsion

/-! ### Units of an actual subspace stalk and values of original germs -/

section Residue

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A germ of an actual subspace stalk is a unit iff its value is nonzero (same proof as the private
`CompatibleCanonicalIdealBlowupPivotChart.actual_stalk_unit_iff_residue`). -/
theorem stalk_isUnit_iff_eval (C : Set M) (x : C)
    (r : ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier) :
    IsUnit r ↔ actualSubspaceStalkEval (n := n) C x r ≠ 0 := by
  let : IsLocalRing ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier :=
    actualSubspaceStalk_isLocalRing C x
  rw [← IsLocalRing.notMem_maximalIdeal, ← actualSubspaceStalkEval_ker C x]
  rfl

/-- The value of the restriction of an original holomorphic germ (same proof as the private
`CompatibleCanonicalIdealBlowupPivotChart.quotient_germ_eval`). -/
theorem eval_inclusion_germ (S : Set M) (x : S) (f : M → ℂ) (hf : HolomorphicAt n f x.val) :
    actualSubspaceStalkEval (n := n) S x
      (((actualSubspaceInclusion (n := n) S).stalkMap x)
        (actualOriginalFunctionGerm x.val f hf)) = f x.val := by
  obtain ⟨U, hxU, s, hs⟩ := exists_actual_section_of_original_holomorphicAt x.val f hf
  rw [actualOriginalFunctionGerm_eq_section U x.val hxU s f hf hs,
    actualSubspaceStalkEval_inclusion_germ]
  exact (sectionExtension_apply U s x.val hxU).symm.trans hs.self_of_nhds

/-- A local map of local rings sends proper ideals to proper ideals. -/
theorem map_ne_top_of_ne_top {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (φ : R →+* S) [IsLocalHom φ] {I : Ideal R} (h : I ≠ ⊤) : Ideal.map φ I ≠ ⊤ := by
  intro htop
  have h1 : Ideal.map φ I ≤ IsLocalRing.maximalIdeal S :=
    Ideal.map_le_iff_le_comap.mpr fun a ha => map_nonunit φ a (IsLocalRing.le_maximalIdeal h ha)
  rw [htop] at h1
  exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top (top_le_iff.mp h1)

end Residue

/-! ### The pivot coordinate of a chart point over the centre -/

section Pivot

variable {n r : ℕ} {P : Type} [TopologicalSpace P] [ChartedSpace (ComplexModel n) P]
  [IsComplexManifold n P]

/-- **A chart point whose strict centre ideal is proper has zero pivot coordinate**: on its pivot chart the strict
centre ideal is generated by the pivot coordinate class, which is then a nonunit, i.e. its value — the pivot
coordinate — vanishes. -/
theorem pivot_coordinate_eq_zero_of_ne_top (a : ProductNormalCharts n r P) (hr : 0 < r)
    (W : Set (P × ComplexModel r)) (hW : IsClosed W) (j : Fin r) (p : strictChartCarrier a W j)
    (hne : strictCentreStalkIdeal W ((strictChartInclusion a W j).base p) ≠ ⊤) :
    productChartCoordinates a j p.val (j.natAdd n) = 0 := by
  let cc := productNormalChart (n := n) a.base j
  let z : actualStrictCarrier (n := n) W := (strictChartInclusion a W j).base p
  have he := Set.ext_iff.mp (strict_pivot_generator_locus
    (HironakaProductZeroPlaneBlowup.interior_product_zero_plane_eq_empty hr)
    W hW cc (j.natAdd n) (by simp [cc, productNormalChart])) z
  change (∃ hz : z.val.base ∈ cc.dom,
    strictCentreStalkIdeal W z = Ideal.span {geometricCoordinateClass W cc z hz (j.natAdd n)}) ↔
      z.val ∈ cc.source at he
  have hzs : z.val ∈ cc.source := p.val.property
  obtain ⟨hz, hgen⟩ := he.mpr hzs
  have hnu : ¬ IsUnit (geometricCoordinateClass W cc z hz (j.natAdd n)) := fun hu =>
    hne (hgen.trans (Ideal.span_singleton_eq_top.mpr hu))
  rw [stalk_isUnit_iff_eval, not_not] at hnu
  have hval := eval_inclusion_germ (actualStrictCarrier (n := n) W) z (cc.τ (j.natAdd n) ∘ blowupProj (n+r) _)
    ((holomorphicAt_flatCoord cc.Φ (j.natAdd n) hz).comp_contMDiff
      (Filter.Eventually.of_forall fun q => contMDiff_blowupProj q))
  change actualSubspaceStalkEval (n := n+r) (actualStrictCarrier (n := n) W) z
    (geometricCoordinateClass W cc z hz (j.natAdd n)) = cc.τ (j.natAdd n) (blowupProj (n+r) _ z.val) at hval
  rw [hnu] at hval
  have hj : cc.j = j.natAdd n := rfl
  change cc.toFun z.val (j.natAdd n) = 0
  rw [← hj, toFun_apply_j]
  exact hval.symm

end Pivot

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

/-- Every point of the strict transform over `x` lies in the source canonical model open. -/
theorem mem_sourceModelOpen
    (y'' : (OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
      (nativePulledIdealInclusion F.hom.left B b)).obj.left)
    (hy : (OriginalFiniteIdealGeometricBlowup.projectionMorphism (nativePulledIdealModule F.hom.left B b)
      (nativePulledIdealInclusion F.hom.left B b)).hom.left.base y'' = x) :
    y'' ∈ (sourceModelOpen B b F x t c g d E).1 := by
  have h : y'' ∈ range (sourceCanonicalMap B b F x t c g E.source).hom.left.base := by
    rw [E.source_maps.range_eq, g.comparison_range]
    exact ⟨c.point, c.point_over.trans hy.symm⟩
  delta sourceModelOpen
  exact h

/-- Every point of the strict transform over `x` is the image of a point of a pivot strict chart. -/
theorem exists_mem_range_sourceChartMap
    (y'' : (OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
      (nativePulledIdealInclusion F.hom.left B b)).obj.left)
    (hy : (OriginalFiniteIdealGeometricBlowup.projectionMorphism (nativePulledIdealModule F.hom.left B b)
      (nativePulledIdealInclusion F.hom.left B b)).hom.left.base y'' = x) :
    ∃ j : Fin t.rank, y'' ∈ range (sourceChartMap B b F x t c g d E j).base := by
  have hP := pivot_open_ranges_of_models B b F x t c g d E
  obtain ⟨P⟩ := hP
  have h1 := mem_sourceModelOpen B b F x t c g d E y'' hy
  rw [← P.source_cover] at h1
  exact (Set.mem_iUnion.mp h1).imp fun j hj =>
    Eq.mpr (congrArg (fun A => y'' ∈ A) (P.chart_ranges.source_range j)) hj


/-- **N1: every point of the strict transform over `x` and over the centre is a canonical chart point**
(`HironakaG10SbCanonicalStrictTorsion.nativePoint`), for a pivot `j`, a recentring `v` with zero pivot coordinate,
and a point `w` of the recentred chart in its local saturation domain and on the strict transform. -/
theorem exists_nativePoint_eq
    (y'' : (OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
      (nativePulledIdealInclusion F.hom.left B b)).obj.left)
    (hy : (OriginalFiniteIdealGeometricBlowup.projectionMorphism (nativePulledIdealModule F.hom.left B b)
      (nativePulledIdealInclusion F.hom.left B b)).hom.left.base y'' = x)
    (hcent : nativePulledIdealStalkIdeal (OriginalFiniteIdealGeometricBlowup.projectionMorphism
        (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left
        (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b) y'' ≠ ⊤) :
    ∃ (j : Fin t.rank) (v : ComplexModel (c.embedding.dim+t.rank))
      (hvj : v (j.natAdd c.embedding.dim) = 0)
      (h0 : (0 : ComplexModel (c.embedding.dim+t.rank)) ∈ targetOpen B b F x t c g d E j v)
      (w : sourceDomain B b F x t c g d E j v)
      (hwS : w ∈ realOpenStrictTransform c.embedding.dim t.rank j (fun i => v i)
        (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)),
      w ∈ localDomain c.embedding.dim t.rank j (fun i => v i)
          (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v) h0
            (originalGraph_analytic B b F x t c g d E j v) ∧
        nativePoint B b F x t c g d E j v hvj w hwS = y'' := by
  refine (exists_mem_range_sourceChartMap B b F x t c g d E y'' hy).elim fun j hj => ?_
  refine (Set.mem_range.mp hj).elim fun p hp => ?_
  subst hp
  have hwh := E.source_normals.whole_ideal
    ((strictChartInclusion E.source.charts (sourceGraphSet B b F x t c) j).base p)
  have hne : strictCentreStalkIdeal (sourceGraphSet B b F x t c)
      ((strictChartInclusion E.source.charts (sourceGraphSet B b F x t c) j).base p) ≠ ⊤ := fun htop =>
    @map_ne_top_of_ne_top _ _ _ _ (LocallyRingedSpace.isLocalRing _ _)
      ((explicitSource B b F x t c).obj.left.isLocalRing _) _
      (LocallyRingedSpace.isLocalHomStalkMap (sourceCanonicalMap B b F x t c g E.source).hom.left _) _ hcent
      (hwh.trans htop)
  have hvj := pivot_coordinate_eq_zero_of_ne_top E.source.charts t.positive (sourceGraphSet B b F x t c)
    c.analytic.isClosed j p hne
  refine (actual_exceptional_point_in_saturation_domain B b F x t c g d E j p.val hvj).elim
    fun w hw => ?_
  have hwS : w ∈ realOpenStrictTransform c.embedding.dim t.rank j
      (fun i => productChartCoordinates E.source.charts j p.val i)
      (targetOpen B b F x t c g d E j (productChartCoordinates E.source.charts j p.val))
      (originalGraph B b F x t c g d E j (productChartCoordinates E.source.charts j p.val)) := by
    refine (mem_strict_iff_chart B b F x t c g d E j _ hvj w).mpr ?_
    rw [hw.1]
    exact p.property
  refine ⟨j, _, hvj, canonical_target_origin B b F x t c g d E j p.val, w, hwS, hw.2, ?_⟩
  have hpt : (chartIso B b F x t c g d E j _ hvj).hom.base ⟨w, hwS⟩ = p := Subtype.ext hw.1
  exact congrArg (sourceChartMap B b F x t c g d E j).base hpt

end

end Hironaka.Analytic.Unibranch.HironakaG10GlCanonicalCoverage
