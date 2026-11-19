import Hironaka.Analytic.Unibranch.HironakaG10SbCanonicalStrictTorsion
import Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease

/-!
# H3.2: the source-side projection square of the canonical strict-torsion readout

Lane G10H3, run 0081 (item H3.2 of `G10N5/hfib-H3-route.md`; source analogue of
`HironakaG10NfTargetChart.square`).  Setting of `HironakaG10SbCanonicalStrictTorsion`: `F : X ⟶ Y`, a finite-type
ideal `b : B ⟶ 𝒪_Y`, the strict transform `Bl_{F*B} X` with its projection `q` to `X`, canonical chart data
`t c g d E M`, a pivot `j`, a recentring `v` with zero pivot coordinate.  The source graph `Γ_X = {(u, g(F u))}`
(`sourceGraphSet`) is the canonical chart `c.chart : Γ_X ⟶ X`.

* `proj` — the ambient representative `w ↦ π(χ w)` of the blowup map on the recentred source chart;
* `proj_mem` — on the real-open strict transform it lands in `Γ_X`;
* `projMap` — `chartIso ≫ strictChartInclusion ≫ geometricProjection` (point map `proj`, `projMap_base`);
* **`square`** — `projMap ≫ c.chart = chartIso ≫ sourceChartMap j ≫ q` (from `SourceExplicitMapLaws.projection`);
* `q_nativePoint` — on points: `q (nativePoint w) = c.chart ⟨proj w, _⟩`;
* `chart_q_point` — the same, stated literally on the composite chart point (for stalk computations).

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff Hironaka.ProductComplexManifold

namespace Hironaka.Analytic.Unibranch.HironakaG10NfSourceSquare

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaSmoothCentreRealDomainActualSheafStalk BlowupConstruction BlowupStrictSubmanifold
  HironakaG10ArbitraryBaseRecenter HironakaG10ArbitraryBaseStrict
  HironakaRealOpenGeometricStrictSaturation
  Hironaka.Analytic.Unibranch.SourceReducedComplexSpace Hironaka.Analytic.Unibranch.OriginalFiniteIdealGraphChart
  Hironaka.Analytic.Unibranch.EmbeddedGeometricBlowup
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupSquareCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupNormalSections
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupExplicitProductCharts
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupMonomialLift
  Hironaka.Analytic.Unibranch.CompatibleCanonicalIdealBlowupPivotOpenRanges
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalRecenteredChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryBaseChart
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalCoordinateStrict
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalArbitraryStrictConjugacy
  Hironaka.Analytic.Unibranch.HironakaG10CanonicalJointSaturation
  Hironaka.Analytic.Unibranch.HironakaG10SbCanonicalStrictTorsion

/-- A commutative square of locally ringed spaces, on stalks at one point. -/
theorem square_apply_generic {T S A C D : LocallyRingedSpace.{0}}
    (i₁ : T ⟶ A) (i₂ : A ⟶ C) (ind : C ⟶ S) (m : T ⟶ D) (tc : D ⟶ S)
    (H : i₁ ≫ (i₂ ≫ ind) = m ≫ tc) (t : T)
    (hs : tc.base (m.base t) = ind.base (i₂.base (i₁.base t)))
    (r : S.presheaf.stalk (ind.base (i₂.base (i₁.base t)))) :
    (i₁.stalkMap t).hom ((i₂.stalkMap (i₁.base t)).hom ((ind.stalkMap (i₂.base (i₁.base t))).hom r)) =
      (m.stalkMap t).hom ((tc.stalkMap (m.base t)).hom
        ((eqToHom (congrArg S.presheaf.stalk hs.symm)).hom r)) := by
  have e := Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease.stalkMap_eq_of_eq _ _ H t hs r
  have c1 := ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp i₁ (i₂ ≫ ind) t) r
  have c2 := ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp i₂ ind (i₁.base t)) r
  have c3 := ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp m tc t)
    ((eqToHom (congrArg S.presheaf.stalk hs.symm)).hom r)
  exact (congrArg (i₁.stalkMap t).hom c2).symm.trans (c1.symm.trans (e.trans c3))

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
  (j : Fin t.rank) (v : ComplexModel (c.embedding.dim+t.rank))
  (hvj : v (j.natAdd c.embedding.dim) = 0)

/-- The source graph `Γ_X = {(u, g(F u))}` of the canonical source data. -/
abbrev graph : Set (c.subdomain × ComplexModel t.rank) := sourceGraphSet B b F x t c

/-- The real-open strict transform of the recentred source chart. -/
abbrev strict : Set (sourceDomain B b F x t c g d E j v) :=
  realOpenStrictTransform c.embedding.dim t.rank j (fun i => v i)
    (targetOpen B b F x t c g d E j v) (originalGraph B b F x t c g d E j v)

/-- The ambient representative `w ↦ π(χ w)` of the blowup map on the recentred source chart. -/
def proj : sourceDomain B b F x t c g d E j v → c.subdomain × ComplexModel t.rank :=
  blowupProj (c.embedding.dim+t.rank) {q : c.subdomain × ComplexModel t.rank | q.2=0} ∘
    (Subtype.val ∘ arbitraryCanonicalRecenteredChart E.source.charts j v hvj)

theorem proj_contMDiff :
    ContMDiff 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank)) 𝓘(ℂ,ComplexModel (c.embedding.dim+t.rank)) ∞
      (proj B b F x t c g d E j v hvj) :=
  contMDiff_blowupProj.comp
    (contMDiff_subtype_val.comp (arbitraryCanonicalRecenteredChart E.source.charts j v hvj).contMDiff)

theorem proj_mem (w : sourceDomain B b F x t c g d E j v) (hw : w ∈ strict B b F x t c g d E j v) :
    proj B b F x t c g d E j v hvj w ∈ graph B b F x t c := by
  have h1 := (mem_strict_iff_chart B b F x t c g d E j v hvj w).mp hw
  exact geoStrictTransform_subset_preimage contMDiff_blowupProj.continuous c.analytic.isClosed h1

/-- The ambient representative as a morphism of actual models (the composite of the chart isomorphism, the strict
chart inclusion and the geometric blowup projection; its point map is `proj`). -/
abbrev projMap :
    actualSubspaceLocallyRingedSpace (n := c.embedding.dim+t.rank) (strict B b F x t c g d E j v) ⟶
      actualSubspaceLocallyRingedSpace (n := c.embedding.dim+t.rank) (graph B b F x t c) :=
  (chartIso B b F x t c g d E j v hvj).hom ≫
    strictChartInclusion E.source.charts (graph B b F x t c) j ≫
      geometricProjection (explicitProductPredicate (n := c.embedding.dim) (P := c.subdomain) t.positive)
        c.analytic.isClosed

theorem projMap_base (w : sourceDomain B b F x t c g d E j v) (hwS : w ∈ strict B b F x t c g d E j v) :
    (projMap B b F x t c g d E j v hvj).base ⟨w, hwS⟩ =
      ⟨proj B b F x t c g d E j v hvj w, proj_mem B b F x t c g d E j v hvj w hwS⟩ :=
  rfl

theorem sourceChartMap_eq :
    sourceChartMap B b F x t c g d E j =
      strictChartInclusion E.source.charts (graph B b F x t c) j ≫
        (sourceCanonicalMap B b F x t c g E.source).hom.left :=
  rfl

/-- **H3.2: the source projection square** of the recentred strict chart over the canonical chart of `X`. -/
theorem square :
    projMap B b F x t c g d E j v hvj ≫ c.chart.hom.left =
      (chartIso B b F x t c g d E j v hvj).hom ≫ (sourceChartMap B b F x t c g d E j ≫
        (OriginalFiniteIdealGeometricBlowup.projectionMorphism (nativePulledIdealModule F.hom.left B b)
          (nativePulledIdealInclusion F.hom.left B b)).hom.left) := by
  have hproj : (sourceCanonicalMap B b F x t c g E.source).hom.left ≫
      (OriginalFiniteIdealGeometricBlowup.projectionMorphism (nativePulledIdealModule F.hom.left B b)
        (nativePulledIdealInclusion F.hom.left B b)).hom.left =
      geometricProjection (explicitProductPredicate (n := c.embedding.dim) (P := c.subdomain) t.positive)
          c.analytic.isClosed ≫ c.chart.hom.left :=
    congrArg (fun φ => φ.hom.left) E.source_maps.projection
  exact (Category.assoc (chartIso B b F x t c g d E j v hvj).hom
      (strictChartInclusion E.source.charts (graph B b F x t c) j ≫
        geometricProjection (explicitProductPredicate (n := c.embedding.dim) (P := c.subdomain) t.positive)
          c.analytic.isClosed) c.chart.hom.left).trans
    (congrArg (fun k => (chartIso B b F x t c g d E j v hvj).hom ≫ k)
      ((Category.assoc (strictChartInclusion E.source.charts (graph B b F x t c) j)
        (geometricProjection (explicitProductPredicate (n := c.embedding.dim) (P := c.subdomain) t.positive)
          c.analytic.isClosed) c.chart.hom.left).trans
      ((congrArg (fun k => strictChartInclusion E.source.charts (graph B b F x t c) j ≫ k) hproj.symm).trans
        (Category.assoc (strictChartInclusion E.source.charts (graph B b F x t c) j)
          (sourceCanonicalMap B b F x t c g E.source).hom.left
          (OriginalFiniteIdealGeometricBlowup.projectionMorphism (nativePulledIdealModule F.hom.left B b)
            (nativePulledIdealInclusion F.hom.left B b)).hom.left).symm)))

/-- **On points**: the strict-transform projection `q` sends the native chart point to the canonical chart point
of its blowup base. -/
theorem q_nativePoint (w : sourceDomain B b F x t c g d E j v) (hwS : w ∈ strict B b F x t c g d E j v) :
    (OriginalFiniteIdealGeometricBlowup.projectionMorphism (nativePulledIdealModule F.hom.left B b)
        (nativePulledIdealInclusion F.hom.left B b)).hom.left.base (nativePoint B b F x t c g d E j v hvj w hwS) =
      c.chart.hom.left.base ⟨proj B b F x t c g d E j v hvj w, proj_mem B b F x t c g d E j v hvj w hwS⟩ :=
  (congrArg (fun k => k.base ⟨w, hwS⟩) (square B b F x t c g d E j v hvj)).symm

/-- The two images of the chart point in `X` agree (the point form of `square`, stated literally on the composite
chart point). -/
theorem chart_q_point (w : sourceDomain B b F x t c g d E j v) (hwS : w ∈ strict B b F x t c g d E j v) :
    c.chart.hom.left.base ((projMap B b F x t c g d E j v hvj).base ⟨w, hwS⟩) =
      (OriginalFiniteIdealGeometricBlowup.projectionMorphism (nativePulledIdealModule F.hom.left B b)
        (nativePulledIdealInclusion F.hom.left B b)).hom.left.base
          ((sourceChartMap B b F x t c g d E j).base ((chartIso B b F x t c g d E j v hvj).hom.base ⟨w, hwS⟩)) :=
  congrArg (fun k => k.base ⟨w, hwS⟩) (square B b F x t c g d E j v hvj)

end

end Hironaka.Analytic.Unibranch.HironakaG10NfSourceSquare
